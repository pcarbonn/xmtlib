// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;
use std::cmp::max;

use crate::api::{QualIdentifier, SpecConstant, Symbol};
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::Column;


////////////////////// Data structures for grounding queries //////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Value(Column),  // in an interpretation table.
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    Predefined(Predefined, Box<Vec<(Ids, SQLExpr)>>),
}

#[derive(Debug, strum_macros::Display, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Predefined {
    #[strum(to_string = "AND")]
    And,
    #[strum(to_string = "OR")]
    Or,
    #[strum(to_string = "NOT")]
    Not,
    #[strum(to_string = "???")]
    Implies,  // binary connective used internally.  "=>" is replaced by a disjunction in `annotate_term`.
    #[strum(to_string = "=")]
    Eq,
}


const UNARY: [Predefined; 1] = [Predefined::Not];
const ASSOCIATIVE: [Predefined; 2] = [Predefined::And, Predefined::Or];
const CHAINABLE: [Predefined; 1] = [Predefined::Eq];


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SQLPosition {
    // SQL expression that evaluates to an SMT-Lib value, for the full expression syntax
    Field,              // in a grounding field
    // SQL expression that evaluats to an SQL boolean, for mapping expressions only
    Join,               // in a join condition
}


///////////////////////////  Display //////////////////////////////////////////


impl SQLExpr {
    // it can return an empty string !
    pub(crate) fn to_sql(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>,
        variant: &SQLPosition
    ) -> String {

        match self {
            SQLExpr::Boolean(value) => format!("\"{value}\""),

            SQLExpr::Constant(spec_constant) => {
                match (variant, spec_constant) {
                    (SQLPosition::Join, _) => unreachable!(),
                    (_, SpecConstant::Numeral(s)) => format!("\"{s}\""),
                    (_, SpecConstant::Decimal(s)) => format!("\"{s}\""),
                    (_, SpecConstant::Hexadecimal(s)) => format!("\"{s}\""),
                    (_, SpecConstant::Binary(s)) => format!("\"{s}\""),
                    (_, SpecConstant::String(s)) => format!("\"{s}\""),
                }
            },
            SQLExpr::Variable(symbol) => {
                let column = variables.get(symbol).unwrap();
                if let Some(column) = column {
                    column.to_string()
                } else {
                    format!("\"{symbol}\"")
                }
            },
            SQLExpr::Value(column) => column.to_string(),

            SQLExpr::Apply(qual_identifier, exprs) => {
                let sub_variant = SQLPosition::Field;
                sql_for("apply", qual_identifier.to_string(), exprs, variables, &sub_variant)
            },
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier.to_string(), exprs, variables, variant)
            },
            SQLExpr::Predefined(function, exprs) => {
                if UNARY.contains(function) {
                    // NOT
                    let (id, e) = exprs.first().unwrap();
                    let expr = e.to_sql(variables, variant);
                    if *id == Ids::None {
                        format!("apply(\"not\", {expr})")
                    } else {
                        format!("not_({expr})")
                    }
                } else if ASSOCIATIVE.contains(function) {
                    // AND, OR
                    match variant {
                        SQLPosition::Field => {
                            let name = function.to_string().to_lowercase();
                            let mut ids = Ids::All;
                            let exprs =
                                exprs.iter().cloned().filter_map( |(id, e)| {
                                    ids = max(ids.clone(), id.clone());
                                    // try to simplify
                                    match e {
                                        SQLExpr::Boolean(b) => {
                                            if name == "and" && b { None }
                                            else if name == "or" && !b { None }
                                            else { Some(e.to_sql(variables, variant)) }
                                        },
                                        _ => Some(e.to_sql(variables, variant))
                                    }
                                }).collect::<Vec<_>>();
                            if exprs.len() == 0 {
                                if name == "and" { "\"true\"".to_string() } else { "\"false\"".to_string()}
                            } else if exprs.len() == 1 {
                                exprs.first().unwrap().to_string()
                            } else {
                                if ids == Ids::None {
                                    format!("apply(\"{name}\", {})", exprs.join(", "))
                                } else {
                                    format!("{name}_({})", exprs.join(", "))
                                }
                            }
                        }
                        SQLPosition::Join => unreachable!(),
                    }
                } else if CHAINABLE.contains(function) {
                    // Eq
                    match (function, variant) {
                        // LINK src/doc.md#_Equality
                        (Predefined::Eq, SQLPosition::Field) => {
                            let equal = exprs.iter().zip(exprs.iter().skip(1))
                                    .all(|((_, a), (_, b))| *a == *b);
                            if equal {
                                "\"true\"".to_string()
                            } else {
                                let mut ids = Ids::All;
                                let terms = exprs.iter()
                                    .map(|(ids_, e)| {
                                        ids = max(ids.clone(), ids_.clone());
                                        e.to_sql(variables, variant)
                                    }).collect::<Vec<_>>().join(", ");
                                if ids == Ids::None {
                                    format!("apply(\"=\",{terms})")
                                } else {
                                    format!("eq_({terms})")
                                }
                            }
                        },
                        (Predefined::Eq, SQLPosition::Join) => {
                            exprs.iter().zip(exprs.iter().skip(1))
                                .filter_map(|((ids_a, a_), (_, b_))| {
                                    // a op b
                                    let a = a_.to_sql(variables, variant);
                                    let b = b_.to_sql(variables, variant);
                                    if a == b {
                                        None
                                    } else {
                                        match ids_a {
                                            Ids::All =>
                                                 Some(format!("{a} = {b}")),
                                            Ids::Some =>
                                                 Some(format!("(NOT is_id({a}) OR {a} = {b})")),
                                            Ids::None =>
                                                if let SQLExpr::Variable(_) = *a_ {  // an infinite variable mapped to an interpretation
                                                    // Variable + Ids::None describe an infinite variable
                                                    Some(format!("{a} = {b}"))
                                                } else {
                                                    None
                                                },
                                        }
                                    }
                                }).collect::<Vec<_>>().join(" AND ")
                        }
                        _ => unreachable!()
                    }
                } else {
                    // Implies
                    assert_eq!(exprs.len(), 2);  // implies is a binary connective used internally
                    let e1 = exprs.first().unwrap().1.to_sql(variables, variant);
                    let e2 = exprs.get(2).unwrap().1.to_sql(variables, variant);
                    if e1 == "true" {
                        e2
                    } else if e1 == "false" {
                        "true".to_string()
                    } else if e2 == "true" {
                        "true".to_string()
                    } else if e2 == "false" {
                        format!("not_({e1})")
                    } else {
                        format!("implies_({e1}, {e2})")
                    }
                }
            }
        }
    }
}



/// Use either "apply" or "construct2", according to the first argument.
/// See description of these functions in y_db module.
///
/// Arguments:
/// * application: either "apply" or "construct2"
fn sql_for(
    application: &str,
    function: String,
    exprs: &Box<Vec<SQLExpr>>,
    variables: &IndexMap<Symbol, Option<Column>>,
    variant: &SQLPosition
) -> String {
    if exprs.len() == 0 {
        format!("\"{function}\"")
    } else {
        let terms = exprs.iter()
            .map(|e| e.to_sql(variables, variant))
            .collect::<Vec<_>>().join(", ");
        format!("{application}(\"{function}\", {terms})")
    }
}