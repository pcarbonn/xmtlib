// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;
use std::cmp::max;

use crate::api::{QualIdentifier, SpecConstant, Symbol};
use crate::private::e1_ground_view::{View, Ids};
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
pub(crate) enum SQLVariant {
    Normal,
    Mapping,
    Theta(Option<View>)
}

///////////////////////////  Display //////////////////////////////////////////


impl SQLExpr {
    // it can return an empty string !
    pub(crate) fn to_sql(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>,
        variant: &SQLVariant
    ) -> String {

        match self {
            SQLExpr::Boolean(value) => format!("\"{value}\""),
            SQLExpr::Constant(spec_constant) => {
                match spec_constant {
                    SpecConstant::Numeral(s) => format!("\"{s}\""),
                    SpecConstant::Decimal(s) => format!("\"{s}\""),
                    SpecConstant::Hexadecimal(s) => format!("\"{s}\""),
                    SpecConstant::Binary(s) => format!("\"{s}\""),
                    SpecConstant::String(s) => format!("\"{s}\""),
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
                sql_for("apply", qual_identifier.to_string(), exprs, variables, variant)
            },
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier.to_string(), exprs, variables, variant)
            },
            SQLExpr::Predefined(function, exprs) => {
                if UNARY.contains(function) {
                    // NOT
                    match variant {
                        SQLVariant::Theta(_) => {
                            let expr = exprs.first().unwrap().1.to_sql(variables, variant);
                            if expr == "TRUE" {
                                "FALSE".to_string()
                            } else if expr == "FALSE" {
                                "TRUE".to_string()
                            } else {
                                format!("NOT({expr})")
                            }
                        }
                        _ => {
                            let expr = exprs.first().unwrap().1.to_sql(variables, variant);
                            format!("not_({expr})")
                        }
                    }
                } else if ASSOCIATIVE.contains(function) {
                    // AND, OR
                    let name = function.to_string().to_lowercase();
                    let exprs =
                        exprs.iter().cloned().filter_map( |(_, e)| {  // try to simplify
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
                        format!("{name}_({})", exprs.join(", "))
                    }
                } else if CHAINABLE.contains(function) {
                    // Eq
                    match (function, variant) {
                        // LINK src/doc.md#_Equality
                        (Predefined::Eq, SQLVariant::Normal) => {
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
                        },
                        (Predefined::Eq, SQLVariant::Mapping) => {
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
                        (Predefined::Eq, SQLVariant::Theta(None)) => {
                            let res = exprs.iter().zip(exprs.iter().skip(1))
                                .filter_map(|((_, a), (_, b))| {
                                    // a op b
                                    let a = a.to_sql(variables, &SQLVariant::Theta(None));
                                    let b = b.to_sql(variables, &SQLVariant::Theta(None));
                                    let comp = format!("{a} {function} {b}");
                                    if a == b {
                                        None
                                    } else {
                                        Some(comp)
                                    }
                                }).collect::<Vec<_>>().join(" AND ");
                                if res.len() == 0 {
                                    "TRUE".to_string()
                                } else {
                                    format!("({res})")
                                }
                        }
                        (Predefined::Eq, SQLVariant::Theta(Some(View::G))) => {
                            "".to_string()
                        }
                        (Predefined::Eq, SQLVariant::Theta(Some(view))) => {
                            let res = exprs.iter().zip(exprs.iter().skip(1))
                                .filter_map(|((a_id, a), (b_id, b))| {
                                    // NOT is_id(a) OR NOT is_id(b) OR a op b
                                    let a = a.to_sql(variables, &SQLVariant::Theta(None));
                                    let b = b.to_sql(variables, &SQLVariant::Theta(None));
                                    let comp = match view {
                                        View::UF => format!("NOT ({a} {function} {b})"),
                                        View::TU => format!("{a} {function} {b}"),
                                        View::G => unreachable!()
                                    };
                                    if a == b {
                                        None
                                    } else {
                                        match (a_id, b_id) {
                                            (Ids::All, Ids::All) =>
                                                Some(comp),
                                            (Ids::Some, Ids::All) =>
                                                Some(format!("(NOT is_id({a}) OR {comp})")),
                                            (Ids::All, Ids::Some) =>
                                                Some(format!("(NOT is_id({b}) OR {comp})")),
                                            (Ids::Some, Ids::Some) =>
                                                Some(format!("(NOT is_id({a}) OR NOT is_id({b}) OR {comp})")),
                                            _ => None,
                                        }
                                    }
                                }).collect::<Vec<_>>().join( if *view == View::UF { " OR " } else { " AND " });
                            if res.len() == 0 && *view == View::UF {
                                "FALSE".to_string()
                            } else if res.len() == 0 {
                                "TRUE".to_string()
                            } else {
                                res
                            }
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
    variant: &SQLVariant
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