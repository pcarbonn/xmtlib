// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;
use std::cmp::max;

use crate::api::{QualIdentifier, SpecConstant, Symbol};
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::Column;


////////////////////// Data structures for grounding queries //////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Mapping (pub Ids, pub SQLExpr, pub Column);


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
    #[strum(to_string = "???")]  // `Implies` is a binary connective used internally.  Use `implies_` instead of string.
    Implies,
    #[strum(to_string = "=")]
    Eq,
    #[strum(to_string = "<")]
    Less,
    #[strum(to_string = "<=")]
    LE,
    #[strum(to_string = ">=")]
    GE,
    #[strum(to_string = ">")]
    Greater,
    #[strum(to_string = "distinct")]
    Distinct,
}


const UNARY: [Predefined; 1] = [Predefined::Not];
const ASSOCIATIVE: [Predefined; 2] = [Predefined::And, Predefined::Or];
const CHAINABLE: [Predefined; 5] = [
    Predefined::Eq,
    Predefined::Less,
    Predefined::LE,
    Predefined::GE,
    Predefined::Greater
    ];
const PAIRWISE: [Predefined; 1] = [ Predefined::Distinct ];


///////////////////////////  Display //////////////////////////////////////////


impl Mapping {

    pub(crate) fn to_if(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>
    ) -> Option<String> {
        let exp = self.1.to_sql(variables);
        let col = self.2.to_string();
        if exp == col {
            None
        } else {
            match self.0 {
                Ids::All => None,
                Ids::Some => Some(format!("if_({}, {})", exp, col)),  // is_id(exp) or exp = col
                Ids::None => Some(format!("apply(\"=\",{}, {})", exp, col))
            }
        }
    }

    pub(crate) fn to_join(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>
    ) -> Option<String> {
        let exp = self.1.to_sql(variables);
        let col = self.2.to_string();
        if exp == col {
            None
        } else {
            match self.0 {
                Ids::All => Some(format!("{} = {}", exp, col)),
                Ids::Some => Some(format!("join_({}, {})", exp, col)),  // NOT is_id(exp) or exp = col
                Ids::None => {
                    if let SQLExpr::Variable(_) = self.1 {  // an infinite variable mapped to an interpretation
                        // Variable + Ids::None describe an infinite variable
                        Some(format!("{exp} = {col}"))
                    } else {
                        None
                    }
                }
            }
        }
    }
}


impl SQLExpr {
    // it can return an empty string !
    pub(crate) fn to_sql(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>
    ) -> String {

        match self {
            SQLExpr::Boolean(value) => format!("\"{value}\""),

            SQLExpr::Constant(spec_constant) => {
                match spec_constant {
                    SpecConstant::Numeral(s) => format!("{s}"),
                    SpecConstant::Decimal(s) => format!("{s}"),
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
                sql_for("apply", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Predefined(function, exprs) => {
                if UNARY.contains(function) {
                    // NOT
                    let (id, e) = exprs.first().unwrap();
                    let expr = e.to_sql(variables);
                    if *id == Ids::None {
                        format!("apply(\"not\", {expr})")
                    } else {
                        format!("not_({expr})")
                    }
                } else if ASSOCIATIVE.contains(function) {
                    // AND, OR
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
                                    else { Some(e.to_sql(variables)) }
                                },
                                _ => Some(e.to_sql(variables))
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
                } else if CHAINABLE.contains(function) {
                    // Eq, comparisons
                    let strings = exprs.iter()
                        .map( |(_, e)| e.to_sql(variables))
                        .collect::<Vec<_>>().join(", ");
                    match function {
                        // LINK src/doc.md#_Equality
                        Predefined::Eq => {
                            let equal = exprs.iter().zip(exprs.iter().skip(1))
                                    .all(|((_, a), (_, b))| *a == *b);
                            if equal {
                                "\"true\"".to_string()
                            } else {
                                let mut ids = Ids::All;
                                let terms = exprs.iter()
                                    .map(|(ids_, e)| {
                                        ids = max(ids.clone(), ids_.clone());
                                        e.to_sql(variables)
                                    }).collect::<Vec<_>>().join(", ");
                                if ids == Ids::None {
                                    format!("apply(\"=\",{terms})")
                                } else {
                                    format!("eq_({terms})")
                                }
                            }
                        },
                        Predefined::Less    => format!("compare_(\"<\", {strings})"),
                        Predefined::LE      => format!("compare_(\"<=\", {strings})"),
                        Predefined::GE      => format!("compare_(\">=\", {strings})"),
                        Predefined::Greater => format!("compare_(\">\", {strings})"),
                        _ => unreachable!()
                    }
                } else {
                    // Implies
                    assert_eq!(exprs.len(), 2);  // implies is a binary connective used internally
                    let e1 = exprs.first().unwrap().1.to_sql(variables);
                    let e2 = exprs.get(2).unwrap().1.to_sql(variables);
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
) -> String {
    if exprs.len() == 0 {
        format!("\"{function}\"")
    } else {
        let terms = exprs.iter()
            .map(|e| e.to_sql(variables))
            .collect::<Vec<_>>().join(", ");
        format!("{application}(\"{function}\", {terms})")
    }
}