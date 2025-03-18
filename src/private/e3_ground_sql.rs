// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;
use strum_macros::Display;

use crate::api::{QualIdentifier, SpecConstant, Symbol};
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::Column;


////////////////////// Data structures for grounding queries //////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    Predefined(Predefined, Box<Vec<SQLExpr>>),
    // Only in GroundingQuery.groundings
    Value(Column),  // in an interpretation table.
    //  Only in GroundingQuery.conditions
    Mapping(Ids, Box<SQLExpr>, Column),  // c_i, i.e., `is_id(expr) or expr=col`.
}

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Predefined {
    And,
    Or,
    Not,
    Implies,  // binary connective used internally.  "=>" is replaced by a disjunction in `annotate_term`.
    Eq,
}


///////////////////////////  Display //////////////////////////////////////////


impl SQLExpr {
    // it can return an empty string !
    pub(crate) fn show(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>,
        theta: bool  // true for theta join, false for condition or grounding
    ) -> String {

            /// Helper: use either "apply" or "construct2", according to the first argument.
            /// See description of these functions in y_db module.
            ///
            /// Arguments:
            /// * application: either "apply" or "construct2"
            fn sql_for(
                application: &str,
                function: String,
                exprs: &Box<Vec<SQLExpr>>,
                variables: &IndexMap<Symbol, Option<Column>>,
                theta: bool
            ) -> String {
                if exprs.len() == 0 {
                    format!("\"{function}\"")
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables, theta))
                        .collect::<Vec<_>>().join(", ");
                    format!("{application}(\"{function}\", {terms})")
                }
            }  // end helper

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
            SQLExpr::Apply(qual_identifier, exprs) => {
                sql_for("apply", qual_identifier.to_string(), exprs, variables, theta)
            },
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier.to_string(), exprs, variables, theta)
            },
            SQLExpr::Predefined(function, exprs) => {
                let name = function.to_string().to_lowercase();
                match function {
                    Predefined::And
                    | Predefined::Or => {
                        let exprs =
                            exprs.iter().cloned().filter_map( |e| {  // try to simplify
                                match e {
                                    SQLExpr::Boolean(b) => {
                                        if name == "and" && b { None }
                                        else if name == "or" && !b { None }
                                        else { Some(e.show(variables, theta)) }
                                    },
                                    _ => Some(e.show(variables, theta))
                                }
                            }).collect::<Vec<_>>();
                        if exprs.len() == 0 {
                            if name == "and" { "\"true\"".to_string() } else { "\"false\"".to_string()}
                        } else if exprs.len() == 1 {
                            exprs.first().unwrap().to_string()
                        } else {
                            format!("{name}_({})", exprs.join(", "))
                        }
                    },
                    Predefined::Not => {
                        let expr = exprs.first().unwrap().show(variables, theta);
                        if expr == "true" {
                            "false".to_string()
                        } else if expr == "false" {
                            "true".to_string()
                        } else {
                            format!("not_({expr})")
                        }
                    },
                    Predefined::Implies => {
                        assert_eq!(exprs.len(), 2);  // implies is a binary connective used internally
                        let e1 = exprs.first().unwrap().show(variables, theta);
                        let e2 = exprs.get(2).unwrap().show(variables, theta);
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
                    },
                    Predefined::Eq => {
                        let terms = exprs.iter()
                            .map(|e| e.show(variables, theta))
                            .collect::<Vec<_>>().join(", ");
                        format!("eq_({terms})")
                    }
                }
            }
            SQLExpr::Value(column) => column.to_string(),
            SQLExpr::Mapping(ids, expr, column) => {
                let value = expr.show(variables, theta);
                let column = column.to_string();

                if value == column {
                    "".to_string()
                } else if theta {
                    match ids {
                        Ids::All =>
                             format!("{value} = {column}"),
                        Ids::Some =>
                             format!("(NOT is_id({value}) OR {value} = {column})"),
                        Ids::None =>
                            if let SQLExpr::Variable(_) = **expr {  // an infinite variable mapped to an interpretation
                                // Variable + Ids::None describe an infinite variable
                                format!("{value} = {column}")
                            } else {
                                "".to_string()
                            },
                    }
                } else {
                    match ids {
                        Ids::All =>
                             "".to_string(),
                        Ids::Some =>
                             format!("or_(is_id({value}), apply(\"=\",{value}, {column}))"),
                        Ids::None =>
                             format!("apply(\"=\",{value}, {column})"),
                    }
                }
            },
        }
    }
}
