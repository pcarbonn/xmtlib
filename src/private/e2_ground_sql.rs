// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;

use crate::api::{QualIdentifier, SpecConstant, Symbol};
use crate::private::e1_ground_query::{Column, Ids};


////////////////////// Data structures for grounding queries //////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    Predefined(QualIdentifier, Box<Vec<SQLExpr>>),
    // Only in GroundingQuery.groundings
    Value(Column),  // in an interpretation table.
    //  Only in GroundingQuery.conditions
    Equality(Ids, Box<SQLExpr>, Column),  // c_i, i.e., `is_id(expr) or expr=col`.
}


///////////////////////////  Display //////////////////////////////////////////


impl SQLExpr {
    // it can return an empty string !
    pub(crate) fn show(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>
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
                variables: &IndexMap<Symbol, Option<Column>>
            ) -> String {
                if exprs.len() == 0 {
                    format!("\"{function}\"")
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables))
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
                sql_for("apply", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Predefined(qual_identifier, exprs) => {
                let function = qual_identifier.to_string();
                // try to simplify
                if ["and", "or"].contains(&function.as_str()) {
                    let exprs =
                        exprs.iter().cloned().filter_map( |e| {  // try to simplify
                            match e {
                                SQLExpr::Boolean(b) => {
                                    if function == "and" && b { None }
                                    else if function == "or" && !b { None }
                                    else { Some(e.show(variables)) }
                                },
                                _ => Some(e.show(variables))
                            }
                        }).collect::<Vec<_>>();
                    if exprs.len() == 0 {
                        if function == "and" { "\"true\"".to_string() } else { "\"false\"".to_string()}
                    } else if exprs.len() == 1 {
                        exprs.first().unwrap().to_string()
                    } else {
                        format!("{function}_({})", exprs.join(", "))
                    }
                } else if function == "not" {
                    let expr = exprs.first().unwrap().show(variables);
                    if expr == "true" {
                        "false".to_string()
                    } else if expr == "false" {
                        "true".to_string()
                    } else {
                        format!("not_({})", expr)
                    }
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables))
                        .collect::<Vec<_>>().join(", ");
                    format!("{function}({terms})")
                }
            }
            SQLExpr::Value(column) => column.to_string(),
            SQLExpr::Equality(ids, expr, column) => {
                let expr = expr.show(variables);
                match ids {
                    Ids::All =>
                         "".to_string(),
                    Ids::Some =>
                         format!("or_(is_id({expr}), apply(\"=\",{expr}, {column}))"),
                    Ids::None =>
                         format!("apply(\"=\",{expr}, {column})"),
                }
            },
        }
    }
}
