// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::IndexMap;
use itertools::Either;

use crate::api::{QualIdentifier, SpecConstant, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TableName {
    base_table: String,
    index: TermId, // to disambiguate
}
impl std::fmt::Display for TableName {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}_{}", self.base_table, self.index)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Column {
    table_name: TableName,
    column: String
}
impl std::fmt::Display for Column {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}.{}", self.table_name, self.column)
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SQLExpr {
    Constant(SpecConstant),
    Variable(Symbol),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    // Only in GroundingQuery.groundings
    Value(Column),  // in an interpretation table.
    //  Only in GroundingQuery.conditions
    Equality(bool, Box<SQLExpr>, Column),  // gated c_i.
}

impl SQLExpr {
    fn show(
        &self,
        variables: &IndexMap<Symbol, Column>
    ) -> String {

            /// Helper: use either "apply" or "construct2", according to the first argument.
            /// See description of these functions in y_db module.
            ///
            /// Arguments:
            /// * function: either "apply" or "construct2"
            fn sql_for(
                function: &str,
                qual_identifier: &QualIdentifier,
                exprs: &Box<Vec<SQLExpr>>,
                variables: &IndexMap<Symbol, Column>
            ) -> String {
                if exprs.len() == 0 {
                    format!("\"{qual_identifier}\"")
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables))
                        .collect::<Vec<_>>().join(", ");
                    format!("{function}(\"{qual_identifier}\", {})", terms)
                }
            }  // end helper

        match self {
            SQLExpr::Constant(spec_constant) => {
                match spec_constant {
                    SpecConstant::Numeral(s) => format!("\"{s}\""),
                    SpecConstant::Decimal(s) => format!("\"{s}\""),
                    SpecConstant::Hexadecimal(s) => format!("\"{s}\""),
                    SpecConstant::Binary(s) => format!("\"{s}\""),
                    SpecConstant::String(s) => format!("\"{s}\""),
                }
            },
            SQLExpr::Variable(symbol) => todo!(),
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier, exprs, variables)
            },
            SQLExpr::Apply(qual_identifier, exprs) => {
                sql_for("apply", qual_identifier, exprs, variables)
            },
            SQLExpr::Value(column) => todo!(),
            SQLExpr::Equality(_, expr, column) => todo!(),
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ids {
    All, // lowest
    Some_,
    None // highest
}


/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GroundingQuery {

    pub(crate) variables: IndexMap<Symbol, Column>,  // maps variables to either a Type table or (better) an Interpretation table
    pub(crate) conditions: Vec<SQLExpr>,  // vector of non-empty SQL expressions
    pub(crate) grounding: SQLExpr,
    pub(crate) natural_joins: IndexMap<TableName, Vec<Symbol>>, // indexed table name -> list of its variables.
    pub(crate) theta_joins: Vec<(TableName, Vec<(bool, SQLExpr, Column)>)>, // indexed table name + mapping of (gated) expressions to value column
    // pub(crate) where_: Vec<SQLExpr>,  // filters on the query, e.g. to select TU values

    pub(crate) default: String,  // "" for inner natural join; "true" (resp. "false") for "and" (resp. "or")
    pub(crate) ids: Ids,  // if the groundings are all Ids
}

impl std::fmt::Display for GroundingQuery {

    // SELECT {variables.0} AS {variables.1},
    //        {condition} AS cond,  -- if condition
    //        {grounding} AS G,
    //   FROM {natural joins}
    //   JOIN {theta_joins}

    // SQL formatting
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let variables = self.variables.iter()
            .map(|(symbol, column)| format!("{column} AS {symbol}"))
            .collect::<Vec<_>>()
            .join(", ");

        // condition
        let condition = self.conditions.iter()
            .map( |e| {
                if self.default == ""
                || self.natural_joins.len() <= 1 {  // can't have nulls
                    format!("({})", e.show(&self.variables))
                } else {
                    format!("IFNULL({}, \"{}\")", e.show(&self.variables), self.default)
                }
            })
            .collect::<Vec<_>>().join(" AND ");
        let condition =
            if condition == "" {
                "".to_string()
            } else if variables != "" {
                format!(", {condition} AS cond")
            } else {
                format!("{condition} AS cond")
            };

        // grounding
        let grounding =
            if self.default == ""
            || self.natural_joins.len() <= 1 {  // can't have nulls
                self.grounding.show(&self.variables)
            } else {
                format!("IFNULL({}, \"{}\")", self.grounding.show(&self.variables), self.default)
            };
        let grounding =
            if condition == "" {
                format!("{} AS G", grounding)
            } else {
                format!(", {} AS G", grounding)
            };

        // natural joins
        let naturals = self.natural_joins.iter()
            .map(|(table_name, on)|
                if on.len() == 0 {
                    format!("{} AS {table_name}", table_name.base_table)
                } else {
                    let on = on.iter()
                        .map( | symbol | {
                            let column = self.variables.get(symbol).unwrap();
                            format!(" {table_name}.{symbol} = {column}")  // TODO eliminate true
                        }).collect::<Vec<_>>().join(" AND ");
                    format!("{} AS {table_name} ON {on}", table_name.base_table)
                })
            .collect::<Vec<_>>();
        let naturals =
            if self.default !="" && 0 < naturals.len() {
                vec![naturals.join(" OUTER JOIN ")]
            } else {
                naturals  // will be joined next
            };

        // theta joins
        let thetas = self.theta_joins.iter()
            .map( | (table_name, mapping) | {
                let on = mapping.iter()
                    .map( | (gated, e, col) | {
                        let gate = if *gated {
                                format!("NOT(is_id({})) OR ", e.show(&self.variables))
                            } else {
                                "".to_string()
                            };
                        format!(" ({gate}{col} = {}) ", e.show(&self.variables))
                    }).collect::<Vec<_>>().join(" AND ");
                format!("{} AS {table_name} ON {on}", table_name.base_table)
            }).collect::<Vec<_>>();

        // naturals + thetas
        let tables = [naturals, thetas].concat();
        let tables = if 0 < tables.len() {
                format!(" FROM {}", tables.join(" JOIN "))
            } else { "".to_string() };

        // let where_ = self.where_.iter()
        //     .map( |e| e.show(&self.variables) )
        //     .collect::<Vec<_>>();
        // let where_ = if 0 < where_.len() {
        //     format!(" WHERE {}", where_.join(" AND "))
        //     } else { "".to_string() };

        write!(f, "SELECT {variables}{condition}{grounding}{tables}")
    }
}

// impl GroundingQuery {
//     fn add_where_clause(
//         &self,
//         condition: SQLExpr
//     ) -> Self {
//         let mut res = self.clone();
//         match self.ids {
//             Ids::All | Ids::Some_ => res.where_.push(condition),
//             Ids::None => {},  // useless
//         }
//         res
//     }
// }

/////////////////////  Grounding implementations ////////////////////////////////////////

pub(crate) fn query_spec_constant(
    spec_constant: &SpecConstant
) -> GroundingQuery {
    GroundingQuery {
        variables: IndexMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexMap::new(),
        theta_joins: vec![],
        // where_: vec![],
        default: "".to_string(),
        ids: Ids::All,
    }
}

/// creates a query for a compound term, according to `variant`.
///
/// Arguments:
/// * variant: either an interpretation or a function name.  The function name can be:
///     * "apply" (implies inner natural joins)
///     * "construct" (implies inner natural joins)
///     * "and" or "or" (implies outer natural joins)
pub(crate) fn query_for_compound(
    qual_identifier: &QualIdentifier,
    sub_queries: &mut Vec<GroundingQuery>,
    variant: Either<TableName, String>
) -> Result<GroundingQuery, SolverError> {

    let mut variables: IndexMap<Symbol, Column> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins: IndexMap<TableName, Vec<Symbol>> = IndexMap::new();
    let mut theta_joins = vec![];
    // let mut where_= vec![];
    let mut ids: Ids = Ids::All;

    for sub_q in sub_queries {

        conditions.append(&mut sub_q.conditions);
        groundings.push(sub_q.grounding.clone());
        natural_joins.append(&mut sub_q.natural_joins.clone());
        theta_joins.append(&mut sub_q.theta_joins);
        // where_.append(&mut sub_q.where_.clone());
        ids = max(ids, sub_q.ids.clone());

        for (symbol, column) in &sub_q.variables {
            // insert if not there yet,
            // or if it was a natural join column, but not anymore
            if match variables.get(symbol) {
                    None => true,
                    Some(old_column) =>
                        natural_joins.contains_key(&old_column.table_name)
                        && ! sub_q.natural_joins.contains_key(&column.table_name)
                } {
                    variables.insert(symbol.clone(), column.clone());
                }
        }
    }

    // todo: use interpretation table of qual_identifier
    let (grounding, default) =
        match variant {
            Either::Left(table_name) => todo!(),
            Either::Right(function) => {  // no interpretation
                match function.as_str() {
                    "apply" =>
                        ( SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings)),
                          "".to_string()
                        ),
                    "construct" =>
                        ( SQLExpr::Construct(qual_identifier.clone(), Box::new(groundings)),
                          "".to_string()
                        ),
                    "and" =>
                        ( SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings)),
                          "true".to_string()
                        ),
                    "or" =>
                        ( SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings)),
                            "false".to_string()
                        ),
                    _ => return Err(SolverError::InternalError(62479519))
                }
            },
        };

    Ok(GroundingQuery {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        // where_,
        default,
        ids,
    })
}



