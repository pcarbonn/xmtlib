// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::IndexMap;

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
    Construct(Symbol, Box<Vec<SQLExpr>>),  // constructor
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    // Only in GroundingQuery.groundings
    Value(Column),  // in an interpretation table.
    //  Only in GroundingQuery.conditions
    Equality(bool, Box<SQLExpr>, Column),  // gated c_i.
}

impl SQLExpr {
    fn show(&self, variables: &IndexMap<Symbol, Column>) -> String {
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
            SQLExpr::Construct(symbol, exprs) => todo!(),
            SQLExpr::Apply(qual_identifier, exprs) => {
                if exprs.len() == 0 {
                    format!("\"{qual_identifier}\"")
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables))
                        .collect::<Vec<_>>().join(", ");
                    format!("apply(\"{qual_identifier}\", {})", terms)
                }
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
    // pub(crate) where_: Vec<(Column, Column)>,  // pairs of columns representing the same variable in (different) interpretation tables

    pub(crate) outer: bool,  // true if outer natural join
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

        let condition = self.conditions.iter()
            .map( |e| format!("({})", e.show(&self.variables)) )
            .collect::<Vec<_>>().join(" AND ");
        let condition =
            if condition == "" {
                "".to_string()
            } else if variables != "" {
                format!(", {condition} AS cond")
            } else {
                format!("{condition} AS cond")
            };

        let grounding =
            if condition == "" {
                format!("{} AS G", self.grounding.show(&self.variables))
            } else {
                format!(", {} AS G", self.grounding.show(&self.variables))
            };

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
        let naturals = if self.outer {
                vec![naturals.join(" OUTER JOIN ")]
            } else {
                naturals  // will be joined next
            };

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

        let tables = [naturals, thetas].concat();
        let tables = if 0 < tables.len() {
                format!(" FROM {}", tables.join(" JOIN "))
            } else { "".to_string() };

        write!(f, "SELECT {variables}{condition}{grounding}{tables}")
    }
}


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
        outer: false,
        ids: Ids::All,
    }
}


pub(crate) fn query_compound(
    qual_identifier: &QualIdentifier,
    sub_queries: &mut Vec<GroundingQuery>,
    solver: &mut Solver
) -> Result<GroundingQuery, SolverError> {

    let mut variables: IndexMap<Symbol, Column> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins: IndexMap<TableName, Vec<Symbol>> = IndexMap::new();
    let mut theta_joins = vec![];
    let mut ids: Ids = Ids::All;

    for sub_q in sub_queries {

        conditions.append(&mut sub_q.conditions);
        groundings.push(sub_q.grounding.clone());
        natural_joins.append(&mut sub_q.natural_joins.clone());
        theta_joins.append(&mut sub_q.theta_joins);
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
    let grounding = SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings));

    Ok(GroundingQuery {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        outer: false,
        ids,
    })
}

// impl GroundingQuery {

//     /// first mandatory step in building a GroundingQuery for an interpreted function application.
//     fn add_interpretation(
//         &mut self,
//         index: TermId,  // index of self in solver.groundings
//         interpretation_table: String
//     ) -> () {
//         self.interpretation_name = format!("{interpretation_table}_{index}");
//         let join = format!(" {interpretation_table} AS {interpretation_table}_{index} ");
//         self.theta_joins.push(join);
//     }

//     /// add a sub-term using a natural or outer join
//     fn add_sub_term<F>(
//         &mut self,
//         position: usize,  // index of the sub-term in the list of argument
//         subterm_id: TermId,  // TermId of the sub-term
//         sub_grounding_view: GroundingQuery,  // grounding view of the sub-term,
//         variant: Option<(F, Option<String>)>  // None for interpretation_table, or (lambda, default)
//     ) -> Result<(), SolverError>
//     where F: Fn(&mut Self, Vec<usize>) -> String,
//     {
//         if let Some((_, first_occurrence, _)) = self.natural_joins.get_full(&subterm_id) {

//             // term already in the natural join --> reuse it
//             let grounding = self.groundings[*first_occurrence].clone();
//             self.groundings.push(grounding);
//             return Ok(())

//         }

//         // check if the sub_grounding_view is a variable  (sgv.var[0] = sgv.g[0])
//         let is_variable =
//             sub_grounding_view.variables.len() == 1
//             && sub_grounding_view.groundings.len() == 1
//             && sub_grounding_view.variables[0] == sub_grounding_view.groundings[0];

//         if is_variable {
//             if self.interpretation_name != "" {

//                 // the value of the variable is in the interpretation table, not in a Type table
//                 let (symbol, _) = sub_grounding_view.variables.first()
//                     .ok_or(InternalError(245566396))?;
//                 let column = format!("{}.a_{position}", self.interpretation_name);
//                 self.variables.insert(symbol.clone(), column.clone());
//                 self.groundings.push(column);
//                 return Ok(())
//             }
//         }

//         // join the variables
//         for (symbol, new_column) in sub_grounding_view.variables {
//             if let Some(old_column) = self.variables.get(&symbol) {
//                 // variable already in self -> join it
//                 assert_eq!(old_column.clone(), new_column)
//             } else {
//                 self.variables.insert(symbol, new_column);
//             }
//         }

//         assert_eq!(sub_grounding_view.groundings.len(), 1);
//         self.groundings.push(sub_grounding_view.groundings[0].clone());

//         // let top = self.natural_joins.len();
//         // for (index, (first_occurrence, natural_join)) in sub_grounding_view.natural_joins {
//         //     self.natural_joins.insert(top+index, (first_occurrence, natural_join));
//         // }


//         Ok(())
//     }
// }


