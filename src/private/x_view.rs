// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;

use crate::{api::{QualIdentifier, SpecConstant, Symbol}, error::SolverError::{self, InternalError}};
use crate::solver::TermId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Column {
    base_table: String,
    index: TermId, // to disambiguate
    column: String
}
impl std::fmt::Display for Column {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}_{}.{}", self.base_table, self.index, self.column)
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SQLExpr {
    Constant(SpecConstant),
    Variable(Symbol),
    Construct(Symbol, Box<Vec<SQLExpr>>),  // constructor
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    // Only in GroundingView.groundings
    Value(Column),  // in an interpretation table.
    //  Only in GroundingView.conditions
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
            SQLExpr::Apply(qual_identifier, exprs) => todo!(),
            SQLExpr::Value(column) => todo!(),
            SQLExpr::Equality(_, expr, column) => todo!(),
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Ids { All, Some_, None }


/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GroundingView {

    pub(crate) variables: IndexMap<Symbol, Column>,  // maps variables to either a Type table or (better) an Interpretation table
    pub(crate) conditions: Vec<SQLExpr>,  // vector of non-empty SQL expressions
    pub(crate) grounding: SQLExpr,
    pub(crate) natural_joins: IndexMap<String, Vec<Symbol>>, // indexed table name -> list of its variables.
    pub(crate) theta_joins: Vec<(String, Vec<(bool, SQLExpr, Column)>)>, // indexed table name + mapping of (gated) expressions to value column
    // pub(crate) where_: Vec<(Column, Column)>,  // pairs of columns representing the same variable in (different) interpretation tables

    pub(crate) outer: bool,  // true if outer natural join
    pub(crate) _ids: Ids,  // if the groundings are all Ids
}

impl std::fmt::Display for GroundingView {

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
            .map(|(table, on)|
                if on.len() == 0 {
                    table.to_string()
                } else {
                    let on = on.iter()
                        .map( | symbol | {
                            let column = self.variables.get(symbol).unwrap();
                            format!(" {table}.{symbol} = {column}")
                        }).collect::<Vec<_>>().join(" AND ");
                    format!("{table} ON {on}")
                })
            .collect::<Vec<_>>();
        let naturals = if self.outer {
                vec![naturals.join(" OUTER JOIN ")]
            } else {
                naturals  // will be joine next
            };

        let thetas = self.theta_joins.iter()
            .map( | (name, mapping) | {
                let on = mapping.iter()
                    .map( | (gated, e, col) | {
                        let gate = if *gated {
                                format!("NOT(is_id({})) OR ", e.show(&self.variables))
                            } else {
                                "".to_string()
                            };
                        format!(" ({gate}{col} = {}) ", e.show(&self.variables))
                    }).collect::<Vec<_>>().join(" AND ");
                format!("{} ON {on}", name.clone())
            }).collect::<Vec<_>>();

        let tables = [naturals, thetas].concat();
        let tables = if 0 < tables.len() {
                format!(" FROM {}", tables.join(" JOIN "))
            } else { "".to_string() };

        write!(f, "SELECT {variables}{condition}{grounding}{tables}")
    }
}


// impl GroundingView {

//     /// first mandatory step in building a GroundingView for an interpreted function application.
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
//         sub_grounding_view: GroundingView,  // grounding view of the sub-term,
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


