// Copyright Pierre Carbonnelle, 2025.

use std::fmt::Display;
use indexmap::{IndexMap, IndexSet};

use crate::api::{SortedVar, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e1_ground_view::{GroundingView, Ids, View};
use crate::private::e3_ground_sql::{SQLExpr, Predefined};



////////////////////// Data structures for grounding queries ////////


/// Contains what is needed to construct the grounding query of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GroundingQuery {
    Join {
        /// maps variables to None if its domain is infinite or to a Column in a Type or Interpretation table.
        variables: IndexMap<Symbol, Option<Column>>,
        conditions: Vec<SQLExpr>,  // vector of non-empty SQL expressions
        grounding: SQLExpr,
        natural_joins: IndexSet<NaturalJoin>,
        theta_joins: IndexSet<ThetaJoin>,
        where_: Vec<SQLExpr>,  // where clause for comparisons
    },
    Aggregate {
        agg: String,  // "" (top-level), "and" or "or"
        free_variables: IndexMap<Symbol, Option<TableName>>,  // None for infinite variables
        infinite_variables: Vec<SortedVar>,
        sub_view: Box<GroundingView>,  // the sub_view has more variables than free_variables
        exclude: Option<bool>
    },
    Union {
        sub_queries: Box<Vec<GroundingQuery>>  // the sub-queries are Join and have the same columns
    }
}


/// Natural join with a table interpreting a variable or a quantification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum NaturalJoin {
    Variable(TableName, Symbol),  // natural join with a table interpreting a variable
    View(TableName, Vec<Symbol>),  // natural join with a table interpreting, e.g., a quantification
}


/// indexed table name + mapping of (gated) expressions to value column
pub(crate) type ThetaJoin = (TableName, Vec<SQLExpr>);


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TableName {
    pub(crate) base_table: String,  // contains index for views !
    pub(crate) index: TermId, // to disambiguate interpretation table
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Column {
    pub(crate) table_name: TableName,
    column: String
}


///////////////////////////  Display //////////////////////////////////////////


impl std::fmt::Display for GroundingQuery {

    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundingQuery::Join{variables, conditions, grounding,
            natural_joins, theta_joins, where_,..} => {

                // SELECT {variables.0} AS {variables.1},
                //        {condition} AS if_,  -- if condition
                //        {grounding} AS G,
                //   FROM {natural joins}
                //   JOIN {theta_joins}
                //  WHERE {where_}

                let variables_ = variables.iter()
                    .map(|(symbol, column)| {
                        if let Some(column) = column {
                            format!("{column} AS {symbol}")
                        } else {
                            format!("\"{symbol}\" AS {symbol}")
                        }

                    }).collect::<Vec<_>>()
                    .join(", ");
                let variables_ = if variables_ == "" { variables_ } else { variables_ + ", "};

                // condition
                let condition = conditions.iter()
                    .map( |e| { e.show(&variables, false)})  // can be empty !
                    .filter( |c| c != "")
                    .map ( |c| format!("({c})"))
                    .collect::<Vec<_>>();
                let condition =
                    if condition.len() == 0 {
                        "".to_string()
                    } else if condition.len() == 1 {
                        format!("{} AS if_, ", condition[0])
                    } else {
                        format!("and_({}) AS if_, ", condition.join(", "))
                    };

                // grounding
                let grounding_ = grounding.show(&variables, false);
                let grounding_ = format!("{grounding_} AS G");

                // natural joins
                let naturals = natural_joins.iter()
                    .map(|natural_join| {

                            /// Helper function.  Returns the name of a table, with an optional alias.
                            fn name(table_name: &TableName) -> String {
                                if table_name.index == 0 {
                                    table_name.base_table.to_string()
                                } else {
                                    format!("{} AS {table_name}", table_name.base_table)
                                }
                            }  // end helper

                        match natural_join {
                            NaturalJoin::Variable(table_name, _) => {
                                // a variable table never has join conditions
                                name(table_name)
                            },
                            NaturalJoin::View(table_name, symbols) => {
                                let name = name(table_name);
                                let on = symbols.iter()
                                    .filter_map( | symbol | {
                                        let this_column = Column::new(table_name, symbol).to_string();
                                        let column = variables.get(symbol).unwrap();
                                        if let Some(column) = column {
                                            if this_column != column.to_string() {
                                                Some(format!(" {this_column} = {column}"))
                                            } else {
                                                None
                                            }
                                        } else {
                                            unreachable!("348595")
                                        }
                                    }).collect::<Vec<_>>().join(" AND ");
                                if on == "" { name  } else { format!("{name} ON {on}")}
                            }
                        }
                    })
                    .collect::<Vec<_>>();

                // theta joins
                let thetas = theta_joins.iter()
                    .map( | (table_name, mapping) | {
                        let on = mapping.iter()
                            .filter_map( | expr | {
                                let theta = expr.show(variables, true);
                                if theta.len() == 0 {
                                    None
                                } else {
                                    Some(theta)
                                }
                            }).collect::<Vec<_>>().join(" AND ");
                        let on = if on == "" { on } else { format!(" ON {on}")};

                        format!("{} AS {table_name}{on}", table_name.base_table)
                    }).collect::<Vec<_>>();

                // naturals + thetas + empty
                let tables = [naturals, thetas].concat();
                let mut first_where = "".to_string();
                let tables =
                    if tables.len() == 0 {
                        "".to_string()
                    } else if tables.len() == 1 {
                        let tables = format!(" FROM {}", tables.join(" JOIN "));  // only one !
                        if let Some((before, after)) = tables.split_once(" ON ") {
                            first_where = after.to_string();
                            before.to_string()
                        } else {
                            tables
                        }
                    } else {
                        format!(" FROM {}", tables.join(" JOIN "))
                    };

                // LINK src/doc.md#_Equality
                let second_where =
                    if where_.len() == 1 {
                        where_.iter()
                            .map(|e| e.show(&variables, true))
                            .collect::<Vec<_>>().join("")  // no join, because only one where clause
                    } else {
                        "".to_string()  // todo: join by AND (or OR for UF view ?!)
                    };

                let where_ = first_where + &second_where;
                let where_ = if where_ == "" { where_ } else { format!(" WHERE {where_}") };

                write!(f, "SELECT {variables_}{condition}{grounding_}{tables}{where_}")
            }
            GroundingQuery::Aggregate { agg, free_variables, infinite_variables, sub_view, exclude } => {
                if let GroundingView::View { condition, ..} = &**sub_view {
                    // SELECT {free_variables},
                    //        "(forall ({infinite_vars}) " || and_aggregate(implies_(if_, G)) || ")" AS G
                    //   FROM {sub_view}
                    //  GROUP BY {free_variables*}
                    // HAVING {G} <> "{exclude}"

                    let free = free_variables.iter()
                        .map( |(symbol, _)| symbol.to_string() )
                        .collect::<Vec<_>>().join(", ");
                    let free = if free == "" { free } else { free + ", " };

                    // group-by is free minus the infinite variables
                    let group_by = free_variables.iter()
                        .filter( |(_, table_name)| table_name.is_some() )
                        .map( |(symbol, _)| symbol.to_string())
                        .collect::<Vec<_>>().join(", ");
                    let group_by =
                        if group_by == "" || agg == "" {
                            "".to_string()
                        } else {
                            format!(" GROUP BY {group_by}")
                        };

                    // compute the grounding
                    let infinite_vars = infinite_variables.iter()
                        .map ( |sv| sv.to_string() )
                        .collect::<Vec<_>>().join(" ");
                    let grounding =
                        if ! condition {
                            match agg.as_str() {
                                "" => "G",
                                "and" => "and_aggregate(G)",
                                "or" => "or_aggregate(G)",
                                _ => unreachable!()
                            }
                        } else {
                            match agg.as_str() {
                                "" => "implies_(if_, G)",
                                "and" => "and_aggregate(implies_(if_, G))",
                                "or" => "or_aggregate(and_(if_, G))",
                                _ => unreachable!()
                            }
                        };
                    let grounding =
                        if infinite_vars.len() == 0 {
                            format!("{grounding}")
                        } else {
                            match agg.as_str() {
                                "" => format!("\"(forall ({infinite_vars}) \" || {grounding} || \")\""),
                                "and" => format!("\"(forall ({infinite_vars}) \" || {grounding} || \")\""),
                                "or" => format!("\"(exists ({infinite_vars}) \" || {grounding} || \")\""),
                                _ => unreachable!()
                            }
                        };

                    let having =
                        if let Some(bool) = exclude {
                            format!(" HAVING {grounding} <> \"{bool}\"")
                        } else {
                            "".to_string()
                        };

                    write!(f, "SELECT {free}{grounding} as G from ({sub_view}){group_by}{having}")
                } else {  // empty view
                    write!(f, "{}", sub_view)
                }
            },
            GroundingQuery::Union { sub_queries, .. } => {
                let view = sub_queries.iter()
                    .map( |query| query.to_string() )
                    .collect::<Vec<_>>().join(" UNION ");
                write!(f, "{}", view)
            }
        }
    }
}


impl std::fmt::Display for TableName {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.index == 0 {
            write!(f, "{}", self.base_table)
        } else {
            write!(f, "{}_{}", self.base_table, self.index)
        }
    }
}


impl std::fmt::Display for Column {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}.{}", self.table_name, self.column)
    }
}


/////////////////////  Grounding Query utilities  //////////////////////////////


impl GroundingQuery {

    pub(crate) fn negate(
        &self,
        free_variables: IndexMap<Symbol, Option<TableName>>,
        index: TermId,
        view: View,
        ids: &Ids,
        solver: &mut Solver
    ) -> Result<GroundingView, SolverError> {
        match self {
            GroundingQuery::Join { variables, conditions, grounding,
            natural_joins, theta_joins, where_, ..} => {

                let new_grounding =
                    if *ids == Ids::All {
                        if view == View::TU {
                            SQLExpr::Boolean(false)  // all ids were true
                        } else if view == View::UF {
                            SQLExpr::Boolean(true)  // all ids were false
                        } else {
                            SQLExpr::Predefined(Predefined::Not, Box::new(vec![grounding.clone()]))
                        }
                    } else {
                        SQLExpr::Predefined(Predefined::Not, Box::new(vec![grounding.clone()]))
                    };
                let query = GroundingQuery::Join {
                    variables: variables.clone(),
                    conditions: conditions.clone(),
                    grounding: new_grounding,
                    natural_joins: natural_joins.clone(),
                    theta_joins: theta_joins.clone(),
                    where_: where_.clone()};
                let table_name = TableName{base_table: format!("negate_{index}"), index: 0};
                GroundingView::new(table_name, free_variables, query, ids.clone(), solver)
            }
            GroundingQuery::Aggregate { agg, infinite_variables, sub_view, exclude, .. } => {
                let query = GroundingQuery::Aggregate {
                    agg : if agg == "or" { "and".to_string() } else { "or".to_string() },
                    free_variables: free_variables.clone(),
                    infinite_variables: infinite_variables.clone(),
                    sub_view: Box::new(sub_view.negate(index, view, solver)?),
                    exclude: if let Some(bool) = exclude { Some(! bool) } else { *exclude }
                };
                let table_name = TableName{base_table: format!("negate_{index}"), index: 0};
                GroundingView::new(table_name, free_variables, query, ids.clone(), solver)
            },
            GroundingQuery::Union {..} => unreachable!()
        }
    }

}


impl TableName {
    #[inline]
    pub(crate) fn new<T: Display + ? Sized>(base_table: &T, index: usize) -> Self {
        TableName{base_table: base_table.to_string(), index}
    }
}


impl Column {
    #[inline]
    pub(crate) fn new<T: Display + ? Sized>(table_name: &TableName, column: &T) -> Self {
        Column{table_name: table_name.clone(), column: column.to_string()}
    }
}