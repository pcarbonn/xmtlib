// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexSet;
use itertools::Either::{self, Left, Right};
use std::cmp::max;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

use crate::ast::{SortedVar, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e1_ground_view::{GroundingView, Ids, ViewType};
use crate::private::e3_ground_sql::{Mapping, SQLExpr, Predefined};
use crate::private::z_utilities::OptionMap;



////////////////////// Data structures for grounding queries ////////


/// Contains what is needed to construct the grounding query of a term, in a composable way.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum GroundingQuery {
    Join {
        /// maps variables to None if its domain is infinite or to a Column in a Type or Interpretation table.
        variables: OptionMap<Symbol, Column>,
        conditions: Vec<Either<Mapping, Option<TableAlias>>>,  // vector of mapping or `if_` column of a table. If TableAlias is None, "true".
        grounding: SQLExpr,
        natural_joins: IndexSet<NaturalJoin>,  // joins of grounding sub-queries
        theta_joins: IndexSet<ThetaJoin>,  // joins with interpretation tables

        precise: bool,  // true if the (boolean) grounding only has values consistent with the view (e.g., no "false" in TU view)
    },
    Aggregate {
        agg: String,  // "" (top-level), "and" or "or"
        free_variables: OptionMap<Symbol, TableAlias>,  // None for infinite variables
        infinite_variables: Vec<SortedVar>,
        sub_view: Box<GroundingView>,  // the sub_view has more variables than free_variables

        // precise: always false
    },
    Union {
        sub_queries: Box<Vec<GroundingQuery>>,  // the sub-queries are Join and have the same columns

        precise: bool  // true if the (boolean) grounding only has values consistent with the view (e.g., no "false" in TU view)
    }
}


/// Natural join with a table interpreting a variable or a quantification.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum NaturalJoin {
    CrossProduct(TableAlias, Symbol),  // natural join with a table interpreting a variable
    ViewJoin(GroundingQuery, TableAlias, Vec<Symbol>),  // natural join with a view interpreting, e.g., a quantification
}
// Custom Hash to avoid hashing a GroundingQuery
impl Hash for NaturalJoin {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // You can use a tag to differentiate variants
        match self {
            NaturalJoin::CrossProduct(alias, symbol) => {
                0u8.hash(state);
                alias.hash(state);
                symbol.hash(state);
            }
            NaturalJoin::ViewJoin(_query, alias, symbols) => {
                1u8.hash(state);
                // query is ignored
                alias.hash(state);
                symbols.hash(state);
            }
        }
    }
}

/// indexed table name + mapping of (gated) expressions to value column
pub(crate) type ThetaJoin = (TableAlias, Vec<Mapping>);


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TableAlias {
    pub(crate) base_table: TableName,  // contains index for views !
    pub(crate) index: TermId, // to disambiguate interpretation table
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Column {
    pub(crate) table_alias: TableAlias,
    column: String
}


/// The name of a table or view in the database
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub(crate) struct TableName(pub(crate) String);


///////////////////////////  Display //////////////////////////////////////////

pub(crate) const INDENT: &str = "       ";


impl std::fmt::Display for GroundingQuery {

    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.to_sql(&IndexSet::new(), "").0)
    }
}


impl GroundingQuery {
    pub(crate) fn to_sql(
        &self,
        var_joins: &IndexSet<NaturalJoin>,  // the interpretation of the variables
        indent: &str
    ) -> (String, Ids) {
        match self {
            GroundingQuery::Join{variables, conditions, grounding,
            natural_joins, theta_joins, ..} => {

                // SELECT {variables.0} AS {variables.1},
                //        {condition} AS if_,  -- if condition
                //        {grounding} AS G,
                //   FROM {natural joins}
                //   JOIN {theta_joins}
                //  WHERE {where_}

                // combine variables and sub_variables
                let mut variables = variables.clone();
                let mut natural_joins = natural_joins.clone();
                for join in var_joins.iter() {
                    if let NaturalJoin::CrossProduct(table_alias, symbol) = join {
                        if let Some(None) = variables.get(symbol) {  // must now add the variable join
                            let a1 = Symbol("a_1".to_string()); // todo
                            let col = Column::new(table_alias, &a1);
                            variables.insert(symbol.clone(), Some(col));
                            natural_joins.insert(join.clone());
                        }
                    } else {
                        unreachable!()  // because var_joins only contain variable joins
                    }
                };
                let variables = &variables;
                let natural_joins = &natural_joins;

                let variables_ = variables.iter()
                    .map(|(symbol, column)| {
                        if let Some(column) = column {
                            format!("{column} AS {symbol}")
                        } else {
                            format!("\"{symbol}\" AS {symbol}")
                        }

                    }).collect::<Vec<_>>()
                    .join(format!(",\n{indent}{INDENT}").as_str());
                let variables_ =
                    if variables_ == "" { variables_ }
                    else { format!("{variables_},\n{indent}{INDENT}") };

                // condition
                let condition = conditions.iter()
                    .filter_map( |e| {
                        match e {
                            Left(mapping) => mapping.to_if(variables),
                            Right(table) => {
                                if let Some(table) = table {
                                    Some(format!("{table}.if_"))
                                } else {
                                    None
                                }
                            }
                        }
                    }).collect::<Vec<_>>();
                let condition =
                    if condition.len() == 0 {
                        "".to_string()
                    } else if condition.len() == 1 {
                        format!("{} AS if_, \n{indent}{INDENT}", condition[0])
                    } else {
                        format!("and_({}) AS if_,\n{indent}{INDENT}", condition.join(", "))
                    };

                // grounding
                let (grounding_, ids) = grounding.to_sql(&variables);
                let grounding_ = format!("{grounding_} AS G");

                // natural joins
                let mut where_ = vec![];
                let naturals = natural_joins.iter().enumerate()
                    .map(|(i, natural_join)| {

                        // Helper function.  Returns the name of a table, with an optional alias.
                        let name = |table_name: &TableAlias| {
                            if table_name.index == 0 {
                                format!("{}", table_name.base_table)
                            } else {
                                format!("{} AS {table_name}", table_name.base_table)
                            }
                        };

                        match natural_join {
                            NaturalJoin::CrossProduct(table_name, _) => {
                                // a variable table never has join conditions
                                name(table_name)
                            },
                            NaturalJoin::ViewJoin(query, table_name, symbols) => {

                                // add the variable joins to var_joins
                                let mut var_joins = var_joins.clone();
                                for (symbol, col) in variables.iter() {
                                    if let Some(Column{table_alias, column: _}) = col {
                                        if ! table_alias.base_table.0.starts_with("Agg_") {  // todo
                                            let join = NaturalJoin::CrossProduct(table_alias.clone(), symbol.clone());
                                            var_joins.insert(join);
                                        }
                                    }
                                }

                                let indent1 = format!("{indent}{INDENT} ").to_string();
                                let query = query.to_sql(&var_joins, &indent1).0;

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

                                if on == "" {
                                    format!("({query}\n{indent1}) AS {name}")
                                } else {
                                    if i == 0 {
                                        if on != "" { where_.push(on) };
                                        format!("({query}\n{indent1}) AS {name}")
                                    } else {
                                        format!("({query}\n{indent1}) AS {name} ON {on}")
                                    }
                                }
                            }
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(format!("\n{indent}  JOIN ").as_str());

                // theta joins
                let thetas = theta_joins.iter().enumerate()
                    .map( | (i, (table_name, mapping)) | {
                        let on = mapping.iter()
                            .filter_map( | expr | expr.to_join(variables))
                            .collect::<Vec<_>>().join(" AND ");
                        if i == 0 && naturals.len() == 0 {
                            if on != "" { where_.push(on) };
                            format!("{} AS {table_name}", table_name.base_table)
                        } else {
                            let on = if on == "" { on } else { format!("\n{indent}{INDENT} ON {on}")};
                            format!("\n{indent}  JOIN {} AS {table_name}{on}", table_name.base_table)
                        }
                    }).collect::<Vec<_>>()
                    .join("");

                let where_ = if where_.len() == 0 {
                        "".to_string()
                    } else {
                        format!("\n{indent} WHERE {}", where_.join(" AND "))
                    };


                // naturals + thetas + empty
                let tables = if 0 < naturals.len() + thetas.len() {
                        format!("\n{indent}  FROM {naturals}{thetas}{where_}")
                    } else {
                        "".to_string()
                    };

                let comment = format!("-- Join({})\n{indent}", indent.len());
               (format!("{comment}SELECT {variables_}{condition}{grounding_}{tables}"),
                ids)
            }
            GroundingQuery::Aggregate { agg, free_variables, infinite_variables, sub_view, .. } => {
                if let GroundingView::View { condition, ..} = **sub_view {
                    // SELECT {free_variables},
                    //        "(forall ({infinite_vars}) " || and_aggregate(implies_(if_, G)) || ")" AS G
                    //   FROM {sub_view}
                    //  GROUP BY {free_variables*}

                    let free = free_variables.iter()
                        .map( |(symbol, _)| symbol.to_string() )
                        .collect::<Vec<_>>().join(", ");
                    let free = if free == "" { free } else { format!("{free},\n{indent}{INDENT}") };

                    // group-by the free variables
                    let group_by = free_variables.iter()
                        .map( |(symbol, _)| symbol.to_string())
                        .collect::<Vec<_>>().join(", ");
                    let group_by =
                        if group_by == "" || agg == "" {
                            "".to_string()
                        } else {
                            format!("\n{indent} GROUP BY {group_by}")
                        };

                    // compute the grounding
                    // LINK src/doc.md#_Infinite
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

                    let (sub_view, ids) = sub_view.to_sql(var_joins, format!("{indent}{INDENT}").as_str());

                    let comment = format!("-- Agg ({})\n{indent}", indent.len());
                    (format!("{comment}SELECT {free}{grounding} as G\n{indent} FROM ({sub_view}){group_by}"),
                     ids)
                } else {  // empty view
                    ("{}".to_string(), Ids::All)
                }
            },
            GroundingQuery::Union { sub_queries, .. } => {
                let mut ids = Ids::All;
                let view = sub_queries.iter()
                    .map( |query| {
                        let (sql, ids_) = query.to_sql(var_joins, indent);
                        ids = max(ids.clone(), ids_);
                        sql
                    }).collect::<Vec<_>>().join(format!("\n{indent}UNION\n{indent}").as_str());
                (view, ids)
            }
        }
    }
}


impl std::fmt::Display for TableName {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}


impl std::fmt::Display for TableAlias {
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
        write!(f, "{}.{}", self.table_alias, self.column)
    }
}


/////////////////////  Grounding Query utilities  //////////////////////////////


impl GroundingQuery {
    pub(crate) fn is_precise(&self) -> bool {
        match self {
            GroundingQuery::Join{ precise, ..}
            | GroundingQuery::Union { precise, ..} =>
                *precise,
            GroundingQuery::Aggregate {..} => false
        }
    }


    pub(crate) fn negate(
        &self,
        free_variables: OptionMap<Symbol, TableAlias>,
        index: TermId,
        view_type: ViewType,
        exclude: Option<bool>,
        all_ids: bool,
        solver: &mut Solver
    ) -> Result<GroundingView, SolverError> {

        let exclude = match exclude {
            None => None,
            Some(true) => Some(false),
            Some(false) => Some(true),
        };
        let base_table = TableName(format!("negate_{index}_{view_type}"));

        match self {
            GroundingQuery::Join { variables, conditions, grounding,
            natural_joins, theta_joins, precise,..} => {

                let new_grounding =
                    if all_ids {
                        if view_type == ViewType::TU {
                            SQLExpr::Boolean(false)  // all ids were true
                        } else if view_type == ViewType::UF {
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
                    precise: *precise
                };
                let table_alias = TableAlias{base_table, index: 0};
                GroundingView::new(table_alias, free_variables, query, exclude, all_ids)
            }
            GroundingQuery::Aggregate { agg, infinite_variables, sub_view, .. } => {
                let query = GroundingQuery::Aggregate {
                    agg : (if agg == "or" { "and" } else { "or" }).to_string(),
                    free_variables: free_variables.clone(),
                    infinite_variables: infinite_variables.clone(),
                    sub_view: Box::new(sub_view.negate(index, view_type, solver)?)
                };
                let table_alias = TableAlias{base_table, index: 1};
                GroundingView::new(table_alias, free_variables, query, exclude, all_ids)
            },
            GroundingQuery::Union {..} => unreachable!()  // because negation is pushed down conjunctions and disjunctions
        }
    }

}


impl TableAlias {
    #[inline]
    pub(crate) fn new(base_table: TableName, index: usize) -> Self {
        TableAlias{base_table: base_table, index}
    }
}


impl Column {
    #[inline]
    pub(crate) fn new<T: Display + ? Sized>(table_alias: &TableAlias, column: &T) -> Self {
        Column{table_alias: table_alias.clone(), column: column.to_string()}
    }
}