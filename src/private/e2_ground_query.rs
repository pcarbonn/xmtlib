// Copyright Pierre Carbonnelle, 2025.

use indexmap::{IndexMap, IndexSet};
use itertools::Either::{self, Left, Right};
use std::cmp::max;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

use crate::ast::{L, Identifier, SortedVar, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e1_ground_view::{GroundingView, Ids, ViewType};
use crate::private::e3_ground_sql::{Mapping, Rho, SQLExpr, Predefined};
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
        outer: Option<bool>,  // the default boolean value for outer joins (None for inner join)
        natural_joins: IndexSet<NaturalJoin>,  // cross-products with sort, or joins with grounding sub-queries
        theta_joins: IndexMap<TableAlias, Vec<Option<Mapping>>>,  // joins with interpretation tables
        wheres: Vec<Rho>,  // set of equality conditions

        has_g_complexity: bool,  // LINK src/doc.md#_has_g_complexity
    },
    Aggregate {
        agg: String,  // "" (top-level), "and" or "or"
        free_variables: OptionMap<Symbol, TableAlias>,  // None for infinite variables
        infinite_variables: Vec<SortedVar>,
        default: Option<bool>,  // to generate Y cross-product
        sub_view: Box<GroundingView>,  // the sub_view has more variables than free_variables

        has_g_complexity: bool,  // LINK src/doc.md#_has_g_complexity
    },
    Union {
        sub_queries: Box<Vec<GroundingQuery>>,  // the sub-queries are Join and have the same columns

        has_g_complexity: bool,  // LINK src/doc.md#_has_g_complexity
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
        write!(f, "{}", self.to_sql(&IndexMap::new(), "").0)
    }
}


impl GroundingQuery {
    /// # Arguments:
    ///
    /// * var_joins: maps variable symbols to the column interpreting the variable;
    /// the usize is the arity of the function interpreted by the table having the column.
    ///
    pub(crate) fn to_sql(
        &self,
        var_joins: &IndexMap<Symbol, (Column, usize)>,
        indent: &str
    ) -> (String, Ids) {

        let indent1 = format!("{indent}{INDENT} ").to_string();
        match self {
            GroundingQuery::Join{variables, conditions, grounding, outer,
            natural_joins, theta_joins, wheres, ..} => {

                // SELECT {variables.0} AS {variables.1},
                //        {condition} AS if_,  -- if condition
                //        {grounding} AS G,
                //   FROM {natural joins}
                //   JOIN {theta_joins}
                //  WHERE {where_}

                // update variables and theta_joins with var_joins
                // example: var_joins = {x: (f.a_1, 3), y:(f.a_3, 3)} where arity of f is 3
                // LINK src/doc.md#_Variables
                let mut variables = variables.clone();
                let mut new_theta_joins: IndexMap<_, Vec<_>> = IndexMap::new();
                for (symbol, (column, arity)) in var_joins.iter() {
                    if let Some(None) = variables.get(symbol) {  // was infinite; must now add the theta join

                        // add "f.a_1 AS x", "f.a_3 AS y" to SELECT
                        variables.insert(symbol.clone(), Some(column.clone()));

                        let Column{table_alias, column: column_name} = column;
                        let mapping = Mapping(SQLExpr::Variable(symbol.clone()), column.clone());  // x->f.a_1, y-> f.a_3
                        let index = column_name[2..].parse::<usize>().unwrap()-1;  // 0, 2

                        let mut mappings = match new_theta_joins.get(table_alias) {
                            None => vec![None; *arity],
                            Some(mappings) => mappings.clone()
                        };
                        mappings[index] = Some(mapping);
                        // at the end, new_thetas is : f -> [Some(x, f.a_1), None, Some(y, f.a_3)]
                        new_theta_joins.insert(table_alias.clone(), mappings);
                    }
                };
                let variables = &variables;
                let mut theta_joins = theta_joins.clone();
                theta_joins.append(&mut new_theta_joins);
                let theta_joins = &theta_joins;

                // add DISTINCT if a mapping is partial
                let distinct = theta_joins.iter()
                    .any( |(_, mappings)|
                        mappings.iter()
                        .any(|mapping| mapping.is_none())
                );
                let distinct = if distinct { " DISTINCT " } else { "" };

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
                let (grounding_, mut ids) = grounding.to_sql(&variables);
                let grounding_ = format!("{grounding_} AS G");

                // wheres
                let mut where_ = wheres.iter()
                    .map(|rho| rho.to_sql(variables))
                    .collect::<Vec<_>>();

                // natural joins
                let join = if outer.is_some() { "FULL JOIN" } else { "JOIN" };
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

                                // add the variable to var_joins if it is part of a theta join
                                // example: theta_joins[f] = [Some(x, f.a_1), .., Some(y, f.a_3)]
                                // LINK src/doc.md#_Variables
                                let mut var_joins = var_joins.clone();
                                for (symbol, col) in variables.iter() {  // (x, Some(f.a_1)), (y, Some(f.a_3))
                                    if let Some(col) = col {
                                        let Column{table_alias, column: _} = col;
                                        if let Some(mappings) = theta_joins.get(table_alias) {
                                            // the variable is an argument to an interpreted symbol
                                            var_joins.insert(symbol.clone(), (col.clone(), mappings.len()));
                                        }
                                    }
                                }  // var_joins is {x: (f.a_1, 3), y:(f.a_3, 3)}

                                let (query, ids_) = query.to_sql(&var_joins, &indent1);
                                ids = max(ids.clone(), ids_);

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
                                    }).collect::<Vec<_>>().join(format!(" \n{indent1}AND ").as_str());

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
                    .join(format!("\n{indent}  {join} ").as_str());

                // theta joins
                let thetas = theta_joins.iter().enumerate()
                    .map( | (i, (table_name, mapping)) | {
                        let on = mapping.iter()
                            .filter_map( | expr |
                                if let Some(expr) = expr {
                                    expr.to_join(variables)
                                } else { None })
                            .collect::<Vec<_>>().join(format!(" \n{indent}{INDENT}AND ").as_str());
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
                        format!("\n{indent} WHERE {}", where_.join(format!(" \n{indent}{INDENT}AND ").as_str()))
                    };


                // naturals + thetas + empty
                let tables = if 0 < naturals.len() + thetas.len() {
                        format!("\n{indent}  FROM {naturals}{thetas}{where_}")
                    } else {
                        "".to_string()  // no benefits gained by adding where_ clause
                    };

                let comment = format!("-- Join({})\n{indent}", indent.len());
               (format!("{comment}SELECT {distinct}{variables_}{condition}{grounding_}{tables}"),
                ids)
            }
            GroundingQuery::Aggregate { agg, free_variables, infinite_variables, sub_view, default, .. } => {
                if let GroundingView::View { free_variables: ref sub_free_variables, condition, ..} = **sub_view {
                    // SELECT {free_variables},
                    //        "(forall ({infinite_vars}) " || and_aggregate(implies_(if_, G)) || ")" AS G
                    //   FROM (SELECT {free_variables}, {default} as G
                    //         UNION ALL {sub_view})
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

                    // handle variable shadowing
                    // LINK src/doc.md#_Variables
                    let mut var_joins = var_joins.clone();
                    for SortedVar(symbol, _) in infinite_variables.iter() {
                        var_joins.shift_remove(symbol);
                    }

                    let (sub_view, mut ids) = sub_view.to_sql(&var_joins, format!("{indent}{INDENT}").as_str());
                    let default = match default {
                        None => "".to_string(),
                        Some(default) => {
                            // SELECT {sub_free_variables*}, "true" AS if_, {default} AS G from {cross-product} UNION ALL
                            let mut subs = vec![];
                            let mut joins = vec! [];
                            let mut cancel = false;
                            for (symb, _) in sub_free_variables.iter() {
                                match free_variables.get(symb){
                                    None => subs.push(format!("NULL AS {symb}")),
                                    Some(Some(table_alias)) => {
                                        subs.push(format!("{table_alias}.G AS {symb}"));
                                        joins.push(format!("{} AS {table_alias}", table_alias.base_table))
                                    },
                                    Some(None) => {  // TODO infinite variable => cancel
                                        cancel = true;
                                    }
                                }
                            };
                            if cancel {
                                "".to_string ()
                            } else {
                                if ids == Ids::None {
                                    ids = Ids::Some  // because of default
                                }
                                let subs = if subs.len() == 0 { "".to_string() }
                                    else { format!("{}, ", subs.join(", ")) };
                                let joins = if joins.len() == 0 { "".to_string() }
                                    else { format!("FROM {} ", joins.join(" JOIN "))};
                                let if_ = if condition { "\"true\" AS if_, "}
                                    else { "" }.to_string();

                                format!("SELECT {subs}{if_}\"{default}\" AS G {joins}\n{indent}{INDENT}UNION ALL\n{indent}{INDENT}")
                            }
                        }
                    };

                    let comment = format!("-- Agg ({})\n{indent}", indent.len());
                    (format!("{comment}SELECT {free}{grounding} as G\n{indent} FROM ({default}{sub_view}){group_by}"),
                     ids)
                } else {  // empty view
                    ("{}".to_string(), Ids::All)
                }
            },
            GroundingQuery::Union { sub_queries, .. } => {
                let mut has_all = false;
                let mut has_some = false;
                let mut has_none = false;
                let view = sub_queries.iter()
                    .map( |query| {
                        let (sql, ids_) = query.to_sql(var_joins, indent);
                        has_all  |= ids_ == Ids::All;
                        has_some |= ids_ == Ids::Some;
                        has_none |= ids_ == Ids::None;
                        sql
                    }).collect::<Vec<_>>().join(format!("\n{indent}UNION ALL\n{indent}").as_str());
                let ids = if has_some { Ids::Some}
                    else if has_all && has_none { Ids:: Some }
                    else if has_all { Ids::All }
                    else { Ids::None };
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
    pub(crate) fn has_g_complexity(&self) -> bool {
        match self {
            GroundingQuery::Join{ has_g_complexity, ..}
            | GroundingQuery::Union { has_g_complexity, ..}
            | GroundingQuery::Aggregate { has_g_complexity, ..} =>
                *has_g_complexity,
        }
    }


    /// Finalize the negation of a query.
    /// Assumes that the the change from TU to UF (or vice-versa) has been done
    /// but massage it to remain correct.
    pub(crate) fn negate(
        &self,
        free_variables: OptionMap<Symbol, TableAlias>,
        index: TermId,
        view_type: ViewType,
        exclude: Option<bool>,
        ids: Ids,
        to_be_defined: IndexSet<L<Identifier>>,
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
            outer, natural_joins, theta_joins, wheres, has_g_complexity} => {

                let new_grounding =
                    match grounding {
                        SQLExpr::Boolean(true) => SQLExpr::Boolean(false),
                        SQLExpr::Boolean(false) => SQLExpr::Boolean(true),
                        _ => SQLExpr::Predefined(Predefined::Not, Box::new(vec![grounding.clone()]))
                    };
                let wheres = wheres.iter()
                    .map(|Rho{t0, op, t1}| {
                        let op = match op.as_str() {
                            "=" => "!=".to_string(),
                            "!=" => "=".to_string(),
                            _ => return Err(SolverError::InternalError(58785596))
                        };
                        Ok(Rho{t0: t0.clone(), op, t1: t1.clone()})
                    }).collect::<Result<Vec<_>,_>>()?;
                let query = GroundingQuery::Join {
                    variables: variables.clone(),
                    conditions: conditions.clone(),
                    grounding: new_grounding,
                    outer: *outer,
                    natural_joins: natural_joins.clone(),
                    theta_joins: theta_joins.clone(),
                    wheres,
                    has_g_complexity: *has_g_complexity
                };
                let table_alias = TableAlias{base_table, index: 0};
                GroundingView::new(table_alias, free_variables, query, exclude, ids, to_be_defined)
            }
            GroundingQuery::Aggregate { agg, infinite_variables, sub_view, default, has_g_complexity, .. } => {
                let default = match default {
                    Some(default) => Some(! default),
                    None => None,
                };
                let query = GroundingQuery::Aggregate {
                    agg : (if agg == "or" { "and" } else { "or" }).to_string(),
                    free_variables: free_variables.clone(),
                    infinite_variables: infinite_variables.clone(),
                    default,
                    sub_view: Box::new(sub_view.negate(index, view_type, solver)?),
                    has_g_complexity: *has_g_complexity
                };
                let table_alias = TableAlias{base_table, index: 1};
                GroundingView::new(table_alias, free_variables, query, exclude, ids, to_be_defined)
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