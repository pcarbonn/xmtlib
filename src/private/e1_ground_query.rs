// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use itertools::Either;

use crate::api::{QualIdentifier, SortedVar, SpecConstant, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e2_ground_sql::SQLExpr;


////////////////////// Data structures for grounding views and queries ////////

/// the grounding view of a term
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum GroundingView {
    Empty,
    View {  // select vars, cond, grounding from view
        free_variables: IndexMap<Symbol, Option<TableName>>,  // None for infinite variables
        condition: bool,
        ground_view: Either<SQLExpr, TableName>, // Left for SpecConstant, Boolean; Right for view

        query: GroundingQuery,  // the underlying query
        ids: Ids,  // describes the groundings only.  Beware that the query may have conditions.
    },
}

/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GroundingQuery {
    Join {
        /// maps variables to None if its domain is infinite or to a Column in a Type or Interpretation table.
        variables: IndexMap<Symbol, Option<Column>>,
        conditions: Vec<SQLExpr>,  // vector of non-empty SQL expressions
        grounding: SQLExpr,
        natural_joins: IndexSet<NaturalJoin>,
        theta_joins: IndexSet<ThetaJoin>,
    },
    Aggregate {
        agg: String,  // "" (top-level), "and" or "or"
        free_variables: IndexMap<Symbol, Option<TableName>>,  // None for infinite variables
        infinite_variables: Vec<SortedVar>,
        sub_view: Box<GroundingView>,  // the sub_view has more variables than free_variables
        exclude: Option<bool>
    },
    Union {
        free_variables: IndexMap<Symbol, Option<TableName>>,  // None for infinite variables
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
pub(crate) type ThetaJoin = (TableName, Vec<(Ids, SQLExpr, Column)>);


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Column {
    table_name: TableName,
    column: String
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TableName {
    pub(crate) base_table: String,
    pub(crate) index: TermId, // to disambiguate
}


/// A flag indicating whether the values in an inetrpretation table are all Ids, some Ids, or all unknown.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Ids {
    All, // lowest
    Some,
    None // highest
}


///////////////////////////  Display //////////////////////////////////////////


// SQL of the view
impl std::fmt::Debug for GroundingView {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundingView::Empty => write!(f, "SELECT \"true\" AS G WHERE FALSE"),
            GroundingView::View { free_variables, condition, ground_view, .. } => {

                let vars = free_variables.iter()
                    .map(|(symbol, _)| symbol.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let vars = if vars == "" { vars } else { vars + ", " };
                let if_= if *condition { "if_, " } else { "" };
                let g_v = match ground_view {
                    Either::Left(c) => format!("{}", c.show(&IndexMap::new())),
                    Either::Right(view) => format!("G from {view}")
                };
                write!(f,"SELECT {vars}{if_}{g_v}")
            }
        }
    }
}


// SQL of the underlying select
impl std::fmt::Display for GroundingView {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundingView::Empty => write!(f, "SELECT \"true\" AS G WHERE FALSE"),
            GroundingView::View { query, .. } => write!(f, "{query}")
        }
    }
}

impl std::fmt::Display for GroundingQuery {

    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundingQuery::Join{variables, conditions, grounding,
                    natural_joins, theta_joins, ..} => {

                // SELECT {variables.0} AS {variables.1},
                //        {condition} AS if_,  -- if condition
                //        {grounding} AS G,
                //   FROM {natural joins}
                //   JOIN {theta_joins}

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
                    .map( |e| { e.show(&variables)})  // can be empty !
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
                let grounding_ = grounding.show(&variables);
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
                                        let this_column = Column{table_name: table_name.clone(), column: symbol.to_string()};
                                        let column = variables.get(symbol).unwrap();
                                        if let Some(column) = column {
                                            if this_column.to_string() != column.to_string() {
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
                            .filter_map( | (ids, e, col) | {
                                let value = e.show(&variables);
                                if col.to_string() == value {
                                    None
                                } else {
                                    match ids {
                                        Ids::All =>
                                            Some(format!("{value} = {col}")),
                                        Ids::Some =>
                                            Some(format!("(NOT(is_id({value})) OR {value} = {col})")),
                                        Ids::None =>
                                            if let SQLExpr::Variable(_) = e {
                                                if value != col.to_string() {
                                                    Some(format!("{value} = {col}"))
                                                } else { None}

                                            } else { None },
                                    }
                                }
                            }).collect::<Vec<_>>().join(" AND ");
                        let on = if on == "" { on } else { format!(" ON {on}")};

                        format!("{} AS {table_name}{on}", table_name.base_table)
                    }).collect::<Vec<_>>();

                // naturals + thetas + empty
                let tables = [naturals, thetas].concat();
                let tables =
                    if tables.len() == 0 {
                        "".to_string()
                    } else if tables.len() == 1 {
                        let mut tables = format!(" FROM {}", tables.join(" JOIN "));
                        if tables.contains(" ON ") {
                            // replace the only " ON " by " WHERE "
                            tables = tables.replace(" ON ", " WHERE ");
                        }
                        tables
                    } else {
                        format!(" FROM {}", tables.join(" JOIN "))
                    };

                write!(f, "SELECT {variables_}{condition}{grounding_}{tables}")
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

impl std::fmt::Display for Column {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}.{}", self.table_name, self.column)
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

impl std::fmt::Display for Ids {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Ids::All => write!(f, "Complete"),
            Ids::Some => write!(f, "Partial"),
            Ids::None => write!(f, "Unknown"),
        }
    }
}


/////////////////////  Grounding Query creation  //////////////////////////////


/// Creates a query for a constant
pub(crate) fn query_spec_constant(
    spec_constant: &SpecConstant,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {
    let query = GroundingQuery::Join {
        variables: IndexMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexSet::new(),
        theta_joins: IndexSet::new(),
    };
    let view = TableName{base_table: "ignore".to_string(), index: 0};
    create_view(view, IndexMap::new(), query, Ids::All, solver)
}


/// Creates a query for a variable
pub(crate) fn query_for_variable(
    symbol: &Symbol,
    base_table: &String,
    index: usize,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {
    let view = TableName{base_table: "variable".to_string(), index};
    if base_table.len() != 0 {
        let table_name = TableName{base_table: base_table.clone(), index};
        let column = Column{table_name: table_name.clone(), column: "G".to_string()};
        let variables= IndexMap::from([(symbol.clone(), Some(column.clone()))]);

        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::from([NaturalJoin::Variable(table_name.clone(), symbol.clone())]),
            theta_joins: IndexSet::new() };
        let free_variables = IndexMap::from([(symbol.clone(), Some(table_name))]);
        create_view(view, free_variables, query, Ids::All, solver)
    } else {  // infinite variable ==> just "x"
        let variables = IndexMap::from([(symbol.clone(), None)]);
        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::new(),
            theta_joins: IndexSet::new() };
        let free_variables = IndexMap::from([(symbol.clone(), None)]);
        create_view(view, free_variables, query, Ids::None, solver)
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum View {
    TU, UF, G,
}

/// describes the type of query to create for a compound term
pub(crate) enum Variant {
    Interpretation(TableName, Ids, View),
    Apply,
    Construct(View),
    PredefinedBoolean(View)
}

/// Creates a query for a compound term, according to `variant`.
pub(crate) fn query_for_compound(
    qual_identifier: &QualIdentifier,
    index: TermId,
    sub_queries: &mut Vec<GroundingView>,
    variant: &Variant,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    let mut free_variables = IndexMap::new();
    let mut variables: IndexMap<Symbol, Option<Column>> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins = IndexSet::new();
    let mut theta_joins = IndexSet::new();
    let mut thetas = vec![];
    let mut ids: Ids = Ids::All;

    for (i, sub_q) in sub_queries.iter_mut().enumerate() {

        match sub_q {
            GroundingView::Empty => {
                return Ok(GroundingView::Empty)
            },
            GroundingView::View {free_variables: sub_free_variables, condition: sub_condition,
                ground_view, query, ids: sub_ids,..} => {

                free_variables.append(sub_free_variables);
                ids = max(ids, sub_ids.clone());

                if let GroundingQuery::Join { variables: sub_variables, conditions: sub_conditions,
                    grounding: sub_grounding, natural_joins: sub_natural_joins,
                    theta_joins: sub_theta_joins, .. } = query {

                    // handle the special case of a query for a variable
                    match sub_grounding {
                        SQLExpr::Variable(symbol) => {
                            if let Variant::Interpretation(table_name, ..) = variant {
                                let column = Column{table_name: table_name.clone(), column: format!("a_{i}")};

                                //  update the query in progress
                                variables.insert(symbol.clone(), Some(column.clone()));
                                // sub-query has no conditions
                                groundings.push(sub_grounding.clone());
                                // do not push to natural_joins
                                thetas.push((sub_ids.clone(), sub_grounding.clone(), column));

                                continue  // to the next sub-query
                            }
                        },
                        _ => {}
                    };

                    conditions.append(sub_conditions);
                    groundings.push(sub_grounding.clone());
                    natural_joins.append(sub_natural_joins);
                    theta_joins.append(sub_theta_joins);

                    // merge the variables
                    for (symbol, column) in sub_variables.clone() {
                        if variables.get(&symbol).is_none() {
                            variables.insert(symbol.clone(), column.clone());
                        }
                    }

                    // compute the join conditions, for later use
                    match variant {
                        Variant::Interpretation(table_name, ..) => {
                            let column = Column{table_name: table_name.clone(), column: format!("a_{i}")};

                            // adds nothing if sub_ids = All
                            conditions.push(SQLExpr::Equality(sub_ids.clone(), Box::new(sub_grounding.clone()), column.clone()));
                            // adds nothing if sub_ids == None
                            thetas.push((sub_ids.clone(), sub_grounding.clone(), column));
                        },
                        Variant::Apply
                        | Variant::Construct(..)
                        | Variant::PredefinedBoolean(..) => {}
                    }
                } else {
                    match ground_view {
                        Either::Left(constant) =>
                            groundings.push(constant.clone()),

                        Either::Right(table_name) => {
                            if *sub_condition {
                                let sub_condition = SQLExpr::Value(Column{table_name: table_name.clone(), column: "if_".to_string()});
                                conditions.push(sub_condition);
                            }
                            groundings.push(SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()}));
                            let sub_natural_join = NaturalJoin::View(table_name.clone(), vec![]);
                            natural_joins.append(&mut IndexSet::from([sub_natural_join]));

                            // merge the variables
                            for (symbol, _) in sub_free_variables.clone() {
                                if variables.get(&symbol).is_none() {
                                    let column = Column{table_name: table_name.clone(), column: symbol.to_string()};
                                    variables.insert(symbol.clone(), Some(column));
                                }
                            }
                        },
                    }
                }
            }
        }
    };

    // remove natural_joins of types that are not used in variables
    let natural_joins = natural_joins.into_iter()
        .filter( |natural_join| {
            match natural_join {
                NaturalJoin::Variable(table_name, symbol) => {
                    let column = variables.get(symbol).unwrap();
                    if let Some(column) = column {
                        column.table_name == *table_name  // // otherwise, unused variable
                    } else {
                        unreachable!()  // infinite variable.
                    }
                },
                NaturalJoin::View(..) => {
                    true
                }
            }
        }).collect();

    let grounding =
        match variant {
            Variant::Interpretation(table_name, ids_, view) => {
                theta_joins.insert((table_name.clone(), thetas));
                ids = ids_.clone();  // reflects the grounding column, not if_
                match (ids_, view) {
                    (Ids::All, View::TU) => SQLExpr::Boolean(true),
                    (Ids::All, View::UF) => SQLExpr::Boolean(false),
                    _ => SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()})
                }
            },
            Variant::Apply => {
                ids = Ids::None;
                SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings))
            },
            Variant::Construct(view) => {
                // do not change ids.
                if *qual_identifier == solver.true_ {
                    match view {
                        View::TU => SQLExpr::Boolean(true),
                        View::UF => return Ok(GroundingView::Empty),
                        View::G => SQLExpr::Boolean(true),
                    }
                } else if *qual_identifier == solver.false_ {
                    match view {
                        View::TU => return Ok(GroundingView::Empty),
                        View::UF => SQLExpr::Boolean(false),
                        View::G => SQLExpr::Boolean(false),
                    }
                } else {  // non-boolean
                    SQLExpr::Construct(qual_identifier.clone(), Box::new(groundings))
                }
            },
            Variant::PredefinedBoolean(view) => {
                if ids == Ids::All {
                    match view {
                        View::TU => SQLExpr::Boolean(true),
                        View::UF => SQLExpr::Boolean(false),
                        View::G  => SQLExpr::Predefined(qual_identifier.clone(), Box::new(groundings)),
                    }
                } else {
                    SQLExpr::Predefined(qual_identifier.clone(), Box::new(groundings))
                }
            }
        };

    let table_name = TableName{base_table: qual_identifier.to_string().clone(), index};
    let query = GroundingQuery::Join {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
    };
    create_view(table_name, free_variables, query, ids, solver)
}


/// Creates a query over an aggregate view, possibly adding a where clause if exclude is not empty
pub(crate) fn query_for_aggregate(
    sub_query: &GroundingView,
    free_variables: &IndexMap<Symbol, Option<TableName>>,
    infinite_variables: &Vec<SortedVar>,  // variables being quantified
    agg: &str,  // "and", "or" or ""
    exclude: Option<bool>,
    table_name: TableName,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    match sub_query {
        GroundingView::Empty => {
            Ok(GroundingView::Empty)
        },
        GroundingView::View{query, ids,..} => {
            // if the query is an aggregate, try to have only one aggregate
            if let GroundingQuery::Aggregate {
                agg: sub_agg,
                infinite_variables: sub_infinite_variables,
                sub_view: sub_sub_view,
                exclude: sub_exclude , ..}
                = query {
                    if agg == sub_agg
                    && (sub_exclude.is_none() || exclude == *sub_exclude)  {
                        // it's possible to by pass the sub-aggregate
                        let mut infinite_variables = infinite_variables.clone();
                        infinite_variables.extend(sub_infinite_variables.iter().cloned());

                        let query = GroundingQuery::Aggregate {
                            agg: agg.to_string(),
                            free_variables: free_variables.clone(),
                            infinite_variables: infinite_variables.clone(),
                            sub_view: Box::new(*sub_sub_view.clone()),
                            exclude,
                        };
                        return create_view(table_name, free_variables.clone(), query, ids.clone(), solver)
                    }
            }

            let query = GroundingQuery::Aggregate {
                agg: agg.to_string(),
                free_variables: free_variables.clone(),
                infinite_variables: infinite_variables.clone(),
                sub_view: Box::new(sub_query.clone()),
                exclude,
            };

            create_view(table_name, free_variables.clone(), query, ids.clone(), solver)
        }
    }
}


pub(crate) fn query_for_union(
    sub_views: Vec<GroundingView>,
    agg: String,
    index: TermId,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    // determine variables, condition and ids
    let mut free_variables = IndexMap::new();
    let mut condition = false;
    let mut ids = Ids::All;
    for sub_view in sub_views.clone() {
        if let GroundingView::View { free_variables: sub_free_variables,
            condition: sub_condition, ids: sub_ids, .. } = sub_view {

            free_variables.append(&mut sub_free_variables.clone());
            condition |= sub_condition;
            ids = max(ids, sub_ids);
        }
    }

    // build the sub-queries
    let sub_queries = sub_views.iter()
        .filter_map( |sub_view| {
            if let GroundingView::View { free_variables: sub_free_variables, condition: sub_condition,
                ground_view, ..} = sub_view {

                match ground_view {
                    Either::Right(table_name) => {
                        let mut q_variables = IndexMap::new();
                        let natural_join = NaturalJoin::View(table_name.clone(), sub_free_variables.keys().cloned().collect());
                        let mut natural_joins = IndexSet::from([natural_join]);
                        for (symbol, sub_table_name) in free_variables.iter() {
                            if let Some(_) = sub_free_variables.get(symbol) {  // the variable is in the sub_view
                                let column = Column{table_name: table_name.clone(), column: symbol.to_string()};
                                q_variables.insert(symbol.clone(), Some(column));
                            } else if let Some(table_name) = sub_table_name {  // create cross-product
                                let column = Column{table_name: table_name.clone(), column: symbol.to_string()};
                                q_variables.insert(symbol.clone(), Some(column));
                                let natural_join = NaturalJoin::Variable(table_name.clone(), symbol.clone());
                                natural_joins.insert(natural_join);
                            } else {  // infinite variable
                                q_variables.insert(symbol.clone(), None);
                            }
                        }

                        let conditions =
                            if *sub_condition {
                                vec![SQLExpr::Value(Column{table_name: table_name.clone(), column: "if_".to_string()})]
                            } else if condition {
                                vec![SQLExpr::Boolean(true)]
                            } else { vec![] };

                        Some(GroundingQuery::Join {
                            variables: q_variables,
                            conditions,
                            grounding: SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()}),
                            natural_joins,
                            theta_joins: IndexSet::new()
                        })
                    },
                    Either::Left(grounding) => {
                        let q_variables = free_variables.iter()
                            .map( |(symbol, _)| (symbol.clone(), None))
                            .collect();
                        Some(GroundingQuery::Join {
                            variables: q_variables,
                            conditions: vec![],
                            grounding: grounding.clone(),
                            natural_joins: IndexSet::new(),
                            theta_joins: IndexSet::new()
                        })
                    }
                }
            } else { // empty view
                None
             }
        }).collect::<Vec<_>>();

    if sub_queries.len() == 0 { return Ok(GroundingView::Empty) }

    let table_name = TableName{base_table: format!("union_{index}"), index: 0};
    if sub_queries.len() == 1 {
        return create_view(table_name, free_variables, sub_queries.first().unwrap().clone(), ids.clone(), solver)
    };

    // create the union
    let query = GroundingQuery::Union{ free_variables: free_variables.clone(), sub_queries: Box::new(sub_queries) };

    let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS {query}");
    solver.conn.execute(&sql, ())?;

    // create the sub_view
    let sub_view = GroundingView::View {
        free_variables: free_variables.clone(),
        condition: condition,
        ground_view: Either::Right(table_name),
        query,
        ids: ids.clone()
    };

    // create the aggregate
    let table_name = TableName{base_table: format!("agg_union_{index}"), index: 0};
    let query = GroundingQuery::Aggregate {
        agg: agg.to_string(),
        free_variables: free_variables.clone(),
        infinite_variables: vec![],
        sub_view: Box::new(sub_view),
        exclude: None,
    };

    create_view(table_name, free_variables, query, ids.clone(), solver)
}


/////////////////////  Grounding Query utilities  //////////////////////////////


pub(crate) fn create_view (
    table_name: TableName,
    free_variables: IndexMap<Symbol, Option<TableName>>,
    query: GroundingQuery,
    ids: Ids,
    solver: &mut Solver,
) -> Result<GroundingView, SolverError> {
    match query {
        GroundingQuery::Join{ref conditions, ref grounding, ref natural_joins, ref theta_joins, ..} => {

            if natural_joins.len() + theta_joins.len() == 0 {// no need to create a view in DB
                Ok(GroundingView::View {
                    free_variables,
                    condition: false,
                    ground_view: Either::Left(grounding.clone()),
                    query,
                    ids
                })
            } else {
                let condition = conditions.len() > 0;

                // create the view in the database
                let vars = free_variables.iter()
                    .map(|(symbol, _)| symbol.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let vars = if vars == "" { vars } else { vars + ", " };
                let if_= if condition { "if_, " } else { "" };
                let grounding = "G".to_string();
                let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS SELECT {vars}{if_}{grounding} FROM ({query})");
                solver.conn.execute(&sql, ())?;

                Ok(GroundingView::View{
                    free_variables,
                    condition,
                    ground_view: Either::Right(table_name),
                    query,
                    ids})
            }
        },
        GroundingQuery::Aggregate { .. } => {

            let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS {query}");
            solver.conn.execute(&sql, ())?;

           Ok(GroundingView::View {
                free_variables,
                condition: false,
                ground_view: Either::Right(table_name),
                query,
                ids: Ids::None
            })
        },
        GroundingQuery::Union { ref sub_queries, .. } => {

            let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS {query}");
            solver.conn.execute(&sql, ())?;

            Ok(GroundingView::View {
                free_variables,
                condition: sub_queries.iter().any( |view| {
                    if let GroundingQuery::Join{conditions, ..} = view {
                        0 < conditions.len()
                    } else {
                        false
                    }
                }),
                ground_view: Either::Right(table_name),
                query,
                ids
            })

        }
    }
}


impl GroundingView {

    /// return the view's variables with their infinity flag
    pub(crate) fn get_free_variables(&self) -> IndexMap<Symbol, Option<TableName>> {
        match self {
            GroundingView::Empty => IndexMap::new(),
            GroundingView::View{free_variables,..} => free_variables.clone()
        }
    }

    pub(crate) fn get_ids(&self) -> Ids {
        match self {
            GroundingView::Empty => Ids::All,
            GroundingView::View{ids, ..} => ids.clone()
        }
    }

    pub(crate) fn negate(
        &self,
        qual_identifier: &QualIdentifier,  // not
        ground_view: &Either<SQLExpr, TableName>,
        index: TermId,
        view: View,
        solver: &mut Solver
    ) -> Result<GroundingView, SolverError> {
        match self {
            GroundingView::Empty => Ok(self.clone()),
            GroundingView::View{free_variables, query, ids, ..} =>
                query.negate(qual_identifier, ground_view, free_variables.clone(), index, view, ids, solver)
        }
    }
}

impl GroundingQuery {

    pub(crate) fn negate(
        &self,
        qual_identifier: &QualIdentifier,  // not
        ground_view: &Either<SQLExpr, TableName>,
        free_variables: IndexMap<Symbol, Option<TableName>>,
        index: TermId,
        view: View,
        ids: &Ids,
        solver: &mut Solver
    ) -> Result<GroundingView, SolverError> {
        match self {
            GroundingQuery::Join { variables, conditions, grounding,
                        natural_joins, theta_joins, ..} => {

                        let new_grounding =
                            if *ids == Ids::All {
                                if view == View::TU {
                                    SQLExpr::Boolean(false)  // all ids were true
                                } else if view == View::UF {
                                    SQLExpr::Boolean(true)  // all ids were false
                                } else {
                                    SQLExpr::Predefined(qual_identifier.clone(), Box::new(vec![grounding.clone()]))
                                }
                            } else {
                                SQLExpr::Predefined(qual_identifier.clone(), Box::new(vec![grounding.clone()]))
                            };
                        let query = GroundingQuery::Join {
                            variables: variables.clone(),
                            conditions: conditions.clone(),
                            grounding: new_grounding,
                            natural_joins: natural_joins.clone(),
                            theta_joins: theta_joins.clone()};
                        let table_name = TableName{base_table: format!("negate_{index}"), index: 0};
                        create_view(table_name, free_variables, query, ids.clone(), solver)
                    }
            GroundingQuery::Aggregate { agg, infinite_variables, sub_view, exclude, .. } => {
                let query = GroundingQuery::Aggregate {
                    agg : if agg == "or" { "and".to_string() } else { "or".to_string() },
                    free_variables: free_variables.clone(),
                    infinite_variables: infinite_variables.clone(),
                    sub_view: Box::new(sub_view.negate(qual_identifier, ground_view, index, view, solver)?),
                    exclude: if let Some(bool) = exclude { Some(! bool) } else { *exclude }
                };
                let table_name = TableName{base_table: format!("negate_{index}"), index: 0};
                create_view(table_name, free_variables, query, ids.clone(), solver)
            },
            GroundingQuery::Union {..} => unreachable!()
        }
    }

}