// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use itertools::Either;

use crate::api::{QualIdentifier, SortedVar, SpecConstant, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e2_ground_query::{GroundingQuery, NaturalJoin, TableName, Column};
use crate::private::e3_ground_sql::{SQLExpr, Predefined};


////////////////////// Data structures for grounding views ////////////////////


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
                    Either::Left(c) => format!("{}", c.show(&IndexMap::new(), false)),
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
pub(crate) fn query_for_constant(
    spec_constant: &SpecConstant,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {
    let query = GroundingQuery::Join {
        variables: IndexMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexSet::new(),
        theta_joins: IndexSet::new(),
        where_: vec![]
    };
    let view = TableName::new("ignore", 0);
    GroundingView::new(view, IndexMap::new(), query, Ids::All, solver)
}


/// Creates a query for a variable
pub(crate) fn query_for_variable(
    symbol: &Symbol,
    base_table: &String,
    index: usize,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {
    let view = TableName::new("variable", index);
    if base_table.len() != 0 {
        let table_name = TableName::new(base_table, index);
        let column = Column::new(&table_name, "G");
        let variables= IndexMap::from([(symbol.clone(), Some(column.clone()))]);

        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::from([NaturalJoin::Variable(table_name.clone(), symbol.clone())]),
            theta_joins: IndexSet::new(),
            where_: vec![] };
        let free_variables = IndexMap::from([(symbol.clone(), Some(table_name))]);
        GroundingView::new(view, free_variables, query, Ids::All, solver)
    } else {  // infinite variable ==> just "x"
        let variables = IndexMap::from([(symbol.clone(), None)]);
        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::new(),
            theta_joins: IndexSet::new(),
            where_: vec![] };
        let free_variables = IndexMap::from([(symbol.clone(), None)]);
        GroundingView::new(view, free_variables, query, Ids::None, solver)
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum View {
    TU, UF, G,
}

/// describes the type of query to create for a compound term
pub(crate) enum QueryVariant {
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
    variant: &QueryVariant,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    let mut free_variables = IndexMap::new();
    let mut variables: IndexMap<Symbol, Option<Column>> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins = IndexSet::new();
    let mut theta_joins = IndexSet::new();
    let mut thetas = vec![];
    let mut where_ = vec![];
    let mut ids: Ids = Ids::All;
    let mut ids_ = vec![];

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
                    theta_joins: sub_theta_joins, where_: sub_where_,.. } = query {

                    // handle the special case of a variable used as an argument to an interpreted function
                    match sub_grounding {
                        SQLExpr::Variable(symbol) => {
                            if let QueryVariant::Interpretation(table_name, ..) = variant {
                                let column = Column::new(table_name, &format!("a_{i}"));

                                //  update the query in progress
                                variables.insert(symbol.clone(), Some(column.clone()));
                                // sub-query has no conditions
                                groundings.push(sub_grounding.clone());
                                // do not push to natural_joins
                                let if_ = SQLExpr::Mapping(sub_ids.clone(), Box::new(sub_grounding.clone()), column);
                                thetas.push(if_);

                                continue  // to the next sub-query
                            }
                        },
                        _ => {}
                    };

                    conditions.append(sub_conditions);
                    groundings.push(sub_grounding.clone());
                    ids_.push(sub_ids.clone());
                    natural_joins.append(sub_natural_joins);
                    theta_joins.append(sub_theta_joins);
                    where_.append(sub_where_);

                    // merge the variables
                    for (symbol, column) in sub_variables.clone() {
                        if variables.get(&symbol).is_none() {
                            variables.insert(symbol.clone(), column.clone());
                        }
                    }

                    // compute the join conditions, for later use
                    match variant {
                        QueryVariant::Interpretation(table_name, ..) => {
                            let column = Column::new(table_name, &format!("a_{i}"));

                            let if_ = SQLExpr::Mapping(sub_ids.clone(), Box::new(sub_grounding.clone()), column.clone());
                            // adds nothing if sub_ids = All
                            conditions.push(if_.clone());
                            // adds nothing if sub_ids == None
                            thetas.push(if_);
                        },
                        QueryVariant::Apply
                        | QueryVariant::Construct(..)
                        | QueryVariant::PredefinedBoolean(..) => {}
                    }
                } else {  // not a Join --> use the View
                    match ground_view {
                        Either::Left(constant) =>
                            groundings.push(constant.clone()),

                        Either::Right(table_name) => {

                            // merge the variables
                            for (symbol, _) in sub_free_variables.clone() {
                                if variables.get(&symbol).is_none() {
                                    let column = Column::new(table_name, &symbol);
                                    variables.insert(symbol.clone(), Some(column));
                                }
                            }

                            if *sub_condition {
                                let sub_condition = SQLExpr::Value(Column::new(table_name,"if_"));
                                conditions.push(sub_condition);
                            }
                            groundings.push(SQLExpr::Value(Column::new(table_name, "G")));

                            let map_variables = sub_free_variables.iter()
                                .filter_map( |(symbol, table_name)| {
                                    if table_name.is_some() {
                                        Some(symbol.clone())
                                    } else {
                                        None
                                    }
                                }).collect();
                            let sub_natural_join = NaturalJoin::View(table_name.clone(), map_variables);
                            natural_joins.append(&mut IndexSet::from([sub_natural_join]));
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
            QueryVariant::Interpretation(table_name, ids_, view) => {
                theta_joins.insert((table_name.clone(), thetas));
                ids = ids_.clone();  // reflects the grounding column, not if_
                match (ids_, view) {
                    (Ids::All, View::TU) => SQLExpr::Boolean(true),
                    (Ids::All, View::UF) => SQLExpr::Boolean(false),
                    _ => SQLExpr::Value(Column::new(table_name, "G"))
                }
            },
            QueryVariant::Apply => {
                ids = Ids::None;
                SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings))
            },
            QueryVariant::Construct(view) => {
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
            QueryVariant::PredefinedBoolean(view) => {
                // LINK src/doc.md#_Equality
                let function = match qual_identifier.to_string().as_str() {
                    "and" => Predefined::And,
                    "or"  => Predefined::Or,
                    "implies" => Predefined::Implies,
                    "not" => Predefined::Not,
                    "=" => Predefined::Eq,
                    _ => panic!()
                };

                let ops: Vec<_> = ids_.iter().cloned().zip(groundings.iter().cloned()).collect();
                match function {
                    Predefined::Eq => where_.push(SQLExpr::Chainable("=".to_string(), Box::new(ops.clone()), view.clone())),
                    _ => {}
                };

                if ids == Ids::All {
                    match view {
                        View::TU => SQLExpr::Boolean(true),
                        View::UF => SQLExpr::Boolean(false),
                        View::G  => SQLExpr::Predefined(function, Box::new(ops)),
                    }
                } else {
                    SQLExpr::Predefined(function, Box::new(ops))
                }
            }
        };

    let table_name = TableName::new(qual_identifier, index);
    let query = GroundingQuery::Join {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        where_
    };
    GroundingView::new(table_name, free_variables, query, ids, solver)
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
                        return GroundingView::new(table_name, free_variables.clone(), query, ids.clone(), solver)
                    }
            }

            let query = GroundingQuery::Aggregate {
                agg: agg.to_string(),
                free_variables: free_variables.clone(),
                infinite_variables: infinite_variables.clone(),
                sub_view: Box::new(sub_query.clone()),
                exclude,
            };

            GroundingView::new(table_name, free_variables.clone(), query, ids.clone(), solver)
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
                    Either::Left(grounding) => {
                        let q_variables = free_variables.iter()
                            .map( |(symbol, _)| (symbol.clone(), None))
                            .collect();
                        Some(GroundingQuery::Join {
                            variables: q_variables,
                            conditions: vec![],
                            grounding: grounding.clone(),
                            natural_joins: IndexSet::new(),
                            theta_joins: IndexSet::new(),
                            where_: vec![]
                        })
                    },
                    Either::Right(table_name) => {
                        let mut q_variables = IndexMap::new();
                        let join_vars = sub_free_variables.iter()
                            .filter_map( |(symbol, table_name)| {
                                if table_name.is_some() {
                                    Some(symbol.clone())
                                } else {
                                    None
                                }
                            }).collect();
                        let natural_join = NaturalJoin::View(table_name.clone(), join_vars);
                        let mut natural_joins = IndexSet::from([natural_join]);
                        for (symbol, sub_table_name) in free_variables.iter() {
                            if let Some(_) = sub_free_variables.get(symbol) {  // the variable is in the sub_view
                                let column = Column::new(table_name, symbol);
                                q_variables.insert(symbol.clone(), Some(column));
                            } else if let Some(table_name) = sub_table_name {  // create cross-product
                                let column = Column::new(table_name, symbol);
                                q_variables.insert(symbol.clone(), Some(column));
                                let natural_join = NaturalJoin::Variable(table_name.clone(), symbol.clone());
                                natural_joins.insert(natural_join);
                            } else {  // infinite variable
                                q_variables.insert(symbol.clone(), None);
                            }
                        }

                        let conditions =
                            if *sub_condition {
                                vec![SQLExpr::Value(Column::new(table_name, "if_"))]
                            } else if condition {
                                vec![SQLExpr::Boolean(true)]
                            } else { vec![] };

                        Some(GroundingQuery::Join {
                            variables: q_variables,
                            conditions,
                            grounding: SQLExpr::Value(Column::new(table_name, "G")),
                            natural_joins,
                            theta_joins: IndexSet::new(),
                            where_: vec![]
                        })
                    },
                }
            } else { // empty view
                None
             }
        }).collect::<Vec<_>>();

    if sub_queries.len() == 0 { return Ok(GroundingView::Empty) }

    let table_name = TableName{base_table: format!("union_{index}"), index: 0};
    if sub_queries.len() == 1 {
        return GroundingView::new(table_name, free_variables, sub_queries.first().unwrap().clone(), ids.clone(), solver)
    };

    // create the union
    let query = GroundingQuery::Union{ sub_queries: Box::new(sub_queries) };

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

    GroundingView::new(table_name, free_variables, query, ids.clone(), solver)
}


/////////////////////  Grounding View utilities  //////////////////////////////


impl GroundingView {

    pub(crate) fn new (
        table_name: TableName,
        free_variables: IndexMap<Symbol, Option<TableName>>,
        query: GroundingQuery,
        ids: Ids,
        solver: &mut Solver,
    ) -> Result<GroundingView, SolverError> {

        match query {

            GroundingQuery::Join{ref conditions, ref grounding,
            ref natural_joins, ref theta_joins, ..} => {

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
        index: TermId,
        view: View,
        solver: &mut Solver
    ) -> Result<GroundingView, SolverError> {
        match self {
            GroundingView::Empty => Ok(self.clone()),
            GroundingView::View{free_variables, query, ids, ..} =>
                query.negate(free_variables.clone(), index, view, ids, solver)
        }
    }
}
