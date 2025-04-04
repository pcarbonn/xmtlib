// Copyright Pierre Carbonnelle, 2025.

use regex::Regex;
use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use itertools::Either::{self, Left, Right};

use crate::api::{QualIdentifier, SortedVar, SpecConstant, Symbol, Term};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e2_ground_query::{GroundingQuery, NaturalJoin, TableName, Column};
use crate::private::e3_ground_sql::{Mapping, SQLExpr, Predefined};


////////////////////// Data structures for grounding views ////////////////////


/// the grounding view of a term
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum GroundingView {
    Empty,
    View {  // SELECT vars, cond, grounding (from view) WHERE val <> exclude
        free_variables: IndexMap<Symbol, Option<TableName>>,  // None for infinite variables, sort interpretation table otherwise
        condition: bool,
        grounding: Either<SQLExpr, TableName>, // Left for SpecConstant, Boolean without table. Right for grounding field in table.
        exclude: Option<bool>, // e.g., "false" in TU view

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
            GroundingView::View { free_variables, condition, grounding, exclude, .. } => {

                let vars = free_variables.iter()
                    .map(|(symbol, _)| symbol.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let vars = if vars == "" { vars } else { vars + ", " };
                let if_= if *condition { "if_, " } else { "" };
                let g_v = match grounding {
                    Either::Left(c) => format!("{}", c.to_sql(&IndexMap::new())),
                    Either::Right(view) => format!("G from {view}")
                };
                // make the view precise if the query is not
                // todo perf: is this usefull ?
                let where_ = match exclude {
                    Some(true) => format!("WHERE {g_v} <> \"true\""),
                    Some(false) => format!("WHERE {g_v} <> \"false\""),
                    None => "".to_string(),
                };

                write!(f,"SELECT {vars}{if_}{g_v}{where_}")
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
        precise: true
    };
    let view = TableName::new("ignore", 0);
    GroundingView::new(view, IndexMap::new(), query, None, Ids::All, solver)
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
            precise: false  // imprecise for boolean variable !
        };
        let free_variables = IndexMap::from([(symbol.clone(), Some(table_name))]);
        GroundingView::new(view, free_variables, query, None, Ids::All, solver) // todo perf: exclude for boolean
    } else {  // infinite variable ==> just "x"
        let variables = IndexMap::from([(symbol.clone(), None)]);
        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::new(),
            theta_joins: IndexSet::new(),
            precise: true  // cannot be boolean
        };
        let free_variables = IndexMap::from([(symbol.clone(), None)]);
        GroundingView::new(view, free_variables, query, None, Ids::None, solver)
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ViewType {
    TU, UF, G,
}

/// describes the type of query to create for a compound term
pub(crate) enum QueryVariant {
    Interpretation(TableName, Ids, Option<Option<Term>>),  // None if complete, Some(None) if `else` value is `unknonw`, or Some(Some(value))
    Apply,
    Construct,
    Predefined
}

/// Creates a query for a compound term, according to `variant`.
pub(crate) fn query_for_compound(
    qual_identifier: &QualIdentifier,
    index: TermId,
    sub_queries: &Vec<GroundingView>,
    variant: &QueryVariant,
    exclude: Option<bool>,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    let mut free_variables = IndexMap::new();
    let mut variables: IndexMap<Symbol, Option<Column>> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins = IndexSet::new();
    let mut theta_joins = IndexSet::new();
    let mut thetas = vec![];
    let mut ids = Ids::All;
    let mut ids_ = vec![];
    let mut precise = true;

    for (i, sub_q) in sub_queries.iter().enumerate() {

        match sub_q {
            GroundingView::Empty => {
                return Ok(GroundingView::Empty)
            },
            GroundingView::View {free_variables: sub_free_variables, condition: sub_condition,
                grounding, query, ids: sub_ids,..} => {

                let to_add = sub_free_variables.iter()
                    .map(|(k, v)| (k.clone(), v.clone()));
                free_variables.extend(to_add);
                ids = max(ids, sub_ids.clone());

                if let GroundingQuery::Join { variables: sub_variables, conditions: sub_conditions,
                    grounding: sub_grounding, natural_joins: sub_natural_joins,
                    theta_joins: sub_theta_joins, precise: sub_precise,.. } = query {

                    // handle the special case of a variable used as an argument to an interpreted function
                    match sub_grounding {
                        SQLExpr::Variable(symbol) => {
                            if let QueryVariant::Interpretation(table_name, _, else_) = variant {
                                if else_.is_none() {  // not a left join
                                    let column = Column::new(table_name, &format!("a_{i}"));

                                    //  update the query in progress
                                    variables.insert(symbol.clone(), Some(column.clone()));
                                    // sub-query has no conditions
                                    groundings.push(sub_grounding.clone());
                                    // do not push to natural_joins
                                    // push `sub_grounding = column` to thetas
                                    let if_ = Mapping(sub_ids.clone(), sub_grounding.clone(), column);
                                    thetas.push(if_);

                                    continue  // to the next sub-query
                                }
                            }
                        },
                        _ => {}
                    };

                    conditions.extend(sub_conditions.iter().cloned());
                    groundings.push(sub_grounding.clone());
                    ids_.push(sub_ids.clone());
                    natural_joins.extend(sub_natural_joins.iter().cloned());
                    theta_joins.extend(sub_theta_joins.iter().cloned());
                    precise &= *sub_precise;

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

                            // push `sub_grounding = column` to conditions and thetas
                            let if_ = Mapping(sub_ids.clone(), sub_grounding.clone(), column);
                            if *sub_ids != Ids::All {
                                conditions.push(Left(if_.clone()));
                            }
                            // adds nothing if sub_ids == None
                            thetas.push(if_);
                        },
                        QueryVariant::Apply
                        | QueryVariant::Construct
                        | QueryVariant::Predefined => {}
                    }
                } else {  // not a Join --> use the ViewType
                    match grounding {
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
                                conditions.push(Right(table_name.clone()));
                            }
                            groundings.push(SQLExpr::Value(Column::new(table_name, "G"), None));

                            let map_variables = sub_free_variables.iter()
                                .filter_map( |(symbol, table_name)| {
                                    if table_name.is_some() {
                                        Some(symbol.clone())
                                    } else {
                                        None
                                    }
                                }).collect();
                            let sub_natural_join = NaturalJoin::ViewType(table_name.clone(), map_variables);
                            natural_joins.insert(sub_natural_join.clone());
                        },
                    }
                }
            }
        }
    };

    // remove natural_joins of types that are not used in variables
    let natural_joins = natural_joins.iter()
        .filter_map( |natural_join| {
            match natural_join {
                NaturalJoin::Variable(table_name, symbol) => {
                    let column = variables.get(symbol).unwrap();
                    if let Some(column) = column {
                        if column.table_name == *table_name  {
                            Some(natural_join.clone())
                        } else {
                            None // otherwise, unused variable
                        }
                    } else {
                        unreachable!()  // infinite variable.
                    }
                },
                NaturalJoin::ViewType(..) => {
                    Some(natural_join.clone())
                }
            }
        }).collect();

    let grounding =
        match variant {
            QueryVariant::Interpretation(table_name, ids_, else_) => {
                let left = else_.is_some();
                theta_joins.insert((left, table_name.clone(), thetas.clone()));

                ids = ids_.clone();  // reflects the grounding column, not if_
                let else_ =
                    match else_ {
                        None => None,
                        Some(None) => {  // no `else` value => create a compound term
                            let expr = SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings));
                            Some(Box::new(expr))
                        },
                        Some(Some(else_)) => Some(Box::new(to_sqlexpr(else_.clone())))
                    };
                match (ids_, exclude) {
                    (Ids::All, Some(false)) => SQLExpr::Boolean(true),  // TU view
                    (Ids::All, Some(true)) => SQLExpr::Boolean(false),  // UF view
                    _ => SQLExpr::Value(Column::new(table_name, "G"), else_)
                }
            },
            QueryVariant::Apply => {
                ids = Ids::None;
                SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings))
            },
            QueryVariant::Construct => {
                // do not change ids.
                match (qual_identifier.to_string().as_str(), exclude) {
                    ("true", Some(false)) => SQLExpr::Boolean(true),  // TU view
                    ("true", Some(true)) => return Ok(GroundingView::Empty), // UF view
                    ("true", None) => SQLExpr::Boolean(true),  // G view

                    ("false", Some(false)) => return Ok(GroundingView::Empty),  // TU view
                    ("false", Some(true)) => SQLExpr::Boolean(false),  // UF view
                    ("false", None) => SQLExpr::Boolean(false),  // G view

                    _ => SQLExpr::Construct(qual_identifier.clone(), Box::new(groundings))
                }
            },
            QueryVariant::Predefined => {
                // LINK src/doc.md#_Equality
                let function = match qual_identifier.to_string().as_str() {
                    "and"       => Predefined::And,
                    "or"        => Predefined::Or,
                    "implies"   => Predefined::Implies,
                    "not"       => Predefined::Not,
                    "="         => Predefined::Eq,
                    "<"         => Predefined::Less,
                    "<="        => Predefined::LE,
                    ">="        => Predefined::GE,
                    ">"         => Predefined::Greater,
                    "distinct"  => Predefined::Distinct,

                    "+"     => Predefined::Plus,
                    "-"     => Predefined::Minus,
                    "*"     => Predefined::Times,
                    "div"   => Predefined::Div,
                    "abs"   => Predefined::Abs,
                    "mod"   => Predefined::Mod,
                    _ => panic!()
                };
                if ! [  Predefined::And,
                        Predefined::Or,
                        Predefined::Implies,
                        Predefined::Not
                     ].contains(&function) {
                    precise = false
                };

                let ops: Vec<_> = ids_.iter().cloned().zip(groundings.iter().cloned()).collect();

                SQLExpr::Predefined(function, Box::new(ops))
            }
        };

    // sanitize the name
    let re = Regex::new(r"[\+\-/\*=\%\?\!\.\$\&\^<>@]").unwrap();
    let name = qual_identifier.to_string();
    let name = re.replace_all(&name, "");
    let table_name = TableName::new(&name, index);
    let query = GroundingQuery::Join {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        precise
    };
    let exclude = if precise { None } else { exclude };
    GroundingView::new(table_name, free_variables, query, exclude, ids, solver)
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
                sub_view: sub_sub_view, ..}
                = query {
                    if agg == sub_agg  {
                        // it's possible to by pass the sub-aggregate
                        let mut infinite_variables = infinite_variables.clone();
                        infinite_variables.extend(sub_infinite_variables.iter().cloned());

                        let query = GroundingQuery::Aggregate {
                            agg: agg.to_string(),
                            free_variables: free_variables.clone(),
                            infinite_variables: infinite_variables.clone(),
                            sub_view: Box::new(*sub_sub_view.clone()),
                        };
                        return GroundingView::new(table_name, free_variables.clone(), query, exclude, ids.clone(), solver)
                    }
            }

            let query = GroundingQuery::Aggregate {
                agg: agg.to_string(),
                free_variables: free_variables.clone(),
                infinite_variables: infinite_variables.clone(),
                sub_view: Box::new(sub_query.clone()),
            };

            GroundingView::new(table_name, free_variables.clone(), query, exclude, ids.clone(), solver)
        }
    }
}


pub(crate) fn query_for_union(
    sub_views: Vec<GroundingView>,
    exclude: Option<bool>,
    agg: String,
    index: TermId,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    // determine variables, condition and ids
    let mut free_variables = IndexMap::new();
    let mut condition = false;
    let mut ids = Ids::All;
    let mut precise = true;
    for sub_view in sub_views.clone() {
        if let GroundingView::View { free_variables: sub_free_variables,
            condition: sub_condition, ids: sub_ids, query, .. } = sub_view {

            free_variables.append(&mut sub_free_variables.clone());
            condition |= sub_condition;
            ids = max(ids, sub_ids);
            precise &= query.is_precise();
        }
    }
    let exclude = if precise { None } else { exclude };

    // build the sub-queries
    let sub_queries = sub_views.iter()
        .filter_map( |sub_view| {
            if let GroundingView::View { free_variables: sub_free_variables, condition: sub_condition,
                grounding, ..} = sub_view {

                match grounding {
                    Either::Left(grounding) => {
                        // boolean
                        let q_variables = free_variables.iter()
                            .map( |(symbol, _)| (symbol.clone(), None))
                            .collect();
                        Some(GroundingQuery::Join {
                            variables: q_variables,
                            conditions: vec![],
                            grounding: grounding.clone(),
                            natural_joins: IndexSet::new(),
                            theta_joins: IndexSet::new(),
                            precise: true
                        })
                    },
                    Either::Right(table_name) => {
                        // add the cross-product of missing variables
                        let mut q_variables = IndexMap::new();
                        let join_vars = sub_free_variables.iter()
                            .filter_map( |(symbol, table_name)| {
                                if table_name.is_some() {
                                    Some(symbol.clone())
                                } else {
                                    None
                                }
                            }).collect();
                        let natural_join = NaturalJoin::ViewType(table_name.clone(), join_vars);
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
                                vec![Right(table_name.clone())]
                            } else if condition {  // add `"true" as if_``
                                let empty_table = TableName { base_table: "".to_string(), index: 0 };
                                vec![Right(empty_table)]
                            } else {
                                vec![]
                            };

                        Some(GroundingQuery::Join {
                            variables: q_variables,
                            conditions,
                            grounding: SQLExpr::Value(Column::new(table_name, "G"), None),
                            natural_joins,
                            theta_joins: IndexSet::new(),
                            precise: true  // because it is based on a view
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
        return GroundingView::new(table_name, free_variables, sub_queries.first().unwrap().clone(), exclude, ids.clone(), solver)
    };

    // create the union
    let query = GroundingQuery::Union{ sub_queries: Box::new(sub_queries), precise };

    let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS {query}");
    solver.conn.execute(&sql, ())?;

    // create the sub_view
    let sub_view = GroundingView::View {
        free_variables: free_variables.clone(),
        condition,
        grounding: Either::Right(table_name),
        query,
        exclude,
        ids: ids.clone()
    };

    // create the aggregate
    let table_name = TableName{base_table: format!("agg_union_{index}"), index: 0};
    let query = GroundingQuery::Aggregate {
        agg: agg.to_string(),
        free_variables: free_variables.clone(),
        infinite_variables: vec![],
        sub_view: Box::new(sub_view),
    };

    GroundingView::new(table_name, free_variables, query, exclude, ids.clone(), solver)
}


/////////////////////  Grounding ViewType utilities  //////////////////////////////


impl GroundingView {

    pub(crate) fn new (
        table_name: TableName,
        free_variables: IndexMap<Symbol, Option<TableName>>,
        query: GroundingQuery,
        exclude: Option<bool>,
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
                        grounding: Either::Left(grounding.clone()),
                        query,
                        exclude,
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
                        grounding: Either::Right(table_name),
                        query,
                        exclude,
                        ids})
                }
            },
            GroundingQuery::Aggregate { .. } => {

                let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS {query}");
                solver.conn.execute(&sql, ())?;

                Ok(GroundingView::View {
                        free_variables,
                        condition: false,
                        grounding: Either::Right(table_name),
                        query,
                        exclude,
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
                    grounding: Either::Right(table_name),
                    query,
                    exclude,
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
        view_type: ViewType,
        solver: &mut Solver
    ) -> Result<GroundingView, SolverError> {
        match self {
            GroundingView::Empty => Ok(self.clone()),
            GroundingView::View{free_variables, query, exclude, ids, ..} =>
                query.negate(free_variables.clone(), index, view_type, *exclude, ids, solver)
        }
    }
}

// convert an identifier to an SQLExpr
fn to_sqlexpr (
    id: Term
) -> SQLExpr {
    match id {
        Term::SpecConstant(v, _) =>
            SQLExpr::Constant(v),
        Term::Identifier(c, _) =>
            SQLExpr::Construct(c, Box::new(vec![])),
        Term::Application(function, terms, _) =>{
            //todo check for constructor
            let terms = terms.iter()
                .map( |t| to_sqlexpr(t.clone()))
                .collect();
            SQLExpr::Construct(function, Box::new(terms))
        }
        _ => unreachable!()
    }
}