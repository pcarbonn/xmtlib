// Copyright Pierre Carbonnelle, 2025.

use std::hash::Hash;

use indexmap::{IndexMap, IndexSet};
use itertools::Either::{self, Left, Right};

use crate::ast::{QualIdentifier, SortedVar, SpecConstant, Symbol, L};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e2_ground_query::{GroundingQuery, NaturalJoin, TableName, TableAlias, Column, INDENT};
use crate::private::e3_ground_sql::{Mapping, SQLExpr, Predefined};
use crate::private::z_utilities::OptionMap;


////////////////////// Data structures for grounding views ////////////////////


/// the grounding view of a term
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum GroundingView {
    Empty,
    View {  // SELECT vars, cond, grounding (from view) WHERE val <> exclude
        free_variables: OptionMap<Symbol, TableAlias>,  // None for infinite variables, sort interpretation table otherwise
        condition: bool,
        grounding: Either<SQLExpr, TableAlias>, // Left for SpecConstant, Boolean without table. Right for grounding field in table.
        exclude: Option<bool>, // e.g., "false" in TU view

        query: GroundingQuery,  // the underlying query
        all_ids: bool,  // true if all the groundings are certainly ids at the time of query creation.
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


// SQL of the underlying select
impl std::fmt::Display for GroundingView {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundingView::Empty => write!(f, "SELECT \"true\" AS G WHERE FALSE"),
            GroundingView::View { query, .. } => write!(f, "{query}")
        }
    }
}

impl GroundingView {
    pub(crate) fn to_sql(
        &self,
        var_joins: &IndexMap<Symbol, (Column, usize)>,
        indent: &str
    ) -> (String, Ids) {
        match self {
            GroundingView::Empty => (format!("SELECT \"true\" AS G\n{indent} WHERE FALSE"), Ids::All),
            GroundingView::View { query, exclude, .. } =>
                if let Some(exclude) = exclude {
                    let indent1 = format!("{indent}{INDENT}").to_string();
                    let (query, ids) = query.to_sql(var_joins, &indent1);
                    let comment = format!("-- exclude({})\n{indent}", indent.len());
                    let query = format!("{comment}SELECT *\n{indent} FROM ({query})\n{indent} WHERE G <> \"{exclude}\"");
                    (query, ids)
                } else {
                    query.to_sql(var_joins, indent)
                }
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
pub(crate) fn view_for_constant(
    spec_constant: &SpecConstant
) -> Result<GroundingView, SolverError> {
    let query = GroundingQuery::Join {
        variables: OptionMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexSet::new(),
        theta_joins: IndexMap::new(),
        precise: true
    };
    let base_table = TableName("ignore".to_string());
    let table_alias = TableAlias::new(base_table, 0);
    GroundingView::new(table_alias, OptionMap::new(), query, None, true)
}


/// Creates a query for a variable
// LINK src/doc.md#_Variables
pub(crate) fn view_for_variable(
    symbol: &Symbol,
    base_table: Option<TableName>,
    index: usize
) -> Result<GroundingView, SolverError> {
    let table_name = TableName("variable".to_string());
    let new_alias = TableAlias::new(table_name, index);
    if let Some(base_table) = base_table {
        let table_alias = TableAlias::new(base_table, index);
        let column = Column::new(&table_alias, "G");
        let variables= OptionMap::from([(symbol.clone(), Some(column.clone()))]);

        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::from([NaturalJoin::CrossProduct(table_alias.clone(), symbol.clone())]),
            theta_joins: IndexMap::new(),
            precise: false  // imprecise for boolean variable !
        };
        let free_variables = OptionMap::from([(symbol.clone(), Some(table_alias))]);
        GroundingView::new(new_alias, free_variables, query, None, true) // todo perf: exclude for boolean
    } else {  // infinite variable ==> just "x"
        let variables = OptionMap::from([(symbol.clone(), None)]);
        let query = GroundingQuery::Join{
            variables,
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::new(),
            theta_joins: IndexMap::new(),
            precise: true  // cannot be boolean
        };
        let free_variables = OptionMap::from([(symbol.clone(), None)]);
        GroundingView::new(new_alias, free_variables, query, None, false)
    }
}


#[derive(Debug, strum_macros::Display, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ViewType {
    #[strum(to_string = "TU")] TU,
    #[strum(to_string = "UF")] UF,
    #[strum(to_string = "G")] G,
}

/// describes the type of query to create for a compound term
pub(crate) enum QueryVariant {
    Interpretation(TableAlias, Ids),
    Apply,
    Construct,
    Predefined
}

/// Creates a query for a compound term, according to `variant`.
pub(crate) fn view_for_compound(
    qual_identifier: &QualIdentifier,
    index: TermId,
    sub_queries: &Vec<GroundingView>,
    variant: &QueryVariant,
    exclude: Option<bool>,
    solver: &mut Solver
) -> Result<GroundingView, SolverError> {

    let mut free_variables = OptionMap::new();
    let mut variables = OptionMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins = IndexSet::new();
    let mut theta_joins = IndexMap::new();
    let mut thetas = vec![];
    let mut all_ids = true;
    let mut precise = true;

    for (i, sub_q) in sub_queries.iter().enumerate() {

        match sub_q {
            GroundingView::Empty => {
                return Ok(GroundingView::Empty)
            },
            GroundingView::View {free_variables: sub_free_variables, condition: sub_condition,
                grounding, query, all_ids: sub_all_ids,..} => {

                let to_add = sub_free_variables.iter()
                    .map(|(k, v)| (k.clone(), v.clone()));
                free_variables.extend(to_add);
                all_ids = all_ids && *sub_all_ids;

                // if the sub-query is a Join
                if let GroundingQuery::Join { variables: sub_variables, conditions: sub_conditions,
                    grounding: sub_grounding, natural_joins: sub_natural_joins,
                    theta_joins: sub_theta_joins, precise: sub_precise,.. } = query {

                    // handle the special case of a variable used as an argument to an interpreted function
                    // example: f(x, a, x)
                    // LINK src/doc.md#_Variables
                    if let SQLExpr::Variable(symbol) = sub_grounding {  // symbol = x, at iteration for argument 1 and 3
                        if let QueryVariant::Interpretation(table_name, _) = variant { // table_name = f
                            // the sub_grounding is a free variable, and and the i-th argument of f
                            // => update the query in progress

                            let column = Column::new(table_name, &format!("a_{}", i+1));  // "f.a_1", "f.a_3"
                            free_variables.insert(symbol.clone(), Some(table_name.clone()));

                            // add "f.a_1 AS x" to SELECT  ("f.a_3" is ignored)
                            variables.insert(symbol.clone(), Some(column.clone()));

                            // sub-query has no conditions
                            // add "{sub_grounding}" to groundings. In SQL, sub_grounding is "f.a_1"
                            groundings.push(sub_grounding.clone());  // ("f.a_1", a, "f.a_1")
                            // do not push to natural_joins
                            // push `f.a_1 = f.a_1` and `f.a_3 = f.a_1` to condition for table_name
                            let if_ = Mapping(sub_grounding.clone(), column);
                            thetas.push(Some(if_));

                            continue  // to the next sub-query
                        }
                    };

                    conditions.extend(sub_conditions.iter().cloned());
                    groundings.push(sub_grounding.clone());
                    natural_joins.extend(sub_natural_joins.iter().cloned());
                    for (table_alias, mappings) in sub_theta_joins.iter() {
                        if theta_joins.contains_key(table_alias) {
                            unreachable!()
                        } else {
                            theta_joins.insert(table_alias.clone(), mappings.clone());
                        }
                    }
                    precise &= *sub_precise;

                    // merge the variables
                    for (symbol, column) in sub_variables.clone().iter() {
                        variables.insert(symbol.clone(), column.clone());
                    }

                    // compute the join conditions, for later use
                    match variant {
                        QueryVariant::Interpretation(table_name, ..) => {
                            let column = Column::new(table_name, &format!("a_{}", i+1));

                            // push `sub_grounding = column` to conditions and thetas
                            let if_ = Mapping(sub_grounding.clone(), column);
                            if ! *sub_all_ids {
                                conditions.push(Left(if_.clone()));
                            }
                            // adds nothing if sub_ids == None
                            thetas.push(Some(if_));
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
                            for (symbol, _) in sub_free_variables.clone().iter() {
                                    let column = Column::new(table_name, &symbol);
                                    variables.insert(symbol.clone(), Some(column));
                            }

                            if *sub_condition {
                                conditions.push(Right(Some(table_name.clone())));
                            }
                            groundings.push(SQLExpr::G(table_name.clone()));

                            let map_variables = sub_free_variables.0.keys().cloned().collect();
                            let sub_natural_join = NaturalJoin::ViewJoin(query.clone(), table_name.clone(), map_variables);
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
                NaturalJoin::CrossProduct(table_name, symbol) => {
                    let column = variables.get(symbol).unwrap();
                    if let Some(column) = column {
                        if column.table_alias == *table_name  {
                            Some(natural_join.clone())
                        } else {
                            None // otherwise, unused variable
                        }
                    } else {
                        unreachable!()  // infinite variable cannot be joined to a table.
                    }
                },
                NaturalJoin::ViewJoin(..) => {
                    Some(natural_join.clone())
                }
            }
        }).collect();

    let grounding =
        match variant {
            QueryVariant::Interpretation(table_name, ids_) => {
                theta_joins.insert(table_name.clone(), thetas.clone());

                all_ids = *ids_ == Ids::All;  // reflects the grounding column, not if_
                match (ids_, exclude) {
                    (Ids::All, Some(false)) => SQLExpr::Boolean(true),  // complete TU view_
                    (Ids::All, Some(true)) => SQLExpr::Boolean(false),  // complete UF view
                    _ => SQLExpr::Value(Column::new(table_name, "G"), ids_.clone())
                }
            },
            QueryVariant::Apply => {
                all_ids = false;
                if let QualIdentifier::Identifier(L(identifier, _)) = qual_identifier {
                    solver.grounded.insert(identifier.clone());
                };  // qualified identifier cannot be interpreted: they are either pre-defined or accessors
                SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings))
            },
            QueryVariant::Construct => {
                // do not change all_ids.
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
                    "not"       => Predefined::Not,
                    "="         => Predefined::Eq,
                    "<"         => Predefined::Less,
                    "<="        => Predefined::LE,
                    ">="        => Predefined::GE,
                    ">"         => Predefined::Greater,
                    "distinct"  => Predefined::Distinct,
                    "ite"       => Predefined::Ite,

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
                        Predefined::Not
                     ].contains(&function) {
                    precise = false
                };

                SQLExpr::Predefined(function, Box::new(groundings))
            }
        };

    let base_table = solver.create_table_name(format!("{qual_identifier}_{index}"));
    let table_alias = TableAlias::new(base_table, 0);
    let query = GroundingQuery::Join {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        precise
    };
    let exclude = if precise { None } else { exclude };
    GroundingView::new(table_alias, free_variables, query, exclude, all_ids)
}


/// Creates a query over an aggregate view, possibly adding a where clause if exclude is not empty
pub(crate) fn query_for_aggregate(
    sub_query: &GroundingView,
    free_variables: &OptionMap<Symbol, TableAlias>,
    infinite_variables: &Vec<SortedVar>,  // variables being quantified
    agg: &str,  // "and", "or" or ""
    exclude: Option<bool>,
    table_alias: TableAlias
) -> Result<GroundingView, SolverError> {

    match sub_query {
        GroundingView::Empty => {
            Ok(GroundingView::Empty)
        },
        GroundingView::View{query, all_ids,..} => {
            // LINK src/doc.md#_Infinite
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
                        return GroundingView::new(table_alias, free_variables.clone(), query, exclude, *all_ids)
                    }
            }

            let query = GroundingQuery::Aggregate {
                agg: agg.to_string(),
                free_variables: free_variables.clone(),
                infinite_variables: infinite_variables.clone(),
                sub_view: Box::new(sub_query.clone()),
            };

            GroundingView::new(table_alias, free_variables.clone(), query, exclude, *all_ids)
        }
    }
}


pub(crate) fn view_for_union(
    sub_views: Vec<GroundingView>,
    exclude: Option<bool>,
    agg: String,
    index: TermId
) -> Result<GroundingView, SolverError> {

    // determine variables and condition
    let mut free_variables = OptionMap::new();
    let mut condition = false;
    let mut all_ids = true;
    let mut precise = true;
    for sub_view in sub_views.clone() {
        if let GroundingView::View { free_variables: sub_free_variables,
            condition: sub_condition, all_ids: sub_all_ids, query, .. } = sub_view {

            free_variables.append(&mut sub_free_variables.clone());
            condition |= sub_condition;
            all_ids = all_ids && sub_all_ids;
            precise &= query.is_precise();
        }
    }
    let exclude = if precise { None } else { exclude };

    // build the sub-queries
    let sub_queries = sub_views.iter()
        .filter_map( |sub_view| {
            if let GroundingView::View { free_variables: sub_free_variables, condition: sub_condition,
                grounding, query, ..} = sub_view {

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
                            theta_joins: IndexMap::new(),
                            precise: true
                        })
                    },
                    Either::Right(table_name) => {
                        // add the cross-product of missing variables
                        let mut extended = false;
                        let mut q_variables = OptionMap::new();
                        let join_vars = sub_free_variables.iter()
                            .filter_map( |(symbol, table_name)| {
                                if table_name.is_some() {
                                    Some(symbol.clone())
                                } else {
                                    None
                                }
                            }).collect();
                        let natural_join = NaturalJoin::ViewJoin(query.clone(), table_name.clone(), join_vars);
                        let mut natural_joins = IndexSet::from([natural_join]);
                        for (symbol, sub_table_name) in free_variables.iter() {
                            if let Some(_) = sub_free_variables.get(symbol) {  // the variable is in the sub_view
                                let column = Column::new(table_name, symbol);
                                q_variables.insert(symbol.clone(), Some(column));
                            } else if let Some(table_name) = sub_table_name {  // create cross-product
                                let column = Column::new(table_name, symbol);
                                q_variables.insert(symbol.clone(), Some(column));
                                let natural_join = NaturalJoin::CrossProduct(table_name.clone(), symbol.clone());
                                natural_joins.insert(natural_join);
                                extended = true;
                            } else {  // infinite variable
                                q_variables.insert(symbol.clone(), None);
                            }
                        }
                        if ! extended {
                            Some(query.clone())  // unchanged
                        } else {
                            let conditions =
                                if *sub_condition {
                                    vec![Right(Some(table_name.clone()))]
                                } else if condition {  // add `"true" as if_``
                                    vec![Right(None)]
                                } else {
                                    vec![]
                                };

                            Some(GroundingQuery::Join {
                                variables: q_variables,
                                conditions,
                                grounding: SQLExpr::G(table_name.clone()),
                                natural_joins,
                                theta_joins: IndexMap::new(),
                                precise: true  // because it is based on a view
                            })
                        }
                    },
                }
            } else { // empty view
                None
             }
        }).collect::<Vec<_>>();

    if sub_queries.len() == 0 { return Ok(GroundingView::Empty) }

    let table_alias = TableAlias{base_table: TableName(format!("union_{index}")), index: 0};
    if sub_queries.len() == 1 {
        return GroundingView::new(table_alias, free_variables, sub_queries.first().unwrap().clone(), exclude, all_ids)
    };

    // create the union
    let query = GroundingQuery::Union{ sub_queries: Box::new(sub_queries), precise };

    // create the sub_view
    let sub_view = GroundingView::View {
        free_variables: free_variables.clone(),
        condition,
        grounding: Either::Right(table_alias),
        query,
        exclude,
        all_ids
    };

    // create the aggregate
    let table_alias = TableAlias{base_table: TableName(format!("agg_union_{index}")), index: 0};
    let query = GroundingQuery::Aggregate {
        agg: agg.to_string(),
        free_variables: free_variables.clone(),
        infinite_variables: vec![],
        sub_view: Box::new(sub_view),
    };

    GroundingView::new(table_alias, free_variables, query, exclude, all_ids)
}


/////////////////////  Grounding ViewType utilities  //////////////////////////////


impl GroundingView {

    pub(crate) fn new (
        table_alias: TableAlias,
        free_variables: OptionMap<Symbol, TableAlias>,
        query: GroundingQuery,
        exclude: Option<bool>,
        all_ids: bool
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
                        all_ids
                    })
                } else {
                    let condition = conditions.len() > 0;

                    Ok(GroundingView::View{
                        free_variables,
                        condition,
                        grounding: Either::Right(table_alias),
                        query,
                        exclude,
                        all_ids})
                }
            },
            GroundingQuery::Aggregate { .. } => {

                Ok(GroundingView::View {
                        free_variables,
                        condition: false,
                        grounding: Either::Right(table_alias),
                        query,
                        exclude,
                        all_ids: false
                    })
            },
            GroundingQuery::Union { ref sub_queries, .. } => {

                Ok(GroundingView::View {
                    free_variables,
                    condition: sub_queries.iter().any( |view| {
                        if let GroundingQuery::Join{conditions, ..} = view {
                            0 < conditions.len()
                        } else {
                            false
                        }
                    }),
                    grounding: Either::Right(table_alias),
                    query,
                    exclude,
                    all_ids
                })

            }
        }
    }

    /// return the view's free and infinite variables
    pub(crate) fn get_free_variables(
        &self,
        variables: &Vec<SortedVar>
    ) -> (OptionMap<Symbol, TableAlias>, Vec<SortedVar>) {

        let query_variables = match self {
                GroundingView::Empty => OptionMap::new(),
                GroundingView::View{free_variables,..} => free_variables.clone()
            };

        // free_variables = query_variables \ variables
        let mut free_variables = query_variables.clone();
        for SortedVar(symbol, _) in variables {
            free_variables.shift_remove(symbol);
        }

        // LINK src/doc.md#_Infinite
        // infinite_variables < variables
        let infinite_variables = variables.iter()
            .filter( |SortedVar(symbol, _)|
                match query_variables.get(symbol) {
                    Some(None) => true,
                    Some(Some(_)) => false,
                    None => false
            }).map(|var| var.clone()).collect::<Vec<_>>();

        (free_variables, infinite_variables)
    }


    pub(crate) fn get_ids(&self) -> bool {
        match self {
            GroundingView::Empty => true,
            GroundingView::View{all_ids, ..} => *all_ids
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
            GroundingView::View{free_variables, query, exclude, all_ids, ..} =>
                query.negate(free_variables.clone(), index, view_type, *exclude, *all_ids, solver)
        }
    }
}

