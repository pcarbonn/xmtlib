// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};

use crate::api::{Identifier, QualIdentifier, SortedVar, SpecConstant, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};

use crate::private::e2_ground_sql::SQLExpr;


////////////////////// Data structures for grounding queries //////////////////


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
        empty: bool,  // true when the grounding table is empty

        ids: Ids,  // if the groundings are all Ids
    },
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


impl std::fmt::Display for GroundingQuery {

    // SELECT {variables.0} AS {variables.1},
    //        {condition} AS cond,  -- if condition
    //        {grounding} AS G,
    //   FROM {natural joins}
    //   JOIN {theta_joins}
    //  WHERE FALSE  (if empty)

    // SQL formatting
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundingQuery::Join{variables, conditions, grounding,
                natural_joins, theta_joins, empty, ..} => {

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
                        format!("{} AS cond, ", condition[0])
                    } else {
                        format!("and_({}) AS cond, ", condition.join(", "))
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
                                            Some(format!(" {this_column} = {column}"))
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
                        if *empty {
                            format!(" WHERE FALSE")
                        } else { "".to_string() }
                    } else if tables.len() == 1 {
                        let mut tables = format!(" FROM {}", tables.join(" JOIN "));
                        if tables.contains(" ON ") {
                            // replace the only " ON " by " WHERE "
                            tables = tables.replace(" ON ", " WHERE ");
                            if *empty {
                                tables = format!("{} AND FALSE", tables)
                            }
                        } else if *empty {
                            tables = format!("{} WHERE FALSE", tables)
                        }
                        tables
                    } else {
                        let mut tables = format!(" FROM {}", tables.join(" JOIN "));
                        if *empty {
                            tables = format!("{} WHERE FALSE", tables)
                        }
                        tables
                    };

                write!(f, "SELECT {variables_}{condition}{grounding_}{tables}")
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
    spec_constant: &SpecConstant
) -> GroundingQuery {
    GroundingQuery::Join {
        variables: IndexMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexSet::new(),
        theta_joins: IndexSet::new(),
        empty: false,
        ids: Ids::All,
    }
}


/// Creates a query for a variable
pub(crate) fn query_for_variable(
    symbol: &Symbol,
    base_table: &String,
    index: usize
) -> GroundingQuery {
    if *base_table != "".to_string() {
        let table_name = TableName{base_table: base_table.clone(), index};
        let column = Column{table_name: table_name.clone(), column: "G".to_string()};

        GroundingQuery::Join{
            variables: IndexMap::from([(symbol.clone(), Some(column.clone()))]),
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::from([NaturalJoin::Variable(table_name, symbol.clone())]),
            theta_joins: IndexSet::new(),
            empty: false,
            ids: Ids::All,
        }
    } else {
        GroundingQuery::Join{
            variables: IndexMap::from([(symbol.clone(), None)]),
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::new(),
            theta_joins: IndexSet::new(),
            empty: false,
            ids: Ids::None,
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum View {
    TU, UF, G,
}

/// describes the type of query to create for a compound term
pub(crate) enum Variant {
    Interpretation(TableName, Ids),
    Apply,
    Construct(View),
    PredefinedBoolean(View)
}

/// Creates a query for a compound term, according to `variant`.
pub(crate) fn query_for_compound(
    qual_identifier: &QualIdentifier,
    sub_queries: &mut Vec<GroundingQuery>,
    variant: &Variant,
    solver: &Solver
) -> Result<GroundingQuery, SolverError> {

    let mut variables: IndexMap<Symbol, Option<Column>> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins = IndexSet::new();
    let mut theta_joins = IndexSet::new();
    let mut thetas = vec![];
    let mut empty = false;
    let mut ids: Ids = Ids::All;

    for (i, sub_q) in sub_queries.iter_mut().enumerate() {
        let for_variable = sub_q.is_for_a_variable()?;

        match sub_q {
            GroundingQuery::Join {
                variables: sub_variables, conditions: sub_conditions,
                grounding: sub_grounding, natural_joins: sub_natural_joins,
                theta_joins: sub_theta_joins, empty: sub_empty,
                ids: sub_ids } => {

                if let Some(symbol) = for_variable {
                    if let Variant::Interpretation(table_name, _) = variant {
                        let column = Column{table_name: table_name.clone(), column: format!("a_{i}")};

                        //  update the query in progress
                        variables.insert(symbol.clone(), Some(column.clone()));
                        let variable = SQLExpr::Variable(symbol.clone());
                        // sub-query has no conditions
                        groundings.push(variable.clone());
                        // do not push to natural_joins
                        thetas.push((sub_ids.clone(), variable.clone(), column));

                        continue  // to the next sub-query
                    }
                };

                conditions.append(sub_conditions);
                groundings.push(sub_grounding.clone());
                natural_joins.append(sub_natural_joins);
                theta_joins.append(sub_theta_joins);
                empty = empty || *sub_empty;
                ids = max(ids, sub_ids.clone());

                for (symbol, column) in sub_variables.clone() {
                    // insert if not there yet,
                    // or if it was a natural join column, but not anymore
                    match variables.get(&symbol) {
                        None => {
                            variables.insert(symbol.clone(), column.clone());
                        },
                        Some(_) => { }
                    }
                }

                // compute the join conditions, for later use
                match variant {
                    Variant::Interpretation(table_name, _) => {
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
            Variant::Interpretation(table_name, ids_) => {
                theta_joins.insert((table_name.clone(), thetas));
                ids = max(ids, ids_.clone());
                SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()})
            },
            Variant::Apply => {
                ids = Ids::None;
                SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings))
            },
            Variant::Construct(view) => {
                ids = Ids::All;
                if *qual_identifier == solver.true_ {
                    match view {
                        View::TU => SQLExpr::Boolean(true),
                        View::UF => {
                            empty = true;
                            SQLExpr::Boolean(true)
                        },
                        View::G => SQLExpr::Boolean(true),
                    }
                } else if *qual_identifier == solver.false_ {
                    match view {
                        View::TU => {
                            empty = true;
                            SQLExpr::Boolean(false)
                        },
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

    Ok(GroundingQuery::Join {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        empty,
        ids,
    })
}


/// Creates a query over an aggregate view, possibly adding a where clause if exclude is not empty
pub(crate) fn query_for_aggregate(
    sub_query: &GroundingQuery,
    free_variables: &IndexMap<Symbol, Option<Column>>,
    variables: &Vec<SortedVar>,  // variables being quantified
    agg: &str,  // "and", "or" or ""
    exclude: &str, // "true" or "false"
    table_name: TableName,
    solver: &mut Solver
) -> Result<GroundingQuery, SolverError> {

    // create sql of the sub_query
    let sub_view = sub_query.as_sql();

    // now create the aggregation view
    let free = free_variables.iter()
        .map( |(symbol, _)| symbol.to_string() )
        .collect::<Vec<_>>().join(", ");
    let free = if free == "" { free } else { free + ", " };

    let sub_variables = sub_query.get_variables();
    let infinite_variables = variables.iter()
        .filter_map ( |sv| {
            if let Some(Some(_)) = sub_variables.get(&sv.0) {
                None
            } else {
                Some(sv)
            }
        }).collect::<Vec<_>>();

    // compute the grounding:-
    //   just `or_aggregate(G)``,
    //   or `or_aggregate("(forall ({vars}) " || G || ")"` for infinite variables
    let vars = infinite_variables.iter()
        .map( |sv| sv.to_string() )
        .collect::<Vec<_>>().join(" ");
    let grounding =
        if vars.len() == 0 && agg == "" {
            format!("G")
        } else if vars.len() == 0 && agg != ""{
            format!("{agg}_aggregate(G)")
        } else if agg == "and" {
            format!("\"(forall ({vars}) \" || {agg}_aggregate(G) || \")\"")
        } else if agg == "or" {
            format!("\"(exists ({vars}) \" || {agg}_aggregate(G) || \")\"")
        } else {  // top-level "for all", with infinite variables
            format!("\"(forall ({vars}) \" || G || \")\"")
        };

    let group_by = free_variables.iter()
        .filter_map( |(_, column)| {
            if let Some(column) = column {
                Some(column.column.to_string())
            } else {
                None
            }
        }).collect::<Vec<_>>().join(", ");
    let group_by =
        if group_by == "" || agg == "" {
            "".to_string()
        } else {
            format!(" GROUP BY {group_by}")
        };

    let mut sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS SELECT {free}{grounding} as G from ({sub_view}){group_by}");
    if exclude != "" {
        sql = sql + format!(" HAVING {grounding} <> {exclude}").as_str()
    }
    solver.conn.execute(&sql, ())?;

    // construct the GroundingQuery
    // select {free_variables}, {table_name}.G from {table_name}
    let select = free_variables.iter()
        .map( |(symbol, _)|
            (symbol.clone(), Some(Column{table_name: table_name.clone(), column: symbol.to_string()})))
        .collect::<IndexMap<_, _>>();

    let natural_joins = IndexSet::from([
        NaturalJoin::View(table_name.clone(),free_variables.keys().cloned().collect())
    ]);

    Ok(GroundingQuery::Join{
        variables: select,
        conditions: vec![],
        grounding: SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()}),
        natural_joins: natural_joins,
        theta_joins: IndexSet::new(),
        empty: false,
        ids: Ids::None
    })
}


/////////////////////  Grounding Query utilities  //////////////////////////////


impl GroundingQuery {

    /// create the SQL code for a view
    pub(crate) fn as_sql(&self) -> String {
        match self {
            GroundingQuery::Join{variables, conditions, grounding,
                natural_joins, theta_joins, empty, ids} => {

                let mut conditions = conditions.clone();
                let mut grounding = grounding.clone();
                if 0 < conditions.len() {
                    let imply = QualIdentifier::Identifier(Identifier::Simple(Symbol("=>".to_string())));
                    conditions.push(grounding);
                    grounding = SQLExpr::Apply(imply, Box::new(conditions));
                    conditions = vec![];
                }
                let sub_view = GroundingQuery::Join{
                    variables: variables.clone(),
                    conditions: conditions,
                    grounding: grounding,
                    natural_joins: natural_joins.clone(),
                    theta_joins: theta_joins.clone(),
                    empty: *empty,
                    ids: ids.clone(),
                };
                sub_view.to_string()
            }
        }
    }

    pub(crate) fn get_variables(&self) -> IndexMap<Symbol, Option<Column>> {
        match self {
            GroundingQuery::Join{variables, ..} => variables.clone()
        }
    }

    pub(crate) fn get_ids(&self) -> Ids {
        match self {
            GroundingQuery::Join{ids, ..} => ids.clone()
        }
    }

    pub(crate) fn negate(&self, qual_identifier: &QualIdentifier, view: View) -> GroundingQuery {
        match self {
            GroundingQuery::Join { variables, conditions, grounding, natural_joins, theta_joins, empty, ids} => {
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
                GroundingQuery::Join {
                    variables: variables.clone(),
                    conditions: conditions.clone(),
                    grounding: new_grounding,
                    natural_joins: natural_joins.clone(),
                    theta_joins: theta_joins.clone(),
                    empty: *empty,
                    ids: ids.clone()}
            }
        }
    }

    /// returns the variable if the query is for a variable
    fn is_for_a_variable(&self) -> Result<Option<Symbol>, SolverError> {
        match self {
            GroundingQuery::Join { variables, natural_joins, ids, .. } => {
                if let Some((symbol, column)) = variables.first() {
                    if variables.len() == 1 {
                        if let Some(column) = column {
                            if natural_joins.len() == 1
                            && *ids == Ids::All {
                                if let Some(NaturalJoin::Variable(table_name, _)) = natural_joins.first() {
                                    if column.table_name == *table_name && column.column == "G" {
                                        return Ok(Some(symbol.clone()))
                                    }
                                }
                            }
                        } else {  // variable over infinite domain
                            return Ok(Some(symbol.clone()))
                        }
                    }
                }
            }
        }
        Ok(None)
    }
}