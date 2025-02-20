// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use itertools::Either::{self, Left, Right};

use crate::api::{Identifier, QualIdentifier, SortedVar, SpecConstant, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};


////////////////////// Data structures for grounding queries //////////////////


/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GroundingQuery {

    /// maps variables to None if its domain is infinite or to a Column in a Type or Interpretation table.
    pub(crate) variables: IndexMap<Symbol, Option<Column>>,
    pub(crate) conditions: Vec<SQLExpr>,  // vector of non-empty SQL expressions
    pub(crate) grounding: SQLExpr,
    pub(crate) natural_joins: IndexSet<NaturalJoin>,
    pub(crate) theta_joins: IndexSet<ThetaJoin>,
    pub(crate) where_: Vec<SQLExpr>,

    pub(crate) ids: Ids,  // if the groundings are all Ids
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SQLExpr {
    Boolean(bool),
    Constant(SpecConstant),
    Variable(Symbol),
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    // Only in GroundingQuery.groundings
    Value(Column),  // in an interpretation table.
    //  Only in GroundingQuery.conditions
    Equality(Ids, Box<SQLExpr>, Column),  // c_i, i.e., `is_id(expr) or expr=col`.
}

/// Natural join with a table interpreting a variable or a quantification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum NaturalJoin {
    Variable(TableName, Symbol),  // natural join with a table interpreting a variable
    View(TableName, Vec<Symbol>),  // natural join with a table interpreting a quantification, or a union of grounding views
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
    //  WHERE {where_}

    // SQL formatting
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let variables = self.variables.iter()
            .map(|(symbol, column)| {
                if let Some(column) = column {
                    format!("{column} AS {symbol}")
                } else {
                    format!("\"{symbol}\" AS {symbol}")
                }

            }).collect::<Vec<_>>()
            .join(", ");
        let variables = if variables == "" { variables } else {variables + ", "};

        // condition
        let condition = self.conditions.iter()
            .map( |e| { e.show(&self.variables)})  // can be empty !
            .filter( |c| c != "")
            .map ( |c| format!("({c})"))
            .collect::<Vec<_>>().join(" AND ");
        let condition =
            if condition == "" {
                condition
            } else {
                format!("{condition} AS cond, ")
            };

        // grounding
        let grounding = self.grounding.show(&self.variables);
        let grounding = format!("{grounding} AS G");

        // natural joins
        let naturals = self.natural_joins.iter()
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
                                let column = self.variables.get(symbol).unwrap();
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
        let thetas = self.theta_joins.iter()
            .map( | (table_name, mapping) | {
                let on = mapping.iter()
                    .filter_map( | (ids, e, col) | {
                        let value = e.show(&self.variables);
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

        let where_ = self.where_.iter()
            .map( |e| e.show(&self.variables))
            .collect::<Vec<_>>().join(" AND ");

        // naturals + thetas + where_
        let tables = [naturals, thetas].concat();
        let tables =
            if tables.len() == 0 {
                if where_ == "" { where_ } else {
                    format!(" WHERE {where_}")
                }
            } else if tables.len() == 1 {
                let mut tables = format!(" FROM {}", tables.join(" JOIN "));
                if tables.contains(" ON ") {
                    // replace the only " ON " by " WHERE "
                    tables = tables.replace(" ON ", " WHERE ");
                    if where_ != "" {
                        tables = format!("{} AND {}", tables, where_)
                    }
                } else if where_ !="" {
                    tables = format!("{} WHERE {}", tables, where_)
                }
                tables
            } else {
                let mut tables = format!(" FROM {}", tables.join(" JOIN "));
                if where_ != "" {
                    tables = format!("{} WHERE {}", tables, where_)
                }
                tables
            };

        write!(f, "SELECT {variables}{condition}{grounding}{tables}")
    }
}


impl SQLExpr {
    // it can return an empty string !
    fn show(
        &self,
        variables: &IndexMap<Symbol, Option<Column>>
    ) -> String {

            /// Helper: use either "apply" or "construct2", according to the first argument.
            /// See description of these functions in y_db module.
            ///
            /// Arguments:
            /// * application: either "apply" or "construct2"
            fn sql_for(
                application: &str,
                function: String,
                exprs: &Box<Vec<SQLExpr>>,
                variables: &IndexMap<Symbol, Option<Column>>
            ) -> String {
                if ["and", "or"].contains(&function.as_str()) {
                    let exprs =
                        exprs.iter().cloned().filter_map( |e| {  // try to simplify
                            match e {
                                SQLExpr::Boolean(b) => {
                                    if function == "and" && b { None }
                                    else if function == "or" && !b { None }
                                    else { Some(e.show(variables)) }
                                },
                                _ => Some(e.show(variables))
                            }
                        }).collect::<Vec<_>>();
                    if exprs.len() == 0 {
                        if function == "and" { "\"true\"".to_string() } else { "\"false\"".to_string()}
                    } else if exprs.len() == 1 {
                        exprs.first().unwrap().to_string()
                    } else {
                        format!("{application}(\"{function}\", {})", exprs.join(", "))
                    }
                } else if exprs.len() == 0 {
                    format!("\"{function}\"")
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables))
                        .collect::<Vec<_>>().join(", ");
                    format!("{application}(\"{function}\", {})", terms)
                }
            }  // end helper

        match self {
            SQLExpr::Boolean(value) => format!("\"{value}\""),
            SQLExpr::Constant(spec_constant) => {
                match spec_constant {
                    SpecConstant::Numeral(s) => format!("\"{s}\""),
                    SpecConstant::Decimal(s) => format!("\"{s}\""),
                    SpecConstant::Hexadecimal(s) => format!("\"{s}\""),
                    SpecConstant::Binary(s) => format!("\"{s}\""),
                    SpecConstant::String(s) => format!("\"{s}\""),
                }
            },
            SQLExpr::Variable(symbol) => {
                let column = variables.get(symbol).unwrap();
                if let Some(column) = column {
                    column.to_string()
                } else {
                    format!("\"{symbol}\"")
                }
            },
            SQLExpr::Apply(qual_identifier, exprs) => {
                sql_for("apply", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier.to_string(), exprs, variables)
            },
            SQLExpr::Value(column) => column.to_string(),
            SQLExpr::Equality(ids, expr, column) => {
                let expr = expr.show(variables);
                match ids {
                    Ids::All =>
                         "".to_string(),
                    Ids::Some =>
                         format!("(is_id({expr}) OR {expr} = {column})"),
                    Ids::None =>
                         format!("{expr} = {column}"),
                }
            },
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
    GroundingQuery {
        variables: IndexMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexSet::new(),
        theta_joins: IndexSet::new(),
        where_: vec![],
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

        GroundingQuery{
            variables: IndexMap::from([(symbol.clone(), Some(column.clone()))]),
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::from([NaturalJoin::Variable(table_name, symbol.clone())]),
            theta_joins: IndexSet::new(),
            where_: vec![],
            ids: Ids::All,
        }
    } else {
        GroundingQuery{
            variables: IndexMap::from([(symbol.clone(), None)]),
            conditions: vec![],
            grounding: SQLExpr::Variable(symbol.clone()),
            natural_joins: IndexSet::new(),
            theta_joins: IndexSet::new(),
            where_: vec![],
            ids: Ids::None,
        }
    }
}

pub(crate) enum View {
    TU, UF, G,
}

/// describes the type of query to create for a compound term
pub(crate) enum Variant {
    Interpretation(TableName, Ids),
    Apply,
    Construct,
    PredefinedBoolean(View)
}

/// Creates a query for a compound term, according to `variant`.
pub(crate) fn query_for_compound(
    qual_identifier: &QualIdentifier,
    sub_queries: &mut Vec<GroundingQuery>,
    variant: &Variant
) -> Result<GroundingQuery, SolverError> {

    let mut variables: IndexMap<Symbol, Option<Column>> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins = IndexSet::new();
    let mut theta_joins = IndexSet::new();
    let mut thetas = vec![];
    let mut ids: Ids = Ids::All;

    for (i, sub_q) in sub_queries.into_iter().enumerate() {

        // handle the special case where an argument is a variable
        if let Some(symbol) = sub_q.is_for_a_variable()? {
            if let Variant::Interpretation(table_name, _) = variant {
                let column = Column{table_name: table_name.clone(), column: format!("a_{i}")};

                //  update the query in progress
                variables.insert(symbol.clone(), Some(column.clone()));
                let variable = SQLExpr::Variable(symbol);
                // sub-query has no conditions
                groundings.push(variable.clone());
                // do not push to natural_joins
                thetas.push((sub_q.ids.clone(), variable.clone(), column));

                continue  // to the next sub-query
            }
        };

        conditions.append(&mut sub_q.conditions);
        groundings.push(sub_q.grounding.clone());
        natural_joins.append(&mut sub_q.natural_joins.clone());
        theta_joins.append(&mut sub_q.theta_joins);
        ids = max(ids, sub_q.ids.clone());

        for (symbol, column) in &sub_q.variables {
            // insert if not there yet,
            // or if it was a natural join column, but not anymore
            match variables.get(symbol) {
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

                // adds nothing if sub_q.ids = All
                conditions.push(SQLExpr::Equality(sub_q.ids.clone(), Box::new(sub_q.grounding.clone()), column.clone()));
                // adds nothing if sub_q.ids == None
                thetas.push((sub_q.ids.clone(), sub_q.grounding.clone(), column));
            },
            Variant::Apply
            | Variant::Construct
            | Variant::PredefinedBoolean(..) => {}
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
            Variant::Construct => {
                ids = Ids::None;
                SQLExpr::Construct(qual_identifier.clone(), Box::new(groundings))
            },
            Variant::PredefinedBoolean(view) => {
                todo!()
            }
        };

    Ok(GroundingQuery {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        where_: vec![],
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

    // create sql of a sub-view, using a GroundingQuery
    let mut sub_view = sub_query.clone();

    if 0 < sub_view.conditions.len() {
        let imply = QualIdentifier::Identifier(Identifier::Simple(Symbol("=>".to_string())));
        sub_view.conditions.push(sub_view.grounding);
        sub_view.grounding = SQLExpr::Apply(imply, Box::new(sub_view.conditions));
        sub_view.conditions = vec![];
    }

    let sub_view = sub_view.to_string();

    // now create the aggregation view
    let free = free_variables.iter()
        .map( |(symbol, _)| symbol.to_string() )
        .collect::<Vec<_>>().join(", ");
    let free = if free == "" { free } else { free + ", " };

    let infinite_variables = variables.iter()
        .filter_map ( |sv| {
            let symbol =  &sv.0;
            if let Some(Some(_)) = sub_query.variables.get(symbol) {
                None
            } else {
                Some(sv)
            }
        }).collect::<Vec<_>>();

    // compute the grounding:-
    //   just `or_aggregate(G)``,
    //   or `or_aggregate("(forall ({vars}) " || G || ")"`
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
        } else {
            format!("\"(exists ({vars}) \" || G || \")\"")
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

    Ok(GroundingQuery{
        variables: select,
        conditions: vec![],
        grounding: SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()}),
        natural_joins: natural_joins,
        theta_joins: IndexSet::new(),
        where_: vec![],
        ids: Ids::None
    })
}


impl GroundingQuery {
    /// returns the variable if the query is for a variable
    fn is_for_a_variable(&self) -> Result<Option<Symbol>, SolverError> {
        if let Some((symbol, column)) = self.variables.first() {
            if self.variables.len() == 1 {
                if let Some(column) = column {
                    if self.natural_joins.len() == 1
                    && self.ids == Ids::All {
                        if let Some(NaturalJoin::Variable(table_name, _)) = self.natural_joins.first() {
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
        Ok(None)
    }
}