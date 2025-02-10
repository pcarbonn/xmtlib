// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::IndexMap;
use itertools::Either;

use crate::api::{Identifier, QualIdentifier, SortedVar, SpecConstant, Symbol};
use crate::error::SolverError;
use crate::solver::{Solver, TermId};


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TableName {
    pub(crate) base_table: String,
    pub(crate) index: TermId, // to disambiguate
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Column {
    pub(crate) table_name: TableName,
    pub(crate) column: String
}
impl std::fmt::Display for Column {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}.{}", self.table_name, self.column)
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SQLExpr {
    Constant(SpecConstant),
    Construct(QualIdentifier, Box<Vec<SQLExpr>>),  // constructor
    Apply(QualIdentifier, Box<Vec<SQLExpr>>),
    // Only in GroundingQuery.groundings
    Value(Column),  // in an interpretation table.
    Aggregate(String, Box<SQLExpr>),
    Forall(Vec<SortedVar>, Box<SQLExpr>),
    Exists(Vec<SortedVar>, Box<SQLExpr>),
    //  Only in GroundingQuery.conditions
    Equality(bool, Box<SQLExpr>, Column),  // gated c_i.
}

impl SQLExpr {
    fn show(
        &self,
        variables: &IndexMap<Symbol, Column>
    ) -> String {

            /// Helper: use either "apply" or "construct2", according to the first argument.
            /// See description of these functions in y_db module.
            ///
            /// Arguments:
            /// * function: either "apply" or "construct2"
            fn sql_for(
                function: &str,
                qual_identifier: &QualIdentifier,
                exprs: &Box<Vec<SQLExpr>>,
                variables: &IndexMap<Symbol, Column>
            ) -> String {
                if exprs.len() == 0 {
                    format!("\"{qual_identifier}\"")
                } else {
                    let terms = exprs.iter()
                        .map(|e| e.show(variables))
                        .collect::<Vec<_>>().join(", ");
                    format!("{function}(\"{qual_identifier}\", {})", terms)
                }
            }  // end helper

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
            SQLExpr::Construct(qual_identifier, exprs) => {
                sql_for("construct2", qual_identifier, exprs, variables)
            },
            SQLExpr::Apply(qual_identifier, exprs) => {
                sql_for("apply", qual_identifier, exprs, variables)
            },
            SQLExpr::Value(column) => format!("{column}"),
            SQLExpr::Aggregate(function, term) =>
                format!("{function}({})", term.show(variables)),
            SQLExpr::Forall(uninterpreted_variables, expr) => {
                let vars = uninterpreted_variables.iter()
                    .map( |sv| sv.to_string())
                    .collect::<Vec<_>>().join(" ");
                format!("\"(forall ({vars}) \" || {} || \")\"", expr.show(variables))
            },
            SQLExpr::Exists(uninterpreted_variables, expr) => {
                let vars = uninterpreted_variables.iter()
                    .map( |sv| sv.to_string())
                    .collect::<Vec<_>>().join(" ");
                format!("\"(exists ({vars}) \" || {} || \")\"", expr.show(variables))
            },
            SQLExpr::Equality(_, expr, column) => todo!(),
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ids {
    All, // lowest
    Some_,
    None // highest
}


/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GroundingQuery {

    pub(crate) variables: IndexMap<Symbol, Column>,  // maps variables to either a Type table or (better) an Interpretation table
    pub(crate) conditions: Vec<SQLExpr>,  // vector of non-empty SQL expressions
    pub(crate) grounding: SQLExpr,
    pub(crate) natural_joins: IndexMap<TableName, Vec<Symbol>>, // indexed table name -> list of its variables.
    pub(crate) theta_joins: Vec<(TableName, Vec<(bool, SQLExpr, Column)>)>, // indexed table name + mapping of (gated) expressions to value column

    pub(crate) ids: Ids,  // if the groundings are all Ids
}

impl std::fmt::Display for GroundingQuery {

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

        // condition
        let condition = self.conditions.iter()
            .map( |e| {
                format!("({})", e.show(&self.variables))
            })
            .collect::<Vec<_>>().join(" AND ");
        let condition =
            if condition == "" {
                condition
            } else if variables != "" {
                format!(", {condition} AS cond")
            } else {
                format!("{condition} AS cond")
            };

        // grounding
        let grounding = self.grounding.show(&self.variables);
        let grounding =
            if variables =="" && condition == "" {
                format!("{} AS G", grounding)
            } else {
                format!(", {} AS G", grounding)
            };

        // natural joins
        let naturals = self.natural_joins.iter()
            .map(|(table_name, on)| {
                let name = if table_name.index == 0 {
                        format!("{}", table_name.base_table)
                    } else {
                        format!("{} AS {table_name}", table_name.base_table)
                    };
                let on = on.iter()
                    .map( | symbol | {
                        let column = self.variables.get(symbol).unwrap();
                        let this_column = Column{table_name: table_name.clone(), column: symbol.to_string()};
                        if this_column == *column {
                            "".to_string()
                        } else {
                            format!(" {this_column} = {column}")
                        }
                    })
                    .filter( |cond| cond != "" )
                    .collect::<Vec<_>>().join(" AND ");
                let on = if on == "" { on } else { format!(" ON {on}")};

                format!("{name}{on}")
            })
            .collect::<Vec<_>>();

        // theta joins
        let thetas = self.theta_joins.iter()
            .map( | (table_name, mapping) | {
                let on = mapping.iter()
                    .map( | (gated, e, col) | {
                        let value = e.show(&self.variables);
                        if col.to_string() == value {
                            "".to_string()
                        } else {
                            let gate = if *gated {
                                    // todo add to condition too !
                                    format!("NOT(is_id({})) OR ", e.show(&self.variables))
                                } else {
                                    "".to_string()
                                };
                            format!(" ({gate}{col} = {value}) ")
                        }
                    }).filter( |s| s != "" )
                    .collect::<Vec<_>>().join(" AND ");
                let on = if on == "" { on } else { format!(" ON {on}")};

                format!("{} AS {table_name}{on}", table_name.base_table)
            }).collect::<Vec<_>>();

        // naturals + thetas
        let tables = [naturals, thetas].concat();
        let tables = if 0 < tables.len() {
                format!(" FROM {}", tables.join(" JOIN "))
            } else { "".to_string() };

        // todo: replace `on` by `where` if only one table
        write!(f, "SELECT {variables}{condition}{grounding}{tables}")
    }
}


/////////////////////  Grounding implementations ////////////////////////////////////////

pub(crate) fn query_spec_constant(
    spec_constant: &SpecConstant
) -> GroundingQuery {
    GroundingQuery {
        variables: IndexMap::new(),
        conditions: vec![],
        grounding: SQLExpr::Constant(spec_constant.clone()),
        natural_joins: IndexMap::new(),
        theta_joins: vec![],
        ids: Ids::All,
    }
}

/// creates a query for a compound term, according to `variant`.
///
/// Arguments:
/// * variant: either an interpretation or a function name.  The function name can be:
///     * "apply"
///     * "construct"
pub(crate) fn query_for_compound(
    qual_identifier: &QualIdentifier,
    sub_queries: &mut Vec<GroundingQuery>,
    variant: &Either<TableName, String>
) -> Result<GroundingQuery, SolverError> {

    let mut variables: IndexMap<Symbol, Column> = IndexMap::new();
    let mut conditions= vec![];
    let mut groundings = vec![];
    let mut natural_joins: IndexMap<TableName, Vec<Symbol>> = IndexMap::new();
    let mut theta_joins = vec![];
    let mut ids: Ids = Ids::All;

    for sub_q in sub_queries {

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
                Some(old_column) => {
                    if natural_joins.contains_key(&old_column.table_name)
                    && ! sub_q.natural_joins.contains_key(&column.table_name) {
                        // todo remove natural join
                        variables.insert(symbol.clone(), column.clone());
                    } else {

                    }
                }
            }
        }
    };

    let grounding =
        match variant {
            Either::Left(_) => todo!(), // todo: use interpretation table of qual_identifier
            Either::Right(function) => {  // no interpretation
                match function.as_str() {
                    "construct" => SQLExpr::Construct(qual_identifier.clone(), Box::new(groundings)),
                    "apply" => SQLExpr::Apply(qual_identifier.clone(), Box::new(groundings)),
                    _ => return Err(SolverError::InternalError(62479519))
                }
            },
        };

    Ok(GroundingQuery {
        variables,
        conditions,
        grounding,
        natural_joins,
        theta_joins,
        ids,
    })
}



/// Creates a query over an aggregate view, possibly adding a where clause if exclude is not empty
pub(crate) fn query_for_aggregate(
    sub_query: &GroundingQuery,
    free_variables: &IndexMap<Symbol, Column>,
    variables: &Vec<SortedVar>,  // variables that are aggregated over infinite sort
    agg: &str,
    exclude: &str,
    table_name: TableName,
    solver: &mut Solver
) -> Result<GroundingQuery, SolverError> {

    // create sql of the view, using a GroundingQuery
    let mut view = sub_query.clone();

    view.variables = free_variables.clone();

    if 0 < sub_query.conditions.len() {
        let imply = QualIdentifier::Identifier(Identifier::Simple(Symbol("=>".to_string())));
        view.conditions.push(view.grounding);
        view.grounding = SQLExpr::Apply(imply, Box::new(view.conditions));
        view.conditions = vec![];
    }
    view.grounding = SQLExpr::Aggregate(format!("{agg}_aggregate"), Box::new(view.grounding));
    if 0 < variables.len() {  // add (forall {vars} {grounding})
        if agg == "and".to_string() {
            view.grounding = SQLExpr::Forall(variables.clone(), Box::new(view.grounding))
        } else {
            view.grounding = SQLExpr::Exists(variables.clone(), Box::new(view.grounding))
        }
    }

    let group_by = free_variables.iter()
        .map( |(_, column)| format!("{column}") )
        .collect::<Vec<_>>().join(", ");
    let group_by = if group_by == "" { group_by } else {
        format!(" GROUP BY {group_by}")
    };

    let sql = format!("CREATE VIEW IF NOT EXISTS {table_name} AS {view}{group_by}");
    solver.conn.execute(&sql, ())?;

    // construct the GroundingQuery
    // select {free_variables}, {table_name}.G from {table_name}
    let select = free_variables.iter()
        .map( |(symbol, _)|
            (symbol.clone(), Column{table_name: table_name.clone(), column: format!("{symbol}")}))
        .collect::<IndexMap<Symbol, Column>>();

    let natural_joins = IndexMap::from([(table_name.clone(), free_variables.keys().cloned().collect())]);

    //todo add exclude
    Ok(GroundingQuery{
        variables: select,
        conditions: vec![],
        grounding: SQLExpr::Value(Column{table_name: table_name.clone(), column: "G".to_string()}),
        natural_joins: natural_joins,
        theta_joins: vec![],
        ids: Ids::None
    })
}