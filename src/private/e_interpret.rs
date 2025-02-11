// Copyright Pierre Carbonnelle, 2025.

use itertools::Itertools;
use rusqlite::params_from_iter;

use crate::api::{Identifier, QualIdentifier, XTuple};
use crate::error::SolverError::{self, InternalError};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::FunctionObject;
use crate::private::x_query::Ids;
use crate::solver::Solver;

use super::b_fun::InterpretationType;


pub(crate) fn interpret_pred(
    identifier: Identifier,
    tuples: Vec<XTuple>,
    _command: String,
    solver: &mut Solver,
 ) -> Result<String, SolverError> {
    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());

    let function_object = solver.functions.get_mut(&qual_identifier)
        .ok_or(SolverError::ExprError("Unknown symbol".to_string(), None))?;

    let FunctionObject{signature, boolean, ..} = function_object;


    let boolean = boolean
        .ok_or(SolverError::ExprError("Unknown co_domain of symbol".to_string(), None))?;

    if ! boolean {
        return Err(SolverError::ExprError("Non-boolean symbol".to_string(), None))
    };

    let (domain, _) = signature.clone()
        .ok_or(SolverError::ExprError("Unknown signature of symbol".to_string(), None))?;

    // create _T table in DB, with foreign keys
    let mut columns = domain.iter().enumerate()
        .map( |(i, sort)| {
            match solver.sorts.get(sort) {
                Some(_) => // infinite domain
                    Ok(format!("a_{i} TEXT")),
                None =>
                    Err(InternalError(658884995))
            }
        }).collect::<Result<Vec<_>, _>>()?;

    let mut foreign_keys = domain.iter().enumerate()
        .map( |(i, sort)| {
            match solver.sorts.get(sort) {
                Some(SortObject::Normal{table_name, ..}) =>
                    Ok(format!("FOREIGN KEY (a_{i}) REFERENCES {table_name}(G)")),
                Some(_) => // infinite domain
                    Ok("".to_string()),
                None =>
                    Err(InternalError(658884995))
            }
        }).collect::<Result<Vec<_>, _>>()?
        .into_iter().filter( |f| f != "").collect();

    columns.append(&mut foreign_keys);
    let columns = columns.join(", ");

    solver.conn.execute(format!("CREATE TABLE {identifier}_T ({columns})").as_str(), ())?;

    // populate the table
    let holes = (0..domain.len()).map(|_|"?").collect::<Vec<_>>().join(",");  // "?" n times
    let stmt = format!("INSERT INTO {identifier}_T VALUES ({holes})");
    let mut stmt = solver.conn.prepare(&stmt)?;
    for XTuple(tuple) in &tuples {
        if tuple.len() == domain.len() {
            let tuples_t = tuple.iter().map(|t| format!("{t}"));  //todo: construct !
            stmt.execute(params_from_iter(tuples_t))?;
        } else {
            return Err(SolverError::ExprError("Incorrect tuple length".to_string(), None))
        }
    }

    // create TU view
    let table_tu = format!("{identifier}_TU");
    let table_uf = format!("{identifier}_UF");
    let  table_g = format!("{identifier}_G");

    let sql = format!("CREATE VIEW IF NOT EXISTS {table_tu} AS SELECT *, \"true\" as G from {identifier}_T");
    solver.conn.execute(&sql, ())?;

    // create UF view
    let columns = domain.iter().enumerate()
        .map( |(i, sort)| format!("{sort}_{i}.G AS a_{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let joins = domain.iter().enumerate()
        .map( |(i, sort)| {
            match solver.sorts.get(sort) {
                Some(SortObject::Normal{table_name, ..}) =>
                    Ok(format!("{table_name} AS {table_name}_{i}")),
                Some(_) => // infinite domain
                    Ok("".to_string()),
                None =>
                    Err(InternalError(658884995))
            }
        }).collect::<Result<Vec<_>, _>>()?
        .join(" JOIN ");
    let thetas = domain.iter().enumerate()
        .map( |(i, sort)| format!("{sort}_{i}.G = {table_tu}.a_{i}"))
        .collect::<Vec<_>>()
        .join(" AND ");
    let sql = format!("CREATE VIEW IF NOT EXISTS {table_uf} AS SELECT {columns}, \"false\" as G from {joins} LEFT JOIN {table_tu} ON {thetas} WHERE {table_tu}.G IS NULL");
    solver.conn.execute(&sql, ())?;

    // create G view
    let sql = format!("CREATE VIEW IF NOT EXISTS {table_g} AS SELECT * FROM {table_tu} UNION SELECT * FROM {table_uf}");
    solver.conn.execute(&sql, ())?;


    // create FunctionObject with boolean interpretation, all ids.
    function_object.typ = InterpretationType::Boolean { table_tu, table_uf, table_g, ids: Ids::All };

    Ok(format!("(x-interpret-pred {identifier} {})", tuples.iter().format(" ")))
}