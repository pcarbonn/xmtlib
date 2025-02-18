// Copyright Pierre Carbonnelle, 2025.

use itertools::Itertools;
use rusqlite::params_from_iter;

use crate::api::{Identifier, QualIdentifier, XTuple};
use crate::error::SolverError::{self, InternalError};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionIs, Interpretation};
use crate::private::x_query::Ids;
use crate::solver::Solver;


pub(crate) fn interpret_pred(
    identifier: Identifier,
    tuples: Vec<XTuple>,
    _command: String,
    solver: &mut Solver,
 ) -> Result<String, SolverError> {
    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());

    let function_is = solver.functions.get(&qual_identifier)
        .ok_or(SolverError::ExprError("Unknown symbol".to_string(), None))?;

    match function_is {
        FunctionIs::Predefined { .. } =>
            Err(SolverError::ExprError("Can't interpret a pre-defined symbol".to_string(), None)),
        FunctionIs::BooleanInterpreted { .. } =>
            Err(SolverError::ExprError("Can't re-interpret an interpreted symbol".to_string(), None)),
        FunctionIs::Calculated { signature: (domain, _, boolean) } => {
            if ! *boolean {
                Err(SolverError::ExprError("Can't use `x-interpret-pred` for non-boolean symbol".to_string(), None))
            } else {
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

                let mut foreign_keys: Vec<_> = domain.iter().enumerate()
                    .map( |(i, sort)| {
                        match solver.sorts.get(sort) {
                            Some(SortObject::Normal{table, ..}) =>
                                Ok(format!("FOREIGN KEY (a_{i}) REFERENCES {table}(G)")),
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
                        let tuples_t = tuple.iter().map(|t| t.to_string() );  //todo: construct !
                        stmt.execute(params_from_iter(tuples_t))?;
                    } else {
                        return Err(SolverError::ExprError("Incorrect tuple length".to_string(), None))
                    }
                }

                // create TU view
                let table_tu = Interpretation::Table{name: format!("{identifier}_TU"), ids: Ids::All};

                let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_TU AS SELECT *, \"true\" as G from {identifier}_T");
                solver.conn.execute(&sql, ())?;

                // is the domain infinite ?
                let infinite = domain.iter()
                    .any( |sort| {
                        let sort_object = solver.sorts.get(sort);
                        if let Some(sort_object) = sort_object {
                            match sort_object {
                                SortObject::Normal{..} => false,
                                SortObject::Infinite
                                | SortObject::Recursive
                                | SortObject::Unknown => true,
                            }
                        } else {
                            true  // dead code ?
                        }
                    });

                if infinite {
                    let table_uf = Interpretation::Infinite;
                    let table_g = Interpretation::Infinite;

                    // create FunctionIs with boolean interpretations.
                    let function_is = FunctionIs::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);
                } else {
                    // create UF view
                    let table_uf = Interpretation::Table{name: format!("{identifier}_UF"), ids: Ids::All};
                    let columns = domain.iter().enumerate()
                        .map( |(i, sort)| format!("{sort}_{i}.G AS a_{i}"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let joins = domain.iter().enumerate()
                        .map( |(i, sort)| {
                            match solver.sorts.get(sort) {
                                Some(SortObject::Normal{table, ..}) =>
                                    Ok(format!("{table} AS {table}_{i}")),
                                Some(_) => // infinite domain
                                    Ok("".to_string()),
                                None =>
                                    Err(InternalError(658884995))
                            }
                        }).collect::<Result<Vec<_>, _>>()?
                        .join(" JOIN ");
                    let thetas = domain.iter().enumerate()
                        .map( |(i, sort)| format!("{sort}_{i}.G = {identifier}_TU.a_{i}"))
                        .collect::<Vec<_>>()
                        .join(" AND ");
                    let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_UF AS SELECT {columns}, \"false\" as G from {joins} LEFT JOIN {identifier}_TU ON {thetas} WHERE {identifier}_TU.G IS NULL");
                    solver.conn.execute(&sql, ())?;

                    // create G view
                    let  table_g = Interpretation::Table{name: format!("{identifier}_G"), ids: Ids::All};
                    let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_G AS SELECT * FROM {identifier}_TU UNION SELECT * FROM {identifier}_UF");
                    solver.conn.execute(&sql, ())?;

                    // create FunctionIs with boolean interpretations.
                    let function_is = FunctionIs::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);

                }

                Ok(format!("(x-interpret-pred {identifier} {})", tuples.iter().format(" ")))

            }
        },
    }

}