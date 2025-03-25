// Copyright Pierre Carbonnelle, 2025.

use rusqlite::params_from_iter;

use crate::api::{Identifier, QualIdentifier, XTuple};
use crate::error::SolverError::{self, InternalError};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionIs, Interpretation};
use crate::private::e1_ground_view::Ids;
use crate::solver::Solver;


pub(crate) fn interpret_pred(
    identifier: Identifier,
    tuples: Vec<XTuple>,
    command: String,
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
        FunctionIs::Constructed { .. } =>
            Err(SolverError::ExprError("Can't interpret a constructor".to_string(), None)),
        FunctionIs::Calculated { signature: (domain, _, boolean) } => {
            if ! *boolean {
                Err(SolverError::ExprError("Can't use `x-interpret-pred` for non-boolean symbol".to_string(), None))
            } else {
                if domain.len() == 0 {
                    // special case: arity 0
                    return interpret_pred_0(qual_identifier, tuples, command, solver);
                }
                // create _T table in DB, with foreign keys
                let mut columns = domain.iter().enumerate()
                    .map( |(i, sort)| {
                        let sort_name = sort.to_string();
                        if sort_name == "Int" {
                            format!("a_{i} INTEGER")
                        } else if sort_name == "Real" {
                            format!("a_{i} REAL")
                        } else {
                            format!("a_{i} TEXT")
                        }
                    }).collect::<Vec<String>>();

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

                solver.conn.execute(&format!("CREATE TABLE {identifier}_T ({columns})"), ())?;

                // populate the table
                let holes = (0..domain.len()).map(|_|"?").collect::<Vec<_>>().join(",");  // "?" n times
                let stmt = format!("INSERT INTO {identifier}_T VALUES ({holes})");
                let mut stmt = solver.conn.prepare(&stmt)?;
                // NOTE now
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
                            unreachable!("7895162")
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

                Ok(command)
            }
        },
    }

}

pub(crate) fn interpret_pred_0(
    qual_identifier: QualIdentifier,
    tuples: Vec<XTuple>,
    command: String,
    solver: &mut Solver,
 ) -> Result<String, SolverError> {

    let table_tu = Interpretation::Table{name: format!("{qual_identifier}_TU"), ids: Ids::All};
    let table_uf = Interpretation::Table{name: format!("{qual_identifier}_UF"), ids: Ids::All};
    let table_g  = Interpretation::Table{name: format!("{qual_identifier}_G"), ids: Ids::All};

    if tuples.len() == 0 {  // false
        let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_TU AS SELECT 'false' as G WHERE false");  // empty table
        solver.conn.execute(&sql, ())?;

        let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_UF AS SELECT 'false' as G");
        solver.conn.execute(&sql, ())?;

        let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_G AS SELECT 'false' as G");
        solver.conn.execute(&sql, ())?;

    } else {  // true
        let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_TU AS SELECT 'true' as G");
        solver.conn.execute(&sql, ())?;

        let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_UF AS SELECT 'true' as G WHERE false");  // empty table
        solver.conn.execute(&sql, ())?;

        let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_G AS SELECT 'true' as G");
        solver.conn.execute(&sql, ())?;

    };

    // create FunctionIs with boolean interpretations.
    let function_is = FunctionIs::BooleanInterpreted { table_tu, table_uf, table_g };
    solver.functions.insert(qual_identifier.clone(), function_is);
    Ok(command)
 }