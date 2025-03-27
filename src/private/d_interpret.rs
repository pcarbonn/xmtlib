// Copyright Pierre Carbonnelle, 2025.

use rusqlite::params_from_iter;
use unzip_n::unzip_n;

unzip_n!(pub 3);

use crate::api::{Identifier, QualIdentifier, Sort, XTuple, Term};
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
        FunctionIs::NonBooleanInterpreted { .. } =>
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

                let domain = domain.clone();
                create_interpretation_table(format!("{identifier}_T"), &domain, &None, solver)?;

                // populate the table
                let holes = (0..domain.len()).map(|_|"?").collect::<Vec<_>>().join(",");  // "?" n times
                let stmt = format!("INSERT INTO {identifier}_T VALUES ({holes})");
                let mut stmt = solver.conn.prepare(&stmt)?;
                for XTuple(tuple) in &tuples {
                    if tuple.len() == domain.len() {
                        let tuples_t = tuple.iter()
                            .map(|t| construct(t) )
                            .collect::<Result<Vec<_>, SolverError>>()?;
                        stmt.execute(params_from_iter(tuples_t))?;
                    } else {
                        return Err(SolverError::ExprError("Incorrect tuple length".to_string(), None))
                    }
                }

                // create TU view
                let name_tu = format!("{identifier}_TU");
                let table_tu = Interpretation::Table{name: name_tu.clone(), ids: Ids::All};

                let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_TU AS SELECT *, \"true\" as G from {identifier}_T");
                solver.conn.execute(&sql, ())?;

                let infinite = is_infinite(&domain, &solver);
                if infinite {
                    let table_uf = Interpretation::Infinite;
                    let table_g = Interpretation::Infinite;

                    // create FunctionIs with boolean interpretations.
                    let function_is = FunctionIs::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);
                } else {
                    // create UF view
                    let name_uf = format!("{identifier}_UF");
                    let table_uf = Interpretation::Table{name: name_uf.clone(), ids: Ids::All};

                    // T_1.G as a_1, T as T_1, T_1.G = name.a_1
                    let (columns, joins, thetas) = domain.iter().enumerate()
                        .map( |(i, sort)| {
                            let column = format!("{sort}_{i}.G AS a_{i}");
                            let theta = format!("{sort}_{i}.G = {name_tu}.a_{i}");

                            match solver.sorts.get(sort) {
                                Some(SortObject::Normal{table, ..}) =>
                                    Ok((column, format!("{table} AS {table}_{i}"), theta)),
                                Some(_) => // infinite domain
                                    Ok((column, "".to_string(), theta)),
                                None =>
                                    Err(InternalError(658884995))
                            }
                        }).collect::<Result<Vec<_>, _>>()?.into_iter().unzip_n_vec();
                    let columns = columns.join(", ");
                    let joins = joins.into_iter()
                        .filter(|j| j!="")
                        .collect::<Vec<_>>()
                        .join(" JOIN ");
                    let thetas = thetas.join(" AND ");

                    let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_UF AS SELECT {columns}, \"false\" as G from {joins} LEFT JOIN {name_tu} ON {thetas} WHERE {name_tu}.G IS NULL");
                    solver.conn.execute(&sql, ())?;

                    // create G view
                    let  table_g = Interpretation::Table{name: format!("{identifier}_G"), ids: Ids::All};
                    let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_G AS SELECT * FROM {name_tu} UNION SELECT * FROM {name_uf}");
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


/// Interpret a predicate of arity 0
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

pub(crate) fn interpret_fun(
    identifier: Identifier,
    tuples: Vec<(XTuple, Term)>,
    else_: Term,
    command: String,
    solver: &mut Solver,
)-> Result<String, SolverError> {

    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());

    let function_is = solver.functions.get(&qual_identifier)
        .ok_or(SolverError::ExprError("Unknown symbol".to_string(), None))?;

    match function_is {
        FunctionIs::Predefined { .. } =>
            Err(SolverError::ExprError("Can't interpret a pre-defined symbol".to_string(), None)),
        FunctionIs::BooleanInterpreted { .. } =>
            Err(SolverError::ExprError("Can't re-interpret an interpreted symbol".to_string(), None)),
        FunctionIs::NonBooleanInterpreted { .. } =>
            Err(SolverError::ExprError("Can't re-interpret an interpreted symbol".to_string(), None)),
        FunctionIs::Constructed { .. } =>
            Err(SolverError::ExprError("Can't interpret a constructor".to_string(), None)),
        FunctionIs::Calculated { signature: (domain, co_domain, boolean) } => {
            if ! *boolean {
                if domain.len() == 0 {
                    // special case: arity 0
                    todo!()
                    //return interpret_fun_0(qual_identifier, tuples, else_, command, solver);
                } else {

                    let domain = domain.clone();
                    let co_domain = co_domain.clone();
                    let size = size(&domain, &solver);

                    let suffix = if size == tuples.len() { "G" } else { "K" };
                    let name = format!("{identifier}_{suffix}");
                    create_interpretation_table(name.clone(), &domain, &Some(co_domain), solver)?;

                    // populate the table
                    let holes = (0..(domain.len()+1))  // "?" n+1 times
                        .map(|_|"?")
                        .collect::<Vec<_>>()
                        .join(",");
                    let stmt = format!("INSERT INTO {name} VALUES ({holes})");
                    let mut stmt = solver.conn.prepare(&stmt)?;

                    for (XTuple(tuple), term) in &tuples {
                        if tuple.len() == domain.len() {
                            let mut tuples_t = tuple.iter()
                                .map(|t| construct(t) )
                                .collect::<Result<Vec<_>, SolverError>>()?;
                            // value is an id or an expression
                            let value = construct(term).unwrap_or(term.to_string());
                            tuples_t.push(value);
                            stmt.execute(params_from_iter(tuples_t))?;
                        } else {
                            return Err(SolverError::ExprError("Incorrect tuple length".to_string(), None))
                        }
                    }

                    if size == tuples.len() {
                        // create FunctionIs
                        let  table_g = Interpretation::Table{name, ids: Ids::All};
                        let function_is = FunctionIs::NonBooleanInterpreted { table_g };
                        solver.functions.insert(qual_identifier, function_is);
                    } else {
                        // create G table
                        todo!()
                    }
                }
            } else {
                todo!()
            };
            Ok(command)
        }
    }
}


pub(crate) fn is_infinite(
    domain: &Vec<Sort>,
    solver: &Solver
) -> bool {
    domain.iter()
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
        })
}


pub(crate) fn size(
    domain: &Vec<Sort>,
    solver: &Solver
) -> usize {
    domain.iter()
        .map( |sort| {
            let sort_object = solver.sorts.get(sort);
            if let Some(sort_object) = sort_object {
                match sort_object {
                    SortObject::Normal{count, ..} => count,
                    SortObject::Infinite
                    | SortObject::Recursive
                    | SortObject::Unknown => &0,
                }
            } else {
                unreachable!("7895162")
            }
        }).product()
}


/// Create interpretation table in DB, with foreign keys
/// (boolean if no co_domain)
pub(crate) fn create_interpretation_table(
    name: String,
    domain: &Vec<Sort>,
    co_domain: &Option<Sort>,
    solver: &mut Solver
) -> Result<(), SolverError> {

        // Helper function
        fn column(name: String, sort: &Sort) -> String {
            let sort_name = sort.to_string();
            if sort_name == "Int" {
                format!("{name} INTEGER")
            } else if sort_name == "Real" {
                format!("{name} REAL")
            } else {
                format!("{name} TEXT")
            }
        }

    let (mut columns, foreign_keys): (Vec<String>, Vec<String>) =
        domain.iter().enumerate()
        .map( |(i, sort)| {
            let col = column(format!("a_{i}"), sort);
            match solver.sorts.get(sort) {
                Some(SortObject::Normal{table, ..}) =>
                    Ok((col, format!("FOREIGN KEY (a_{i}) REFERENCES {table}(G)"))),
                Some(_) => // infinite domain
                    Ok((col, "".to_string())),
                None =>
                    Err(InternalError(658884995))
            }
        }).collect::<Result<Vec<(String, String)>, _>>()?
        .into_iter().unzip();
    let mut foreign_keys = foreign_keys.into_iter()
        .filter( |f| f != "")
        .collect();

    // co_domain
    if let Some(sort) = co_domain {
        columns.push(column("G".to_string(), sort))
    }

    // can't have foreign key on G because it can be undefined

    // todo: primary key
    columns.append(&mut foreign_keys);
    let columns = columns.join(", ");

    solver.conn.execute(&format!("CREATE TABLE {name} ({columns})"), ())?;
    Ok(())
}


/// Returns the string representation of the id.
/// Constructor applications are preceded by a space, e.g. ` (cons 0 nil)`
pub(crate) fn construct(id: &Term) -> Result<String, SolverError> {
    match id {
        Term::SpecConstant(_) => Ok(id.to_string()),
        Term::Identifier(_) => Ok(id.to_string()),
        Term::Application(qual_identifier, terms) => {
            let new_terms = terms.iter()
                .map( |t| construct(t))
                .collect::<Result<Vec<_>, SolverError>>()?.join(" ");
            Ok(format!(" ({qual_identifier} {new_terms})"))
        },
        Term::Let(_, _)
        | Term::Forall(_, _)
        | Term::Exists(_, _)
        | Term::Match(_, _)
        | Term::Annotation(_, _)
        | Term::XSortedVar(_, _) =>
            Err(SolverError::ExprError("Invalid id in interpretation".to_string(), None))
    }
}