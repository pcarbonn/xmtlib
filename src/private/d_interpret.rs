// Copyright Pierre Carbonnelle, 2025.

use rusqlite::params_from_iter;
use unzip_n::unzip_n;

unzip_n!(pub 3);

use crate::api::{Identifier, QualIdentifier, Sort, XTuple, Term, SpecConstant};
use crate::error::SolverError::{self, InternalError};
use crate::solver::Solver;

use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, Interpretation};
use crate::private::e1_ground_view::Ids;
use crate::private::z_utilities::L;


pub(crate) fn interpret_pred(
    identifier: L<Identifier>,
    tuples: Vec<XTuple>,
    command: String,
    solver: &mut Solver,
 ) -> Result<String, SolverError> {
    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());

    let function_is = solver.functions.get(&qual_identifier)
        .ok_or(SolverError::IdentifierError("Unknown symbol", identifier.clone()))?;

    match function_is {
        FunctionObject::Predefined { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a pre-defined symbol", identifier.clone())),
        FunctionObject::BooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier.clone())),
        FunctionObject::NonBooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier.clone())),
        FunctionObject::Constructor { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a constructor", identifier.clone())),
        FunctionObject::NotInterpreted { signature: (domain, _, boolean) } => {
            if ! *boolean {
                Err(SolverError::IdentifierError("Can't use `x-interpret-pred` for non-boolean symbol", identifier.clone()))
            } else {
                if domain.len() == 0 {
                    // special case: arity 0
                    return interpret_pred_0(qual_identifier, tuples, command, solver);
                }

                let domain = domain.clone();
                create_interpretation_table(format!("{identifier}_T"), &domain, &None, solver)?;

                // populate the table
                let mut tuples_strings = vec![];
                for XTuple(tuple) in &tuples {
                    if tuple.len() == domain.len() {
                        let tuples_t = tuple.iter()
                            .map(|t| construct(t, solver) )
                            .collect::<Result<Vec<_>, SolverError>>()?;
                        tuples_strings.push(tuples_t);
                    } else {
                        return Err(SolverError::IdentifierError("Incorrect tuple length", identifier.clone()))
                    }
                }
                populate_table(&format!("{identifier}_T"), tuples_strings, solver)?;

                // create TU view
                let name_tu = format!("{identifier}_TU");
                let table_tu = Interpretation::Table{name: name_tu.clone(), ids: Ids::All, else_: None};

                let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_TU AS SELECT *, \"true\" as G from {identifier}_T");
                solver.conn.execute(&sql, ())?;

                let size = size(&domain, &solver)?;
                if size == 0 {  // infinite
                    let table_uf = Interpretation::Infinite;
                    let table_g = Interpretation::Infinite;

                    // create FunctionObject with boolean interpretations.
                    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);
                } else {
                    // create UF view
                    let name_uf = format!("{identifier}_UF");
                    let table_uf = Interpretation::Table{name: name_uf.clone(), ids: Ids::All, else_: None};

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
                    let  table_g = Interpretation::Table{name: format!("{identifier}_G"), ids: Ids::All, else_: None};
                    let sql = format!("CREATE VIEW IF NOT EXISTS {identifier}_G AS SELECT * FROM {name_tu} UNION SELECT * FROM {name_uf}");
                    solver.conn.execute(&sql, ())?;

                    // create FunctionObject with boolean interpretations.
                    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);

                }

                Ok("".to_string())
            }
        },
    }
}


/// Interpret a predicate of arity 0
fn interpret_pred_0(
    qual_identifier: QualIdentifier,
    tuples: Vec<XTuple>,
    command: String,
    solver: &mut Solver,
) -> Result<String, SolverError> {

    let table_tu = Interpretation::Table{name: format!("{qual_identifier}_TU"), ids: Ids::All, else_: None};
    let table_uf = Interpretation::Table{name: format!("{qual_identifier}_UF"), ids: Ids::All, else_: None};
    let table_g  = Interpretation::Table{name: format!("{qual_identifier}_G"), ids: Ids::All, else_: None};

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

    // create FunctionObject with boolean interpretations.
    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
    solver.functions.insert(qual_identifier.clone(), function_is);
    Ok(command)
}

pub(crate) fn interpret_fun(
    identifier: L<Identifier>,
    tuples: Vec<(XTuple, L<Term>)>,
    else_: Option<L<Term>>,
    _command: String,
    solver: &mut Solver,
)-> Result<String, SolverError> {

    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());

    let function_is = solver.functions.get(&qual_identifier)
        .ok_or(SolverError::IdentifierError("Unknown symbol", identifier.clone()))?;

    match function_is {
        FunctionObject::Predefined { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a pre-defined symbol", identifier.clone())),
        FunctionObject::BooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier.clone())),
        FunctionObject::NonBooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier.clone())),
        FunctionObject::Constructor { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a constructor", identifier.clone())),
        FunctionObject::NotInterpreted { signature: (domain, co_domain, boolean) } => {
            if ! *boolean {
                if domain.len() == 0 {  // constant

                    let value =
                        if tuples.len() == 0 {  // (x-interpret-fun c () 1)
                            else_.clone().ok_or(SolverError::IdentifierError("no values", identifier.clone()))
                        } else if tuples.len() == 1 {   // (x-interpret-fun c (() 1))
                            Ok(tuples[0].1.clone())
                        } else {
                            Err(SolverError::IdentifierError("too many tuples", identifier.clone()))
                        }?;
                    let value = match value {
                        L(Term::SpecConstant(SpecConstant::Numeral(v)), _) => v.to_string(),
                        L(Term::SpecConstant(SpecConstant::Decimal(v)), _) => v.to_string(),
                        _ => format!("\"{}\"", construct(&value, solver)?)
                    };

                    let sql = format!("CREATE VIEW IF NOT EXISTS {qual_identifier}_G AS SELECT {value} as G");
                    solver.conn.execute(&sql, ())?;

                    // create FunctionObject.
                    let table_g  = Interpretation::Table{name: format!("{qual_identifier}_G"), ids: Ids::All, else_: None};
                    let function_is = FunctionObject::NonBooleanInterpreted { table_g };
                    solver.functions.insert(qual_identifier.clone(), function_is);

                } else {

                    let domain = domain.clone();
                    let co_domain = co_domain.clone();
                    let size = size(&domain, &solver)?;

                    let name = format!("{identifier}_G");
                    create_interpretation_table(name.clone(), &domain, &Some(co_domain), solver)?;

                    // populate the table
                    let mut ids = Ids::All;
                    let mut tuples_strings = vec![];
                    for (XTuple(tuple), term) in &tuples {
                        if tuple.len() == domain.len() {
                            let mut tuples_t = tuple.iter()
                                .map(|t| construct(t, solver) )
                                .collect::<Result<Vec<_>, SolverError>>()?;
                            // value is the identifier or an id
                            let value = if term.to_string() == "?" {
                                ids = Ids::Some;
                                format!("({identifier} {})", tuples_t.join(" "))
                            } else {
                                construct(term, solver)?
                            };
                            tuples_t.push(value);
                            tuples_strings.push(tuples_t);
                        } else {
                            return Err(SolverError::IdentifierError("Incorrect tuple length", identifier.clone()))
                        }
                    }
                    populate_table(&name, tuples_strings, solver)?;

                    let table_g = if size == tuples.len() {  // full interpretation
                        if let Some(else_) = else_ {
                            return Err(SolverError::TermError("Unnecessary `else` value", else_.clone()))
                        }
                        Interpretation::Table{name, ids, else_: None}
                    } else if let Some(else_) = else_ {  // incomplete interpretation
                        if else_.to_string() == "?" {
                            Interpretation::Table{name, ids, else_: Some(None)}
                        } else {
                            let _ = construct(&else_, solver)?;  // check that it is an id
                            Interpretation::Table{name, ids, else_: Some(Some(else_))}
                        }
                    } else {
                        return Err(SolverError::IdentifierError("Missing `else` value", identifier.clone()))
                    };
                    let function_is = FunctionObject::NonBooleanInterpreted { table_g };
                    solver.functions.insert(qual_identifier, function_is);
                }
            } else {  // boolean
                todo!()
            };
            Ok("".to_string())
        }
    }
}


// returns the size of the domain (or 0 if infinite)
fn size(
    domain: &Vec<Sort>,
    solver: &Solver
) -> Result<usize, SolverError> {
    domain.iter()
        .map( |sort| {
            let sort_object = solver.sorts.get(sort);
            if let Some(sort_object) = sort_object {
                match sort_object {
                    SortObject::Normal{row_count, ..} => Ok(row_count),
                    SortObject::Infinite
                    | SortObject::Recursive
                    | SortObject::Unknown => Ok(&0),
                }
            } else {
                let id = match sort {
                    Sort::Sort(id)
                    | Sort::Parametric(id, _) => id,
                };
                return Err(SolverError::IdentifierError("Unknown sort", id.clone()));
            }
        }).product()
}


/// Create interpretation table in DB, with foreign keys
/// (boolean if no co_domain)
fn create_interpretation_table(
    name: String,
    domain: &Vec<Sort>,
    co_domain: &Option<Sort>,
    solver: &mut Solver
) -> Result<(), SolverError> {

        // Helper function
        fn column(name: String, sort: &Sort) -> String {
            // LINK src/doc.md#_Infinite
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

    // primary key
    if 0 < domain.len() {
        let primary_key = format!("PRIMARY KEY ({})",
            (0..domain.len())
            .map(|i| format!("a_{i}"))
            .collect::<Vec<_>>().join(", "));
        columns.push(primary_key);
    }

    // can't have foreign key on G because it can be undefined
    columns.append(&mut foreign_keys);
    let columns = columns.join(", ");

    solver.conn.execute(&format!("CREATE TABLE {name} ({columns})"), ())?;
    Ok(())
}


/// Returns the string representation of the id.
/// Constructor applications are preceded by a space, e.g. ` (cons 0 nil)`
// LINK src/doc.md#_Constructor
fn construct(id: &L<Term>, solver: &mut Solver) -> Result<String, SolverError> {
    match id {
        L(Term::SpecConstant(_), _) => Ok(id.to_string()),
        L(Term::Identifier(qual_identifier), _) => {
            if let Some(f_is) = solver.functions.get(qual_identifier) {
                match f_is {
                    FunctionObject::Constructor => Ok(id.to_string()),
                    _ => Err(SolverError::TermError("Not an id", id.clone())),
                }
            } else {
                Err(SolverError::TermError("Invalid id in interpretation", id.clone()))
            }
        },
        L(Term::Application(qual_identifier, terms), _) => {
            if let Some(f_is) = solver.functions.get(qual_identifier) {
                match f_is {
                    FunctionObject::Constructor => {
                        let new_terms = terms.iter()
                            .map( |t| construct(t, solver))
                            .collect::<Result<Vec<_>, SolverError>>()?.join(" ");
                        Ok(format!(" ({qual_identifier} {new_terms})"))
                    },
                    FunctionObject::Predefined { .. }
                    | FunctionObject::NotInterpreted { .. }
                    | FunctionObject::NonBooleanInterpreted { .. }
                    | FunctionObject::BooleanInterpreted { .. } =>
                        Err(SolverError::TermError("Not an id", id.clone())),
                }
            } else {
                Err(SolverError::TermError("Invalid id in interpretation", id.clone()))
            }
        },
        L(Term::Let(_, _), _)
        | L(Term::Forall(_, _), _)
        | L(Term::Exists(_, _), _)
        | L(Term::Match(_, _), _)
        | L(Term::Annotation(_, _), _)
        | L(Term::XSortedVar(_, _), _) =>
            Err(SolverError::TermError("Invalid id in interpretation", id.clone()))
    }
}

fn populate_table(
    name: &String,
    tuples_strings: Vec<Vec<String>>,
    solver: &mut Solver
) -> Result<(), SolverError> {
    if let Some(tuple) = tuples_strings.first() {
        let holes = (0..(tuple.len()))  // "?" n times
            .map(|_|"?")
            .collect::<Vec<_>>()
            .join(",");
        let stmt = format!("INSERT INTO {name} VALUES ({holes})");
        let mut stmt = solver.conn.prepare(&stmt)?;
        for tuples_t in tuples_strings.iter() {
            stmt.execute(params_from_iter(tuples_t))?;
        }
    }
    Ok(())
}