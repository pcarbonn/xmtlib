// Copyright Pierre Carbonnelle, 2025.

use itertools::Either::{self, Left, Right};
use rusqlite::params_from_iter;
use unzip_n::unzip_n;

unzip_n!(pub 4);

use crate::ast::{Identifier, QualIdentifier, Sort, XTuple, XSet, Term, SpecConstant, String_};
use crate::error::SolverError::{self, InternalError};
use crate::solver::Solver;

use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, Interpretation};
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::TableName;
use crate::ast::L;


pub(crate) fn interpret_pred(
    identifier: L<Identifier>,
    tuples: XSet,
    solver: &mut Solver,
) -> Result<String, SolverError> {
    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());
    let table_name = solver.create_table_name(identifier.to_string());

    let function_is = solver.functions.get(&qual_identifier)
        .ok_or(SolverError::IdentifierError("Unknown symbol", identifier.clone()))?;

    match function_is {
        FunctionObject::Predefined { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a pre-defined symbol", identifier)),
        FunctionObject::BooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier)),
        FunctionObject::NonBooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier)),
        FunctionObject::Constructor { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a constructor", identifier)),
        FunctionObject::NotInterpreted { signature: (domain, _, boolean) } => {
            if solver.grounded.contains(&identifier.0) {
                // todo: convert interpretation to definition
                return Err(SolverError::IdentifierError("Can't interpret a symbol after grounding its use", identifier))
            };
            if ! *boolean {
                Err(SolverError::IdentifierError("Can't use `x-interpret-pred` for non-boolean symbol", identifier))
            } else {
                if domain.len() == 0 {
                    // special case: arity 0
                    return interpret_pred_0(qual_identifier, tuples, solver);
                }

                let domain = domain.clone();
                let table_t = TableName(format!("{table_name}_T"));

                // populate the table
                match tuples {
                    XSet::XSet(tuples) => {
                        create_interpretation_table(table_t.clone(), &domain, &None, solver)?;
                        let mut tuples_strings = vec![];
                        for XTuple(tuple) in &tuples {
                            if tuple.len() == domain.len() {
                                let tuples_t = tuple.iter()
                                    .map(|t| construct(t, solver) )
                                    .collect::<Result<Vec<_>, SolverError>>()?;
                                tuples_strings.push(tuples_t);
                            } else {
                                return Err(SolverError::IdentifierError("Incorrect tuple length", identifier))
                            }
                        }
                        populate_table(&table_t, tuples_strings, solver)?;
                    }
                    XSet::XRange(ranges) => {
                        if ranges.len() % 2 == 1 {
                            return Err(SolverError::IdentifierError("Odd number of boundaries in range", identifier))
                        };
                        create_interpretation_table(table_t.clone(), &domain, &None, solver)?;
                        let mut tuples_strings = vec![];
                        for pairs in ranges.chunks(2) {
                            if let L(Term::SpecConstant(SpecConstant::Numeral(a)), _) = &pairs[0] {
                                if let L(Term::SpecConstant(SpecConstant::Numeral(b)), _) = &pairs[1] {
                                    for i in a.0..(b.0+1) {
                                        tuples_strings.push(vec![i.to_string()]);
                                    }
                                } else {
                                    return Err(SolverError::TermError("Expecting an integer", pairs[1].clone()))
                                }
                            } else {
                                return Err(SolverError::TermError("Expecting an integer", pairs[0].clone()))
                            }
                        }
                        populate_table(&table_t, tuples_strings, solver)?;
                    }
                    XSet::XSql(sql) => {
                        let sql = format!("CREATE VIEW {table_t} AS {}", sql.0);
                        solver.conn.execute(&sql, ())?;
                    }
                };

                // create TU view
                let table_tu = TableName(format!("{table_name}_TU"));

                let sql = format!("CREATE VIEW {table_tu} AS SELECT *, \"true\" as G from {table_t}");
                solver.conn.execute(&sql, ())?;

                let size = size(&domain, &solver)?;
                if size == 0 {  // infinite
                    // create FunctionObject with boolean interpretations.
                    let table_tu = Interpretation::Table{name: table_tu.clone(), ids: Ids::All};
                    let table_uf = Interpretation::Infinite;
                    let table_g  = Interpretation::Infinite;
                    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);
                } else {

                    // create UF view
                    let missing = TableName(format!("{table_name}_UF"));
                    let name_g = TableName(format!("{table_name}_G"));

                    create_missing_views(
                        table_tu.clone(),
                        &domain,
                        &Some("false".to_string()),
                        identifier.clone(),
                        &missing,
                        name_g.clone(),
                        solver
                    )?;

                    // create FunctionObject with boolean interpretations.
                    let table_tu = Interpretation::Table{name: table_tu, ids: Ids::All};
                    let table_uf = Interpretation::Table{name: missing,  ids: Ids::All};
                    let  table_g = Interpretation::Table{name: name_g,   ids: Ids::All};
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
    tuples: XSet,
    solver: &mut Solver,
) -> Result<String, SolverError> {
    let table_name = solver.create_table_name(qual_identifier.to_string());

    let table_tu = Interpretation::Table{name: TableName(format!("{table_name}_TU")), ids: Ids::All};
    let table_uf = Interpretation::Table{name: TableName(format!("{table_name}_UF")), ids: Ids::All};
    let table_g  = Interpretation::Table{name: TableName(format!("{table_name}_G")), ids: Ids::All};

    match tuples {
        XSet::XSet(tuples) => {
            if tuples.len() == 0 {  // false
                let sql = format!("CREATE VIEW {table_name}_TU AS SELECT 'false' as G WHERE false");  // empty table
                solver.conn.execute(&sql, ())?;

                let sql = format!("CREATE VIEW {table_name}_UF AS SELECT 'false' as G");
                solver.conn.execute(&sql, ())?;

                let sql = format!("CREATE VIEW {table_name}_G AS SELECT 'false' as G");
                solver.conn.execute(&sql, ())?;

            } else {  // true
                let sql = format!("CREATE VIEW {table_name}_TU AS SELECT 'true' as G");
                solver.conn.execute(&sql, ())?;

                let sql = format!("CREATE VIEW {table_name}_UF AS SELECT 'true' as G WHERE false");  // empty table
                solver.conn.execute(&sql, ())?;

                let sql = format!("CREATE VIEW {table_name}_G AS SELECT 'true' as G");
                solver.conn.execute(&sql, ())?;

            }
        }
        XSet::XRange(_) => unreachable!(),
        XSet::XSql(_)   => unreachable!()
    };

    // create FunctionObject with boolean interpretations.
    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
    solver.functions.insert(qual_identifier.clone(), function_is);
    Ok("".to_string())
}

pub(crate) fn interpret_fun(
    identifier: L<Identifier>,
    tuples: Either<Vec<(XTuple, L<Term>)>, String_>,
    else_: Option<L<Term>>,
    _command: String,
    solver: &mut Solver,
)-> Result<String, SolverError> {
    let table_name = solver.create_table_name(identifier.to_string());

    // get the symbol declaration
    let qual_identifier = QualIdentifier::Identifier(identifier.clone());

    let function_is = solver.functions.get(&qual_identifier)
        .ok_or(SolverError::IdentifierError("Unknown symbol", identifier.clone()))?;

    match function_is {
        FunctionObject::Predefined { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a pre-defined symbol", identifier)),
        FunctionObject::BooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier)),
        FunctionObject::NonBooleanInterpreted { .. } =>
            Err(SolverError::IdentifierError("Can't re-interpret an interpreted symbol", identifier)),
        FunctionObject::Constructor { .. } =>
            Err(SolverError::IdentifierError("Can't interpret a constructor", identifier)),
        FunctionObject::NotInterpreted { signature: (domain, co_domain, boolean) } => {
            if solver.grounded.contains(&identifier.0) {
                // todo: convert interpretation to definition
                return Err(SolverError::IdentifierError("Can't interpret a symbol after grounding its use", identifier))
            };
            if domain.len() == 0 {  // constant
                let value = match tuples {
                    Left(tuples) =>
                        if tuples.len() == 0 {  // (x-interpret-fun c (x-mapping ) 1)
                            else_.clone().ok_or(SolverError::IdentifierError("no values", identifier))?
                        } else if tuples.len() == 1 {   // (x-interpret-fun c (x-mapping () 1))
                            tuples[0].1.clone()
                        } else {
                            return Err(SolverError::IdentifierError("too many tuples", identifier))
                        },
                    Right(_) =>
                        return Err(SolverError::IdentifierError("Can't use x-sql for constants yet", identifier))
                };
                if ! *boolean {
                    let value = match value {
                        L(Term::SpecConstant(SpecConstant::Numeral(v)), _) => v.to_string(),
                        L(Term::SpecConstant(SpecConstant::Decimal(v)), _) => v.to_string(),
                        _ => format!("\"{}\"", construct(&value, solver)?)
                    };

                    let sql = format!("CREATE VIEW {table_name}_G AS SELECT {value} as G");
                    solver.conn.execute(&sql, ())?;

                    // create FunctionObject.
                    let table_g  = Interpretation::Table{name: TableName(format!("{table_name}_G")), ids: Ids::All};
                    let function_is = FunctionObject::NonBooleanInterpreted { table_g };
                    solver.functions.insert(qual_identifier.clone(), function_is);
                } else {
                    let (tu, uf, g) =
                        match value.to_string().as_str() {
                            "true"  => (
                                format!("CREATE VIEW {table_name}_TU AS SELECT \"true\" as G"),
                                format!("CREATE VIEW {table_name}_UF AS SELECT \"true\" as G WHERE FALSE"),
                                format!("CREATE VIEW {table_name}_G AS SELECT \"true\" as G"),
                            ),
                            "false" => (
                                format!("CREATE VIEW {table_name}_TU AS SELECT \"false\" as G WHERE FALSE"),
                                format!("CREATE VIEW {table_name}_UF AS SELECT \"false\" as G"),
                                format!("CREATE VIEW {table_name}_G AS SELECT \"false\" as G"),
                            ),
                            _ => {
                                return Err(SolverError::TermError("Expecting `true` or `false`", value))
                            }
                    };
                    solver.conn.execute(&tu, ())?;
                    solver.conn.execute(&uf, ())?;
                    solver.conn.execute(&g, ())?;

                    // create FunctionObject.
                    let table_tu  = Interpretation::Table{name: TableName(format!("{table_name}_TU")), ids: Ids::All};
                    let table_uf  = Interpretation::Table{name: TableName(format!("{table_name}_UF")), ids: Ids::All};
                    let table_g  = Interpretation::Table{name: TableName(format!("{table_name}_G")), ids: Ids::All};
                    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier.clone(), function_is);
                }
            } else {
                let domain = domain.clone();
                let co_domain = co_domain.clone();
                let size = size(&domain, &solver)?;

                if ! *boolean {

                    let table_g = TableName(format!("{table_name}_G"));

                    // populate the table
                    let mut ids = Ids::All;
                    let count = match tuples {
                        Left(tuples) => {
                            create_interpretation_table(table_g.clone(), &domain, &Some(co_domain), solver)?;
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
                                    return Err(SolverError::IdentifierError("Incorrect tuple length", identifier))
                                }
                            }
                            populate_table(&table_g, tuples_strings, solver)?;
                            tuples.len()
                        },
                        Right(sql) => {
                            let sql = format!("CREATE VIEW {table_g} AS {}", sql.0);
                            solver.conn.execute(&sql, ())?;
                            solver.conn.query_row(
                                format!("SELECT COUNT(*) FROM {table_g}").as_str(),
                                [],
                                |row| row.get(0),
                            )?
                        }
                    };

                    let missing = TableName(format!("{table_name}_U"));
                    if size == count {  // full interpretation
                        if let Some(else_) = else_ {
                            return Err(SolverError::TermError("Unnecessary `else` value", else_.clone()))
                        }
                    } else if let Some(else_) = else_ {  // incomplete interpretation

                        let else_ = if else_.to_string() == "?" {
                            ids = Ids::Some;
                            None
                        } else {
                            Some(construct(&else_, solver)?)
                        };
                        create_missing_views(
                            table_g.clone(),
                            &domain,
                            &else_,
                            identifier.clone(),
                            &missing,
                            table_g.clone(),
                            solver
                        )?;
                    } else {
                        return Err(SolverError::IdentifierError("Missing `else` value", identifier))
                    };

                    let table_g = Interpretation::Table{name: table_g, ids};
                    let function_is = FunctionObject::NonBooleanInterpreted { table_g };
                    solver.functions.insert(qual_identifier, function_is);

                } else {  // partial interpretation of predicate

                    let table_tu = TableName(format!("{table_name}_TU"));
                    let table_uf = TableName(format!("{table_name}_UF"));
                    let table_g  = TableName(format!("{table_name}_G"));

                    // populate the table
                    let mut ids = Ids::All;
                    let count = match tuples {
                        Left(tuples) => {
                            create_interpretation_table(table_tu.clone(), &domain, &Some(co_domain.clone()), solver)?;
                            create_interpretation_table(table_uf.clone(), &domain, &Some(co_domain.clone()), solver)?;
                            create_interpretation_table(table_g .clone(), &domain, &Some(co_domain.clone()), solver)?;
                            let mut tuples_tu = vec![];
                            let mut tuples_uf = vec![];
                            let mut tuples_g  = vec![];
                            for (XTuple(tuple), term) in &tuples {
                                if tuple.len() == domain.len() {
                                    let mut tuples_t = tuple.iter()
                                        .map(|t| construct(t, solver) )
                                        .collect::<Result<Vec<_>, SolverError>>()?;

                                    match term.to_string().as_str() {
                                        "?" => {
                                            ids = Ids::Some;
                                            let value = format!("({identifier} {})", tuples_t.join(" "));
                                            tuples_t.push(value);
                                            tuples_tu.push(tuples_t.clone());
                                            tuples_uf.push(tuples_t.clone());
                                            tuples_g .push(tuples_t);
                                        },
                                        "true" => {
                                            tuples_t.push("true".to_string());
                                            tuples_tu.push(tuples_t.clone());
                                            tuples_g .push(tuples_t);
                                        },
                                        "false" => {
                                            tuples_t.push("false".to_string());
                                            tuples_uf.push(tuples_t.clone());
                                            tuples_g .push(tuples_t);
                                        },
                                        _ => {
                                            return Err(SolverError::TermError("Unexpected value", term.clone()))
                                        }
                                    }
                                } else {
                                    return Err(SolverError::IdentifierError("Incorrect tuple length", identifier))
                                }
                            }
                            populate_table(&table_tu, tuples_tu, solver)?;
                            populate_table(&table_uf, tuples_uf, solver)?;
                            populate_table(&table_g , tuples_g , solver)?;
                            tuples.len()
                        },
                        Right(sql) => {
                            let sql = format!("CREATE VIEW {table_g} AS {}", sql.0);
                            solver.conn.execute(&sql, ())?;
                            let sql = format!("CREATE VIEW {table_tu} AS SELECT FROM {table_g} WHERE G <> \"false\"");
                            solver.conn.execute(&sql, ())?;
                            let sql = format!("CREATE VIEW {table_uf} AS SELECT FROM {table_g} WHERE G <> \"true\"");
                            solver.conn.execute(&sql, ())?;

                            solver.conn.query_row(
                                format!("SELECT COUNT(*) FROM {table_g}").as_str(),
                                [],
                                |row| row.get(0),
                            )?
                        }
                    };

                    if size == count {  // full interpretation
                        if let Some(else_) = else_ {
                            return Err(SolverError::TermError("Unnecessary `else` value", else_.clone()))
                        }
                    } else if let Some(else_) = else_ {  // incomplete interpretation

                        let value = if else_.to_string() == "?" {
                            ids = Ids::Some;
                            None
                        } else {
                            Some(construct(&else_, solver)?)
                        };

                        let missing = TableName(format!("{table_name}_U"));
                        create_missing_views(  // add missing rows to _G
                            table_g.clone(),
                            &domain,
                            &value,
                            identifier.clone(),
                            &missing,
                            table_g.clone(),
                            solver
                        )?;

                        match else_.to_string().as_str() {
                            "?" => { // update TU, UF
                                ids = Ids::Some;
                                add_missing_rows(&table_tu, &missing, solver)?;
                                add_missing_rows(&table_uf, &missing, solver)?;
                            },
                            "true" => { // update TU
                                add_missing_rows(&table_tu, &missing, solver)?;
                            },
                            "false" => { // update UF
                                add_missing_rows(&table_uf, &missing, solver)?;
                            },
                            _ => return Err(SolverError::TermError("Unexpected value", else_))
                            }
                    } else {
                        return Err(SolverError::IdentifierError("Missing `else` value", identifier))
                    };

                    let table_tu = Interpretation::Table{name: table_tu, ids: ids.clone()};
                    let table_uf = Interpretation::Table{name: table_uf, ids: ids.clone()};
                    let table_g  = Interpretation::Table{name: table_g , ids: ids};
                    let function_is = FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g };
                    solver.functions.insert(qual_identifier, function_is);
                }
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


/// Create interpretation table in DB, with foreign keys.
/// Columns are (a_1, .., a_n, G) if co-domain, else (a_1, .., a_n).
fn create_interpretation_table(
    table_name: TableName,
    domain: &Vec<Sort>,
    co_domain: &Option<Sort>,
    solver: &mut Solver
) -> Result<(), SolverError> {

    // Helper function
    let column = |name: String, sort: &Sort| {
        // LINK src/doc.md#_Infinite
        let sort_name = sort.to_string();
        if sort_name == "Int" {
            format!("{name} INTEGER")
        } else if sort_name == "Real" {
            format!("{name} REAL")
        } else {
            format!("{name} TEXT")
        }
    };

    let (mut columns, foreign_keys): (Vec<String>, Vec<String>) =
        domain.iter().enumerate()
        .map( |(i, sort)| {
            let col = column(format!("a_{}", i+1), sort);
            match solver.sorts.get(sort) {
                Some(SortObject::Normal{table, ..}) =>
                    Ok((col, format!("FOREIGN KEY (a_{}) REFERENCES {table}(G)", i+1))),
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
            .map(|i| format!("a_{}", i+1))
            .collect::<Vec<_>>().join(", "));
        columns.push(primary_key);
    }

    // can't have foreign key on G because it can be undefined
    columns.append(&mut foreign_keys);
    let columns = columns.join(", ");

    solver.conn.execute(&format!("CREATE TABLE {table_name} ({columns})"), ())?;
    Ok(())
}


// LINK src/doc.md#_Constructor
/// Returns the string representation of the id.
/// Constructor applications are preceded by a space, e.g. ` (cons 0 nil)`
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
    table_name: &TableName,
    tuples_strings: Vec<Vec<String>>,
    solver: &mut Solver
) -> Result<(), SolverError> {
    if let Some(tuple) = tuples_strings.first() {
        let holes = (0..(tuple.len()))  // "?" n times
            .map(|_|"?")
            .collect::<Vec<_>>()
            .join(",");
        let stmt = format!("INSERT INTO {table_name} VALUES ({holes})");
        let mut stmt = solver.conn.prepare(&stmt)?;

        for tuples_t in tuples_strings.iter() {
            stmt.execute(params_from_iter(tuples_t))?;
        }
    }
    Ok(())
}

/// Create the `missing` and `all` views given the known rows in the `from` table.
/// `all` is the union of `from` and `missing`,
/// and covers the domain of the domain of `identifier`.
/// The `G` column for the missing rows is `value` (either an SMT-lib string or unknown).
/// `from` is renamed to `.._K` if it is the same as `all``.
fn create_missing_views(
    from: TableName,  // table with partial interpretation
    domain: &Vec<Sort>,
    value: &Option<String>,
    identifier: L<Identifier>,
    missing: &TableName,
    all: TableName,
    solver: &mut Solver
) -> Result<(), SolverError> {

    // rename `from` if it is thes same as `all`
    let from = if from == all {
        // replace suffix by `_K`
            let new = TableName(format!("{}_K", from.0.rsplit_once('_').unwrap().0));
            let sql = format!("ALTER TABLE {from} RENAME TO {new}");
            solver.conn.execute(&sql, ())?;
            new
        } else {
            from
        };

    // T_1.G as a_1, T_1.G, T as T_1, T_1.G = from.a_1
    let (columns, args, joins, thetas) = domain.iter().enumerate()
        .map( |(i, sort)| {
            match solver.sorts.get(sort) {
                Some(SortObject::Normal{table, ..}) =>
                    Ok((format!("{table}_{i}.G AS a_{}", i+1),
                        format!("{table}_{i}.G"),
                        format!("{table} AS {table}_{i}"),
                        format!("{table}_{i}.G = {from}.a_{}", i+1))),
                Some(_) => // infinite domain
                    Err(SolverError::IdentifierError("Cannot interpret a symbol with infinite domain", identifier.clone())),
                None =>
                    Err(InternalError(658884995))
            }
        }).collect::<Result<Vec<_>, _>>()?.into_iter().unzip_n_vec();
    let columns = columns.join(", ");
    let args = args.join(", ");
    let joins = joins.into_iter()
        .filter(|j| j!="")
        .collect::<Vec<_>>()
        .join(" JOIN ");
    let thetas = thetas.join(" AND ");

    // create view with missing interpretations
    let value = match value {
        Some(v) => format!("\"{v}\""),
        None => format!("apply(\"{identifier}\", {args})")
    };
    let sql = format!("CREATE VIEW {missing} AS SELECT {columns}, {value} as G from {joins} LEFT JOIN {from} ON {thetas} WHERE {from}.G IS NULL");
    solver.conn.execute(&sql, ())?;

    // create the final view
    let sql = format!("CREATE VIEW {all} AS SELECT * FROM {from} UNION SELECT * FROM {missing}");
    solver.conn.execute(&sql, ())?;
    Ok(())
}

/// Rename `table` to `table_K`, and make `table = table_K + missing``
fn add_missing_rows(
    table: &TableName,  // table with partial interpretation
    missing: &TableName,
    solver: &mut Solver
) -> Result<(), SolverError> {
    let table_k = TableName(format!("{table}_K"));

    let sql = format!("ALTER TABLE {table} RENAME TO {table_k}");
    solver.conn.execute(&sql, ())?;

    let sql = format!("CREATE VIEW {table} AS SELECT * FROM {table_k} UNION SELECT * FROM {missing}");
    solver.conn.execute(&sql, ())?;

    Ok(())
}