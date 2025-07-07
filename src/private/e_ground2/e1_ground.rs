
// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use rusqlite::Connection;
use indexmap::IndexSet;

use crate::ast::{Identifier, QualIdentifier, Sort, Symbol, Term, L};
use crate::error::{Offset, SolverError::{self, *}};
use crate::solver::{Backend, CanonicalSort, Solver};

use crate::private::b_fun::{FunctionObject, get_function_object};
use crate::private::d_interpret::convert_to_definition;
use crate::private::e_ground2::e3_query::GroundingQuery;
use crate::private::e_ground2::e2_generator::{Generator, prepare_generators};

/////////////////////// Data model ///////////////////////////////////

#[derive(Debug, strum_macros::Display, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ViewType {
    #[strum(to_string = "TU")] TU,
    #[strum(to_string = "UF")] UF,
    #[strum(to_string = "G")] G,
}


/////////////////////  Command (x-ground //////////////////////////////////////

/// ground the pending assertions
pub(crate) fn ground(
    no: bool,
    debug: bool,
    sql: bool,
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        // update statistics in DB
        solver.conn.execute("ANALYZE", []).unwrap();

        let mut terms = vec![];  // for concatenation
        let mut grounded = vec![];
        for term in solver.assertions_to_ground.clone() {
            if no {
                let assert = format!("(assert {term})\n");
                yield_!(solver.exec(&assert));
            } else {
                match has_interpreted_function(&term, &mut grounded, solver) {
                    Ok( (_, has) ) => {
                        if ! has && ! debug {  // no interpretation
                            let assert = format!("(assert {})\n", &term);
                            yield_!(solver.exec(&assert));
                        } else if debug {  // execute immediately
                            for result in execute_term(term, sql, solver) {
                                yield_!(result)
                            }
                            yield_!(Ok("\n".to_string()))
                        } else {  // conjoin with other terms
                            terms.push(term.clone())
                        }
                    }
                    Err(e) => yield_!(Err(e))
                }
            }
        }
        for identifier in grounded.into_iter() {
            solver.grounded.insert(identifier);
        }

        // faster, because it gives sqlite more scope for optimisation
        if 0 < terms.len() {
            let and_ = QualIdentifier::new(&Symbol("and".to_string()), None);
            let term = L(Term::Application(and_, terms), Offset(0));

            for result in execute_term(term, sql, solver) {
                yield_!(result)
            }
        }
    })
}


/// Determine if a term uses a function that is interpreted in the solver.
///
/// Arguments:
///
/// * grounded: returned list of uninterpreted symbols occurring in the term
///
fn has_interpreted_function(
    term: &L<Term>,
    not_interpreted: &mut Vec<Identifier>,
    solver: &mut Solver
) -> Result<(CanonicalSort, bool), SolverError> {

    /// returns true if the function is interpreted.
    /// Add it to not_interpreted if not interpreted.
    fn analyze_function(
        function: &QualIdentifier,
        function_object: &FunctionObject,
        not_interpreted: &mut Vec<Identifier>
    ) -> Result<bool, SolverError> {
        match function_object {
            FunctionObject::Predefined { .. }
            | FunctionObject::Constructor => Ok(false),

            FunctionObject::NotInterpreted => {
                if let QualIdentifier::Identifier(L(function, _)) = function {
                    not_interpreted.push(function.clone());
                    Ok(false)
                } else {
                    return Err(SolverError::InternalError(6875596))
                }
            },

            FunctionObject::Interpreted(_)
            | FunctionObject::BooleanInterpreted { .. } => {
                Ok(true)
            },
        }
    }

    let L(term_, _) = term;
    match term_ {
        Term::SpecConstant(spec_constant) => Ok( (spec_constant.to_canonical_sort(), false) ),

        Term::Identifier(function) => {
            let (sort, function_object) =  get_function_object(term, function, &vec![], &solver)?;
            let sort = sort.clone();
            let interpreted = analyze_function(function, function_object, not_interpreted)?;
            Ok( (sort, interpreted) )
        },
        Term::Application(function, ls) => {
            let (sorts, interpreteds): (Vec<_>, Vec<_>) = ls.iter()
                            .map( |term| has_interpreted_function(term, not_interpreted, solver))
                            .collect::<Result<Vec<(_,_)>,_>>()?
                            .into_iter().unzip();
            let (sort, function_object) =  get_function_object(term, function, &sorts, &solver)?;
            let sort = sort.clone();
            let interpreted = interpreteds.iter().any(|b| *b)
                || analyze_function(function, function_object, not_interpreted)?;
            Ok( (sort, interpreted) )
        },
        Term::Let(_, l) => has_interpreted_function(l, not_interpreted, solver),
        Term::Forall(_, l) => has_interpreted_function(l, not_interpreted, solver),
        Term::Exists(_, l) => has_interpreted_function(l, not_interpreted, solver),
        Term::Match(l, _) => has_interpreted_function(l, not_interpreted, solver), // TODO
        Term::Annotation(l, _) => has_interpreted_function(l, not_interpreted, solver),
        Term::XSortedVar(_, sort, _) => {
            let canonical = solver.canonical_sorts.get(sort)
                .ok_or(InternalError(1458856))?
                .clone();
            Ok( (canonical, false) )
        },
        Term::XLetVar(_, l) => has_interpreted_function(l, not_interpreted, solver),
    }
}

/// # Arguments
///
/// * sql: true if the query should be returned as string
fn execute_term(
    term: L<Term>,
    sql: bool,
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        match prepare_generators(&term, solver) {
            Ok(_) => {},
            Err(e) => yield_!(Err(e))
        };
        let mut to_be_defined : &mut IndexSet<L<Identifier>> = &mut IndexSet::new();
        match ground_term(&term, true, ViewType::UF, Generator::Empty, to_be_defined, solver) {
            Ok((query, _)) => {
                if sql {
                    yield_!(Ok("; ==== Query =============================\n;".to_string()));
                    let temp = query.to_sql("");
                    yield_!(Ok(temp.replace("\n", "\n;")))
                }
                for res in execute_query(query, &mut solver.conn, &mut solver.backend) {
                    solver.started = true;
                    yield_!(res)
                }
                for identifier in to_be_defined.iter() {
                    yield_!(convert_to_definition(identifier, solver))
                }
            },
            Err(e) => yield_!(Err(e))
        }
    })
}


/// Computes the grounding query of a term.
/// This function is recursive.
///
/// # Arguments
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction
/// if the term is a universal quantification).
///
/// * to_be_defined: set of identifiers for which a definition must be created
///
fn ground_term(
    term: &L<Term>,
    top_level: bool,
    view_type: ViewType,
    generator: Generator,
    to_be_defined: &mut IndexSet<L<Identifier>>,
    solver: &mut Solver
) -> Result<(GroundingQuery, CanonicalSort), SolverError> {

    Ok((GroundingQuery::Todo("SELECT \"true\"".to_string()), CanonicalSort(Sort::Sort(L(Identifier::Simple(Symbol("Bool".to_string())), Offset(0))))))
    // match term {
    //     L(Term::SpecConstant(spec_constant), _) => {

    //         // a number or string; cannot be Boolean
    //         let grounding = view_for_constant(spec_constant)?;
    //         let canonical = spec_constant.to_canonical_sort();
    //         Ok((Grounding::NonBoolean(grounding), canonical))
    //     },
    //     L(Term::XSortedVar(symbol, sort, sorted_object), _) => {

    //         // a regular variable
    //         let base_table =
    //             match sorted_object {
    //                 SortObject::Normal{table, ..} => Some(table.clone()),
    //                 SortObject::Recursive
    //                 | SortObject::Infinite
    //                 | SortObject::Unknown => None,
    //             };

    //         let index = solver.groundings.len();
    //         let g = view_for_variable(symbol, base_table, index)?;

    //         let canonical = solver.canonical_sorts.get(sort)
    //             .ok_or(InternalError(1458856))?
    //             .clone();
    //         if sort.to_string() == "bool" {
    //             Ok((Grounding::Boolean { tu: g.clone(), uf: g.clone(), g }, canonical))
    //         } else {
    //             Ok((Grounding::NonBoolean(g), canonical))
    //         }
    //     },
    //     L(Term::XLetVar(_, _), _) => {
    //         todo!()
    //     }
    //     L(Term::Identifier(qual_identifier), _) => {

    //         // an identifier
    //         ground_compound(term, qual_identifier, &mut vec![], false, solver)
    //     },
    //     L(Term::Application(qual_identifier, sub_terms), _) => {

    //         // a compound term
    //         ground_compound(term, qual_identifier, sub_terms, top_level, solver)
    //     },
    //     L(Term::Let(..), _) => todo!(),
    //     L(Term::Forall(variables, term), _) => {
    //         match ground_term(term, false, solver)? {
    //             (Grounding::NonBoolean(_), _) =>
    //                 Err(InternalError(42578548)),
    //             (Grounding::Boolean { tu: _, uf: sub_uf, g: _ }, canonical) => {

    //                 let index = solver.groundings.len();
    //                 let table_name = TableName(format!("Agg_{index}"));

    //                 let (free_variables, infinite_variables) = sub_uf.get_free_variables(variables).clone();

    //                 let tu = view_for_aggregate(
    //                     &sub_uf,
    //                     &free_variables,
    //                     &infinite_variables,
    //                     "and",
    //                     Some(true),
    //                     Some(false),
    //                     true,
    //                     TableAlias{base_table: TableName(format!("{table_name}_TU")), index: 0})?;

    //                 let uf = view_for_aggregate(
    //                     &sub_uf,
    //                     &free_variables,
    //                     &infinite_variables,
    //                     if top_level { "" } else { "and" },
    //                     None,
    //                     None,
    //                     false,
    //                     TableAlias{base_table: TableName(format!("{table_name}_UF")), index: 0})?;

    //                 let g = view_for_aggregate(
    //                     &sub_uf,
    //                     &free_variables,
    //                     &infinite_variables,
    //                     "and",
    //                     Some(true),
    //                     None,
    //                     true,
    //                     TableAlias{base_table: TableName(format!("{table_name}_G")), index: 0})?;

    //                 Ok((Grounding::Boolean{tu, uf, g}, canonical))
    //             },
    //         }
    //     },
    //     L(Term::Exists(variables, term), _) => {
    //         match ground_term(term, false, solver)? {
    //             (Grounding::NonBoolean(_), _) =>
    //                 Err(InternalError(42578548)),
    //             (Grounding::Boolean { tu: sub_tu, uf: _, g: _ }, canonical) => {

    //                 let index = solver.groundings.len();
    //                 let table_name = TableName(format!("Agg_{index}"));

    //                 let (free_variables, infinite_variables) = sub_tu.get_free_variables(variables).clone();

    //                 let tu = view_for_aggregate(
    //                     &sub_tu,
    //                     &free_variables,
    //                     &infinite_variables,
    //                     "or",
    //                     None,
    //                     None,
    //                     false,
    //                     TableAlias{base_table: TableName(format!("{table_name}_TU")), index: 0})?;

    //                 let uf = view_for_aggregate(
    //                     &sub_tu,
    //                     &free_variables,
    //                     &infinite_variables,
    //                     "or",
    //                     Some(false),
    //                     Some(true),
    //                     true,
    //                     TableAlias{base_table: TableName(format!("{table_name}_UF")), index: 0})?;

    //                 let g = view_for_aggregate(
    //                     &sub_tu,
    //                     &free_variables,
    //                     &infinite_variables,
    //                     "or",
    //                     Some(false),
    //                     None,
    //                     true,
    //                     TableAlias{base_table: TableName(format!("{table_name}_G")), index: 0})?;
    //                 Ok((Grounding::Boolean{tu, uf, g}, canonical))
    //             },
    //         }
    //     },
    //     L(Term::Match(..), _) => todo!(),
    //     L(Term::Annotation(..), _) => todo!(),
    // }
}


fn execute_query<'a>(
    query: GroundingQuery,
    conn: &'a mut Connection,
    backend: &'a mut Backend
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + 'a> {

    gen!({
        let query = query.to_sql("");
        let mut stmt = match conn.prepare(&query) {
            Ok(stmt) => stmt,
            Err(e) => {
                yield_!(Err(SolverError::from(e)));
                return;
            }
        };
        if stmt.column_count() == 1 {  //  just G
            match stmt.query_map([], |row| {
                        row.get::<usize, String>(0)
                    }) {
                Ok(row_iter) => {
                    for row in row_iter {
                        match row {
                            Ok(g) => {
                                if g != "true" {
                                    let assert = format!("(assert {g})\n");
                                    yield_!(backend.exec(&assert));
                                    if g == "false" {  // theory is unsatisfiable anyway
                                        break
                                    }
                                }
                            }
                            Err(e) => yield_!(Err(SolverError::from(e)))
                        }
                    }
                }
                Err(e) => yield_!(Err(SolverError::from(e)))
            };
        } else if stmt.column_count() == 2 {  // with an if_ column
            match stmt.query_map([], |row| {
                        row.get::<usize, String>(0).and_then(|col0| {
                            row.get::<usize, String>(1).map(|col1| (col0, col1))
                        })
                    }) {
                Ok(row_iter) => {
                    for row in row_iter {
                        match row {
                            Ok((if_, g)) => {
                                if if_ == "" || if_ == "true" {
                                    if g != "true" {
                                        let assert = format!("(assert {g})\n");
                                        yield_!(backend.exec(&assert));
                                        if g == "false" {  // theory is unsatisfiable anyway
                                            break
                                        }
                                    }
                                } else {
                                    let assert = format!("(assert (=> {if_} {g}))\n");
                                    yield_!(backend.exec(&assert));
                                }
                            }
                            Err(e) => {
                                yield_!(Err(SolverError::from(e)));
                                break
                            }
                        }
                    }
                }
                Err(e) => yield_!(Err(SolverError::from(e)))
            };
        } else {
            unreachable!()
        }
    })
}

