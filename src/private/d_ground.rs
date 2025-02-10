// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;
use itertools::Either::Right;
use rusqlite::Connection;

use crate::api::{Identifier, QualIdentifier, SortedVar, Symbol, Term, VarBinding};
use crate::error::SolverError::{self, *};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, InterpretationType};
use crate::private::x_query::{GroundingQuery, TableName, Column, query_for_compound, query_spec_constant, query_for_aggregate};
use crate::solver::Solver;


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Grounding {
    NonBoolean(GroundingQuery),
    Boolean{tu: GroundingQuery, uf: GroundingQuery, g: GroundingQuery}
}
impl std::fmt::Display for Grounding {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Grounding::NonBoolean(query) => write!(f, " {query}"),
            Grounding::Boolean{tu, uf, g, ..} => {
                writeln!(f, "")?;
                writeln!(f, "    TU: {tu}")?;
                writeln!(f, "    UF: {uf}")?;
                write!  (f, "    G : {g}")
            },
        }
    }
}


/////////////////////  Command (x-ground //////////////////////////////////////

/// ground the pending assertions
pub(crate) fn ground(
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        // extract terms and commands
        let (commands, terms) = solver.assertions_to_ground.iter()
            .map(|(command, term)| (command.clone(), term.clone()))
            .collect::<(Vec<_>, Vec<_>)>();

        for (term, command) in terms.iter().zip(commands) {
            // todo: push and pop, to avoid polluting the SMT state
            yield_!(solver.exec("(push)"));
            yield_!(solver.exec(&command));
            yield_!(solver.exec("(pop)"));

            match ground_term(&term, true, solver) {
                Ok(g) => {
                    match g {
                        Grounding::NonBoolean(_) => yield_!(Err(InternalError(4852956))),
                        Grounding::Boolean{uf, ..} => {
                            // execute the UF query
                            let query = format!("{uf}");
                            match execute_query(query, &mut solver.conn) {
                                Ok(asserts) => {
                                    for assert in asserts {
                                        yield_!(solver.exec(&assert));
                                    }
                                },
                                Err(e) => yield_!(Err(e))
                            }
                        }
                    }
                },
                Err(e) => yield_!(Err(e))
            }
        }

        // reset terms to ground
        solver.assertions_to_ground = vec![];
    })
}


fn execute_query(
    query: String,
    conn: &mut Connection
) -> Result<Vec<String>, SolverError> {
    let mut stmt = conn.prepare(&query)?;
    let row_iter = stmt.query_map([], |row| {
        row.get::<usize, String>(0)
    })?;

    let mut res = vec![];
    for row in row_iter {
        let assert = format!("(assert {})", row?);
        res.push(assert)
    }
    Ok(res)
}


/// Adds the grounding of a term to the solver, if necessary.
/// This function is recursive.
///
/// # Arguments
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction
/// if the term is a universal quantification).
///
fn ground_term(
    term: &Term,
    top_level: bool,
    solver: &mut Solver
) -> Result<Grounding, SolverError> {

    if let Some(grounding) = solver.groundings.get(term) {
        Ok(grounding.clone())
    } else {
        let grounding = ground_term_(term, top_level, solver)?;
        solver.groundings.insert(term.clone(), grounding.clone());
        Ok(grounding)
    }
}

/// Helper function to ground a new term.
///
/// # Arguments:
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction)
///
pub(crate) fn ground_term_(
    term: &Term,
    _top_level: bool,
    solver: &mut Solver
) -> Result<Grounding, SolverError> {

    match term {
        Term::SpecConstant(spec_constant) => {

            // a number or string; cannot be Boolean
            let grounding = query_spec_constant(spec_constant);
            Ok(Grounding::NonBoolean(grounding))
        },
        Term::XSortedVar(..) => {

            // if var is boolean: generate 3 queries
            // else generate 1 query on the type
            // do not generate a view !
            todo!()
        },
        Term::Identifier(qual_identifier) => {

            // an identifier
            ground_compound(qual_identifier, &mut vec![], solver)


            // match qual_identifier {
            //     QualIdentifier::Identifier(identifier) => {
            //         match identifier {
            //             Identifier::Simple(symbol) => {
                            // match variables.get(symbol) {
                            //     None => {

                            //         // a predicate or constant
                            //         ground_application(term, qual_identifier, &vec![], variables, solver)

                            //     },
                            //     Some(SortedVar(_, sort)) => {

                            //         // a variable
                            //         match solver.sorts.get(sort) {
                            //             Some(SortObject::Normal {table_name, ..}) => {
                            //                 // variable `symbol`` in `table_name`
                            //                 // let view = View {
                            //                 //     variables: IndexMap::from([(symbol.clone(), table_name.clone())]),
                            //                 //     condition: "".to_string(),
                            //                 //     grounding: format!("{table_name}.G"),
                            //                 //     joins: IndexMap::from([(table_name.clone(), "".to_string())]),
                            //                 //     where_: "".to_string(),
                            //                 //     group_by: "".to_string(),
                            //                 //     _ids: Ids::All,
                            //                 // };
                            //                 // Ok((term.clone(), Grounding::Function(view)))
                            //                 todo!()
                            //             },
                            //             Some(SortObject::Infinite)
                            //             | Some(SortObject::Recursive)
                            //             | Some(SortObject::Unknown) => {
                            //                 // `symbol` as computed
                            //                 todo!()
                            //             },
                            //             None => { todo!() }
                            //         }
                            //     },
                            // }
            //                 todo!()
            //             },
            //             Identifier::Indexed(..) => todo!()
            //         }
            //     },
            //     QualIdentifier::Sorted(..) => todo!(),
            // }
        },
        Term::Application(qual_identifier, sub_terms) => {

            // a compound term
            ground_compound(qual_identifier, sub_terms, solver)
        },
        Term::Let(..) => todo!(),
        Term::Forall(variables, term, Some(interpreted_vars)) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: _, uf: sub_uf, g: sub_g } => {

                    let mut free_variables = sub_g.variables.clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }
                    for SortedVar(symbol, _) in interpreted_vars {
                        free_variables.shift_remove(symbol);
                    }

                    let index = solver.groundings.len();
                    let table_name = format!("Agg_{index}");
                    let tu = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &variables,
                        "and",
                        "false",
                        TableName{base_table: table_name.clone() + "_TU", index: 0},
                        solver)?;
                    let uf = query_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &variables,
                        "and",
                        "",
                        TableName{base_table: table_name.clone() + "_UF", index: 0},
                        solver)?;
                    let g = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &variables,
                        "and",
                        "",
                        TableName{base_table: table_name.clone() + "_G", index: 0},
                        solver)?;
                    Ok(Grounding::Boolean{tu, uf, g})
                },
            }
        },
        Term::Exists(variables, term, Some(interpreted_vars)) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: _, uf: sub_uf, g: sub_g } => {

                    let mut free_variables = sub_g.variables.clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }
                    for SortedVar(symbol, _) in interpreted_vars {
                        free_variables.shift_remove(symbol);
                    }

                    let index = solver.groundings.len();
                    let table_name = format!("Agg_{index}");
                    let tu = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &variables,
                        "or",
                        "",
                        TableName{base_table: table_name.clone() + "_TU", index: 0},
                        solver)?;
                    let uf = query_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &variables,
                        "or",
                        "true",
                        TableName{base_table: table_name.clone() + "_UF", index: 0},
                        solver)?;
                    let g = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &variables,
                        "or",
                        "",
                        TableName{base_table: table_name.clone() + "_G", index: 0},
                        solver)?;
                    Ok(Grounding::Boolean{tu, uf, g})
                },
            }
        },
        Term::Forall(_, _, None)
        | Term::Exists(_, _, None) => Err(InternalError(95788566)),
        Term::Match(..) => todo!(),
        Term::Annotation(..) => todo!(),
    }
}

// Grounds a compound term
fn ground_compound(
    qual_identifier: &QualIdentifier,
    sub_terms: &Vec<Term>,
    solver: &mut Solver
) -> Result<Grounding, SolverError> {

    // ground sub_terms, creating an entry in solver.groundings if necessary
    let groundings = sub_terms.iter()
        .map( |t| ground_term(t, false, solver))
        .collect::<Result<Vec<_>,_>>()?;

    // collect the full grounding queries
    let mut gqs = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(gq) => gq.clone(),
                Grounding::Boolean{g: gq, ..} => gq.clone()
            })
        .collect::<Vec<_>>();

    match solver.functions.get(qual_identifier) {
        Some(FunctionObject { boolean: None, ..}) => { // ite
            // need to determine if boolean result or not
            todo!("ite not yet supported")
        },
        Some(FunctionObject { boolean: Some(boolean), typ, ..}) => { // custom function
            if *boolean {
                match qual_identifier {
                    QualIdentifier::Identifier(Identifier::Simple(s)) => {
                        match s.0.as_str() {
                            "and" => {

                                // and
                                let (mut tus, mut ufs) = collect_tu_uf(groundings);

                                let variant = Right("apply".to_string());
                                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant)?;

                                let tu = query_for_compound(qual_identifier, &mut tus, &variant)?;

                                // todo: union query(qual_identifer, ufs)
                                let uf = query_for_compound(qual_identifier, &mut ufs, &variant)?;

                                Ok(Grounding::Boolean{tu, uf, g: grounding_query})
                            },
                            "or" => {

                                // or
                                let (mut tus, mut ufs) = collect_tu_uf(groundings);

                                let variant = Right("apply".to_string());
                                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant)?;

                                // todo: union query(qual_identifer, ufs)
                                let tu = query_for_compound(qual_identifier, &mut tus, &variant)?;

                                let uf = query_for_compound(qual_identifier, &mut ufs, &variant)?;

                                Ok(Grounding::Boolean{tu, uf, g: grounding_query})
                            },
                              "not" => {
                                // get tu, uf, g of groundings[0]
                                // return uf, tu, g with grounding G replaced by not(G)
                                todo!()
                              },
                            "=>"
                            | "="
                            | "<="
                            | "<"
                            | ">="
                            | ">" => todo!(),

                            _ => {

                                // custom boolean function with simple name
                                ground_boolean_compound(qual_identifier, groundings, &mut gqs, &typ)
                            }
                        }
                    },
                    QualIdentifier::Identifier(Identifier::Indexed(_,_))
                    | QualIdentifier::Sorted(_, _) => {

                        // custom boolean function with complex identifier
                        ground_boolean_compound(qual_identifier, groundings, &mut gqs, &typ)
                    },
                }

            } else {

                // custom non-boolean function
                let variant =
                    match typ {
                        InterpretationType::Calculated => Right("apply".to_string()),
                        // todo : Constructed
                    };
                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        None => {
            // constructor.  todo: this should not happen once constructors are declared
            // todo: use construct() in SQL
            let variant = Right("construct".to_string());
            let grounding_query = query_for_compound(qual_identifier, &mut vec![], &variant)?;
            Ok(Grounding::NonBoolean(grounding_query))
        },
    }
}


/// Collect the TU (resp. UF) grounding queries in the vector of groundings
fn collect_tu_uf(
    groundings: Vec<Grounding>
) -> (Vec<GroundingQuery>, Vec<GroundingQuery>) {

    // collect the TU grounding queries
    let tus = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(q) => q.clone(),
                Grounding::Boolean{tu: q, ..} => q.clone()
            })
        .collect::<Vec<_>>();

    // collect the UF grounding queries
    let ufs = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(q) => q.clone(),
                Grounding::Boolean{uf: q, ..} => q.clone()
            })
        .collect::<Vec<_>>();

    (tus, ufs)
}

/// grounds a boolean compound term
fn ground_boolean_compound(
    qual_identifier: &QualIdentifier,
    groundings: Vec<Grounding>,
    gqs: &mut Vec<GroundingQuery>,
    typ: &InterpretationType
) -> Result<Grounding, SolverError> {
    // custom boolean function
    match typ {
        InterpretationType::Calculated => {
            let (mut tus, mut ufs) = collect_tu_uf(groundings);
            let variant = Right("apply".to_string());

            let g = query_for_compound(qual_identifier, gqs, &variant)?;

            let tu = query_for_compound(qual_identifier, &mut tus, &variant)?;

            let uf = query_for_compound(qual_identifier, &mut ufs, &variant)?;

            Ok(Grounding::Boolean{tu, uf, g})
        },
    }
}

