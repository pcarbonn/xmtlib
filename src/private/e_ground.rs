// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use rusqlite::Connection;

use crate::api::{QualIdentifier, SortedVar, Term};
use crate::error::SolverError::{self, *};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, Interpretation};
use crate::private::e1_ground_view::{GroundingView, Ids, ViewType, QueryVariant,
    query_for_constant, query_for_variable, query_for_compound, query_for_aggregate, query_for_union};
use crate::private::e2_ground_query::TableAlias;
use crate::solver::{Solver, Backend};


/////////////////////  Data structure for Grounding  //////////////////////////


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Grounding {
    NonBoolean(GroundingView),
    Boolean{tu: GroundingView, uf: GroundingView, g: GroundingView}
}
impl std::fmt::Display for Grounding {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Grounding::NonBoolean(query) => write!(f, " {query}"),
            Grounding::Boolean{tu, uf, g, ..} => {
                writeln!(f, "")?;
                if tu.get_ids() == Ids::All {
                    writeln!(f, "    T: {tu}")?;
                } else {
                    writeln!(f, "    TU: {tu}")?;
                }
                if uf.get_ids() == Ids::All {
                    writeln!(f, "    F: {uf}")?;
                } else {
                    writeln!(f, "    UF: {uf}")?;
                }
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
        // update statistics in DB
        solver.conn.execute("ANALYZE", []).unwrap();

        // extract terms and commands
        let (commands, terms) = solver.assertions_to_ground.iter()
            .map(|(command, term)| (command.clone(), term.clone()))
            .collect::<(Vec<_>, Vec<_>)>();

        for (term, command) in terms.iter().zip(commands) {
            if solver.backend != Backend::NoDriver {
                // push and pop, to avoid polluting the SMT state
                yield_!(solver.exec("(push)"));
                yield_!(solver.exec(&command));
                yield_!(solver.exec("(pop)"));
            }

            match ground_term(&term, true, solver) {
                Ok(g) => {
                    match g {
                        Grounding::NonBoolean(_) => yield_!(Err(InternalError(4852956))),
                        Grounding::Boolean{uf, ..} => {
                            // execute the UF query
                            let query = uf.to_string();
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
        match row {
            Err(e) => return Err(SolverError::from(e)),
            Ok(row) => {
                if row != "true" {
                    let assert = format!("(assert {})\n", row);
                    res.push(assert);
                    if row == "false" {
                        break
                    }
                }
            }
        }
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
    top_level: bool,
    solver: &mut Solver
) -> Result<Grounding, SolverError> {

    let index = solver.groundings.len();
    match term {
        Term::SpecConstant(spec_constant, _) => {

            // a number or string; cannot be Boolean
            let grounding = query_for_constant(spec_constant, solver)?;
            Ok(Grounding::NonBoolean(grounding))
        },
        Term::XSortedVar(symbol, sort, _) => {

            // a variable
            let base_table = if let Some(sort) = sort {  // finite domain
                    sort.to_string()
                } else {
                    "".to_string()
                };

            let g = query_for_variable(symbol, &base_table, index, solver)?;

            if base_table == "bool" {
                Ok(Grounding::Boolean { tu: g.clone(), uf: g.clone(), g })
            } else {
                Ok(Grounding::NonBoolean(g))
            }
        },
        Term::Identifier(qual_identifier, _) => {

            // an identifier
            ground_compound(qual_identifier, &mut vec![], solver)
        },
        Term::Application(qual_identifier, sub_terms, _) => {

            // a compound term
            ground_compound(qual_identifier, sub_terms, solver)
        },
        Term::Let(..) => todo!(),
        Term::Forall(variables, term, _) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: _, uf: sub_uf, g: sub_g } => {

                    // free_variables = query.variables \ variables
                    let mut free_variables = sub_g.get_free_variables().clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }

                    // infinite_variables < variables
                    let infinite_variables = variables.iter()
                        .filter( |SortedVar(_, sort)|
                            match solver.sorts.get(sort).unwrap() {
                                SortObject::Normal { .. } => false,
                                SortObject::Recursive
                                | SortObject::Infinite
                                | SortObject::Unknown => true
                        }).map(|var| var.clone()).collect::<Vec<_>>();

                    let table_name = format!("Agg_{index}");

                    let tu = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "and",
                        Some(false),
                        TableAlias{base_table: table_name.clone() + "_TU", index: 0},
                        solver)?;

                    let uf = query_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &infinite_variables,
                        if top_level { "" } else { "and" },
                        None,
                        TableAlias{base_table: table_name.clone() + "_UF", index: 0},
                        solver)?;

                    let g = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "and",
                        None,
                        TableAlias{base_table: table_name.clone() + "_G", index: 0},
                        solver)?;
                    Ok(Grounding::Boolean{tu, uf, g})
                },
            }
        },
        Term::Exists(variables, term, _) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: sub_tu, uf: _, g: sub_g } => {

                    // free_variables = query.variables \ variables
                    let mut free_variables = sub_g.get_free_variables().clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }

                    // infinite_variables < variables
                    let infinite_variables = variables.iter()
                    .filter( |SortedVar(_, sort)|
                        match solver.sorts.get(sort).unwrap() {
                            SortObject::Normal { .. } => false,
                            SortObject::Recursive
                            | SortObject::Infinite
                            | SortObject::Unknown => true
                    }).map(|var| var.clone()).collect::<Vec<_>>();

                    let table_name = format!("Agg_{index}");
                    let tu = query_for_aggregate(
                        &sub_tu,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        None,
                        TableAlias{base_table: table_name.clone() + "_TU", index: 0},
                        solver)?;

                    let uf = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        Some(true),
                        TableAlias{base_table: table_name.clone() + "_UF", index: 0},
                        solver)?;

                    let g = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        None,
                        TableAlias{base_table: table_name.clone() + "_G", index: 0},
                        solver)?;
                    Ok(Grounding::Boolean{tu, uf, g})
                },
            }
        },
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

    let index = solver.groundings.len();

    // collect the full grounding queries
    let mut gqs = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(gq) => gq.clone(),
                Grounding::Boolean{g: gq, ..} => gq.clone()
            })
        .collect::<Vec<_>>();

    let function_is = match solver.functions.get(qual_identifier) {
        Some(f) => f,
        None => unreachable!()
    };

    match function_is {
        FunctionObject::Predefined { boolean: None } => { // ite
            // need to determine if boolean result or not
            todo!("ite not yet supported")
        },
        FunctionObject::Predefined { boolean: Some(boolean) } => {
            let variant = QueryVariant::Predefined;
            if *boolean {
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);

                match qual_identifier.to_string().as_str() {
                    "and" => {

                        let tu = query_for_compound(qual_identifier, index, &mut tus, &variant, Some(false), solver)?;

                        let uf = query_for_union(ufs, Some(true), "and".to_string(), index, solver)?;

                        let g = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})
                    }
                    "or" => {

                        let tu = query_for_union(tus, Some(false), "or".to_string(), index, solver)?;

                        let uf = query_for_compound(qual_identifier, index, &mut ufs, &variant, Some(true), solver)?;

                        let g = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})

                    }
                    "not" => {
                        // return uf, tu, g with grounding G replaced by not(G)
                        match groundings.get(0) {
                            Some(Grounding::Boolean { tu, uf, g }) => {
                                if let GroundingView::View { .. } = g {
                                    // switch uf and tu and negate the groundings
                                    let new_tu = uf.negate(index, ViewType::UF, solver)?;
                                    let new_uf = tu.negate(index, ViewType::TU, solver)?;
                                    let new_g = g.negate(index, ViewType::G, solver)?;

                                    Ok(Grounding::Boolean{tu: new_tu, uf: new_uf, g: new_g})
                                } else {  // empty
                                    Ok(Grounding::Boolean{tu: GroundingView::Empty, uf:  GroundingView::Empty, g:  GroundingView::Empty})
                                }
                            },
                            Some(Grounding::NonBoolean(_))
                            | None => Err(InternalError(85896566))
                        }
                    }
                    "=" => {
                        // LINK src/doc.md#_Equality
                        let tu = query_for_compound(qual_identifier, index, &mut gqs, &variant, Some(false), solver)?;

                        let uf = query_for_compound(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?;

                        let g = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})
                    }
                    "<"
                    | "<="
                    | ">="
                    | ">"
                    | "distinct" => {
                        let tu = query_for_compound(qual_identifier, index, &mut gqs, &variant, Some(false), solver)?;

                        let uf = query_for_compound(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?;

                        let g = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})
                    }
                    _ => Err(InternalError(58994512))
                }
            } else {  // predefined non-boolean function
                match qual_identifier.to_string().as_str() {
                    "+" | "-" | "*" | "div" | "mod" | "abs" => {
                        let g = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::NonBoolean( g ))
                    }
                    _ => Err(InternalError(48519624))
                }
            }
        },
        FunctionObject::Constructor => {
            // LINK src/doc.md#_Constructor
            let variant = QueryVariant::Construct;
            if qual_identifier.to_string() == "true"
            || qual_identifier.to_string() == "false" {  // boolean
                let tu = query_for_compound(qual_identifier, index, &mut vec![], &variant, Some(false), solver)?;
                let uf = query_for_compound(qual_identifier, index, &mut vec![], &variant, Some(true), solver)?;
                let g = query_for_compound(qual_identifier, index, &mut vec![], &variant, None, solver)?;
                Ok(Grounding::Boolean{tu, uf, g})
            } else {
                let grounding_query = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        FunctionObject::NotInterpreted { signature: (_, _, boolean)} => { // custom function
            let variant = QueryVariant::Apply;
            if *boolean {

                // custom boolean function
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);
                let  g = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                let tu = query_for_compound(qual_identifier, index, &mut tus, &variant, Some(false), solver)?;
                let uf = query_for_compound(qual_identifier, index, &mut ufs, &variant, Some(true), solver)?;

                Ok(Grounding::Boolean{tu, uf, g})
            } else {

                // custom non-boolean function
                let grounding_query = query_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g } => {
            let (tus, ufs) = collect_tu_uf(&groundings);

            let mut new_queries = vec![];

            for ((table, groundings), view_type)
            in [table_tu.clone(), table_uf.clone(), table_g.clone()].iter()
                .zip([tus, ufs, gqs.to_vec()])
                .zip([ViewType::TU, ViewType::UF, ViewType::G]) {

                let exclude = match view_type {
                    ViewType::TU => Some(false),
                    ViewType::UF => Some(true),
                    ViewType::G  => None
                };
                let variant = match table {
                    Interpretation::Table{name, ids, else_} => {
                        let table_name = TableAlias::new(name, index);
                        QueryVariant::Interpretation(table_name, ids.clone(), else_.clone())
                    },
                    Interpretation::Infinite => QueryVariant::Apply
                };
                let new_view = query_for_compound(qual_identifier, index, &groundings, &variant, exclude, solver)?;
                new_queries.push(new_view);
            };

            Ok(Grounding::Boolean{tu: new_queries[0].clone(), uf: new_queries[1].clone(), g: new_queries[2].clone()})
        },
        FunctionObject::NonBooleanInterpreted { table_g } => {
            let variant = match table_g {
                Interpretation::Table{name, ids, else_} => {
                    let table_name = TableAlias::new(name, index);
                    QueryVariant::Interpretation(table_name, ids.clone(), else_.clone())
                },
                Interpretation::Infinite => QueryVariant::Apply
            };
            let new_view = query_for_compound(qual_identifier, index, &gqs, &variant, None, solver)?;
            Ok(Grounding::NonBoolean(new_view))
        }
    }
}


/// Collect the TU (resp. UF) grounding queries in the vector of groundings
fn collect_tu_uf(
    groundings: &Vec<Grounding>
) -> (Vec<GroundingView>, Vec<GroundingView>) {

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

