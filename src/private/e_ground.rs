// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use rusqlite::Connection;

use crate::ast::{QualIdentifier, Term};
use crate::error::SolverError::{self, *};
use crate::solver::{Solver, Backend};

use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, Interpretation};
use crate::private::e1_ground_view::{GroundingView, Ids, ViewType, QueryVariant,
    view_for_constant, view_for_variable, view_for_compound, query_for_aggregate, view_for_union};
use crate::private::e2_ground_query::{TableName, TableAlias};
use crate::ast::L;


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
                        Grounding::NonBoolean(_) => yield_!(Err(SolverError::TermError("Expecting a boolean", term.clone()))),
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
    if stmt.column_count() == 1 {  //  just G
        let row_iter = stmt.query_map([], |row| {
            row.get::<usize, String>(0)
        })?;

        let mut res = vec![];
        for row in row_iter {
            match row {
                Err(e) => return Err(SolverError::from(e)),
                Ok(g) => {
                    if g != "true" {
                        let assert = format!("(assert {g})\n");
                        res.push(assert);
                        if g == "false" {
                            break
                        }
                    }
                }
            }
        }
        return Ok(res)
    } else if stmt.column_count() == 2 {  // with an if_ column
        let row_iter = stmt.query_map([], |row| {
            Ok((
                row.get::<usize, String>(0)?,
                row.get::<usize, String>(1)?
            ))
        })?;

        let mut res = vec![];
        for row in row_iter {
            match row {
                Err(e) => return Err(SolverError::from(e)),
                Ok((if_, g)) => {
                    if if_ == "" {
                        if g != "true" {
                            let assert = format!("(assert {g})\n");
                            res.push(assert);
                            if g == "false" {
                                break
                            }
                        }
                    } else {
                        let assert = format!("(assert (=> {if_} {g}))\n");
                        res.push(assert);
                    }
                }
            }
        }
        return Ok(res)
    } else {
        unreachable!()
    }

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
    term: &L<Term>,
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
    term: &L<Term>,
    top_level: bool,
    solver: &mut Solver
) -> Result<Grounding, SolverError> {

    match term {
        L(Term::SpecConstant(spec_constant), _) => {

            // a number or string; cannot be Boolean
            let grounding = view_for_constant(spec_constant, solver)?;
            Ok(Grounding::NonBoolean(grounding))
        },
        L(Term::XSortedVar(symbol, sort), _) => {

            // a variable
            let base_table =
                if let Some(sort) = sort {  // finite domain
                    match solver.sorts.get(sort) {
                        Some(SortObject::Normal{table, ..}) => Some(table.clone()),
                        Some(SortObject::Recursive)
                        | Some(SortObject::Infinite)
                        | Some(SortObject::Unknown) => None,
                        None => None,
                    }
                } else {
                    None
                };

            let index = solver.groundings.len();
            let g = view_for_variable(symbol, base_table, index, solver)?;

            match sort {
                Some(sort) if sort.to_string() == "bool" => {
                    Ok(Grounding::Boolean { tu: g.clone(), uf: g.clone(), g })
                },
                _ => Ok(Grounding::NonBoolean(g))
            }
        },
        L(Term::Identifier(qual_identifier), _) => {

            // an identifier
            ground_compound(term, qual_identifier, &mut vec![], solver)
        },
        L(Term::Application(qual_identifier, sub_terms), _) => {

            // a compound term
            ground_compound(term, qual_identifier, sub_terms, solver)
        },
        L(Term::Let(..), _) => todo!(),
        L(Term::Forall(variables, term), _) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: _, uf: sub_uf, g: sub_g } => {

                    let index = solver.groundings.len();
                    let table_name = TableName(format!("Agg_{index}"));

                    let (free_variables, infinite_variables) = sub_g.get_free_variables(variables).clone();

                    let tu = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "and",
                        Some(false),
                        TableAlias{base_table: TableName(format!("{table_name}_TU")), index: 0},
                        solver)?;

                    let g = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "and",
                        None,
                        TableAlias{base_table: TableName(format!("{table_name}_G")), index: 0},
                        solver)?;

                    // the infinite variables may be different for sub_uf
                    let (free_variables, infinite_variables) = sub_uf.get_free_variables(variables).clone();

                    let uf = query_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &infinite_variables,
                        if top_level { "" } else { "and" },
                        None,
                        TableAlias{base_table: TableName(format!("{table_name}_UF")), index: 0},
                        solver)?;

                    Ok(Grounding::Boolean{tu, uf, g})
                },
            }
        },
        L(Term::Exists(variables, term), _) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: sub_tu, uf: _, g: sub_g } => {

                    let index = solver.groundings.len();
                    let table_name = TableName(format!("Agg_{index}"));

                    let (free_variables, infinite_variables) = sub_tu.get_free_variables(variables).clone();

                    let tu = query_for_aggregate(
                        &sub_tu,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        None,
                        TableAlias{base_table: TableName(format!("{table_name}_TU")), index: 0},
                        solver)?;

                    // the infinite variables may be different from sub tu
                    let (free_variables, infinite_variables) = sub_g.get_free_variables(variables).clone();

                    let uf = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        Some(true),
                        TableAlias{base_table: TableName(format!("{table_name}_UF")), index: 0},
                        solver)?;

                    let g = query_for_aggregate(
                        &sub_g,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        None,
                        TableAlias{base_table: TableName(format!("{table_name}_G")), index: 0},
                        solver)?;
                    Ok(Grounding::Boolean{tu, uf, g})
                },
            }
        },
        L(Term::Match(..), _) => todo!(),
        L(Term::Annotation(..), _) => todo!(),
    }
}

// Grounds a compound term
fn ground_compound(
    term: &L<Term>,
    qual_identifier: &QualIdentifier,
    sub_terms: &Vec<L<Term>>,
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
        None => return Err(SolverError::TermError("Unknown symbol", term.clone()))
    };

    match function_is {
        FunctionObject::Predefined { boolean: None } => { // ite
            match qual_identifier.to_string().as_str() {
                "ite" => {
                    if sub_terms.len() != 3 {
                        return Err(SolverError::TermError("Incorrect number of arguments", term.clone()))
                    }
                    let variant = QueryVariant::Predefined;
                    if let Grounding::Boolean{g: ifg, ..} = groundings[0].clone() {
                        match (groundings[1].clone(), groundings[2].clone()) {
                            ( Grounding::NonBoolean(lg),
                              Grounding::NonBoolean(rg)) => {
                                let mut sub_queries = vec![ifg, lg, rg];
                                let g = view_for_compound(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                        Ok(Grounding::NonBoolean( g ))
                            },
                            ( Grounding::Boolean{tu: ltu, uf: luf, g: lg, ..},
                              Grounding::Boolean{tu: rtu, uf: ruf, g: rg, ..}) => {

                                let mut sub_queries = vec![ifg.clone(), ltu, rtu];
                                let tu = view_for_compound(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                let mut sub_queries = vec![ifg.clone(), luf, ruf];
                                let uf = view_for_compound(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                let mut sub_queries = vec![ifg, lg, rg];
                                let g = view_for_compound(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                Ok(Grounding::Boolean{tu, uf, g})
                            },
                            _ => return Err(SolverError::TermError("Incorrect type of arguments", term.clone()))
                        }
                    } else {
                        return Err(SolverError::TermError("Incorrect type of arguments", term.clone()))
                    }
                }
                _ => Err(InternalError(3884562))
            }
        },
        FunctionObject::Predefined { boolean: Some(boolean) } => {
            let variant = QueryVariant::Predefined;
            if *boolean {
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);

                match qual_identifier.to_string().as_str() {
                    "and" => {

                        let tu = view_for_compound(qual_identifier, index, &mut tus, &variant, Some(false), solver)?;

                        let uf = view_for_union(ufs, Some(true), "and".to_string(), index, solver)?;

                        let g = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})
                    }
                    "or" => {

                        let tu = view_for_union(tus, Some(false), "or".to_string(), index, solver)?;

                        let uf = view_for_compound(qual_identifier,  index, &mut ufs, &variant, Some(true), solver)?;

                        let g = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

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
                            | None => Err(SolverError::TermError("not a boolean term", term.clone()))
                        }
                    }
                    "=" => {
                        // LINK src/doc.md#_Equality
                        let tu = view_for_compound(qual_identifier, index, &mut gqs, &variant, Some(false), solver)?;

                        let uf = view_for_compound(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?;

                        let g = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})
                    }
                    "<"
                    | "<="
                    | ">="
                    | ">"
                    | "distinct" => {
                        let tu = view_for_compound(qual_identifier, index, &mut gqs, &variant, Some(false), solver)?;

                        let uf = view_for_compound(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?;

                        let g = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok(Grounding::Boolean{tu, uf, g})
                    }
                    _ => Err(InternalError(58994512))
                }
            } else {  // predefined non-boolean function
                match qual_identifier.to_string().as_str() {
                    "+" | "-" | "*" | "div" | "mod" | "abs" => {
                        let g = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;

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
                let tu = view_for_compound(qual_identifier, index, &mut vec![], &variant, Some(false), solver)?;
                let uf = view_for_compound(qual_identifier, index, &mut vec![], &variant, Some(true), solver)?;
                let g = view_for_compound(qual_identifier, index, &mut vec![], &variant, None, solver)?;
                Ok(Grounding::Boolean{tu, uf, g})
            } else {
                let grounding_query = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        FunctionObject::NotInterpreted { signature: (_, _, boolean)} => { // custom function
            let variant = QueryVariant::Apply;
            if *boolean {

                // custom boolean function
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);
                let  g = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                let tu = view_for_compound(qual_identifier, index, &mut tus, &variant, Some(false), solver)?;
                let uf = view_for_compound(qual_identifier, index, &mut ufs, &variant, Some(true), solver)?;

                Ok(Grounding::Boolean{tu, uf, g})
            } else {

                // custom non-boolean function
                let grounding_query = view_for_compound(qual_identifier, index, &mut gqs, &variant, None, solver)?;
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
                    Interpretation::Table{name, ids} => {
                        let table_name = TableAlias::new(name.clone(), index);
                        QueryVariant::Interpretation(table_name, ids.clone())
                    },
                    Interpretation::Infinite => QueryVariant::Apply
                };
                let new_view = view_for_compound(qual_identifier, index, &groundings, &variant, exclude, solver)?;
                new_queries.push(new_view);
            };

            Ok(Grounding::Boolean{tu: new_queries[0].clone(), uf: new_queries[1].clone(), g: new_queries[2].clone()})
        },
        FunctionObject::NonBooleanInterpreted { table_g } => {
            let variant = match table_g {
                Interpretation::Table{name, ids} => {
                    let table_name = TableAlias::new(name.clone(), index);
                    QueryVariant::Interpretation(table_name, ids.clone())
                },
                Interpretation::Infinite => QueryVariant::Apply
            };
            let new_view = view_for_compound(qual_identifier, index, &gqs, &variant, None, solver)?;
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

