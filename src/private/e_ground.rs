// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use rusqlite::Connection;

use crate::api::{QualIdentifier, SortedVar, Term};
use crate::error::SolverError::{self, *};
use crate::private::b_fun::{FunctionIs, Interpretation};
use crate::private::e1_ground_query::{TableName, GroundingQuery, Ids, View, Variant,
    query_spec_constant, query_for_variable, query_for_aggregate, query_for_compound};
use crate::private::e2_ground_sql::SQLExpr;
use crate::solver::Solver;


/////////////////////  Data structure for Grounding  //////////////////////////


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
                if tu.ids == Ids::All {
                    writeln!(f, "    T: {tu}")?;
                } else {
                    writeln!(f, "    TU: {tu}")?;
                }
                if uf.ids == Ids::All {
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
            // push and pop, to avoid polluting the SMT state
            yield_!(solver.exec("(push)"));
            yield_!(solver.exec(&command));
            yield_!(solver.exec("(pop)"));

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
                let assert = format!("(assert {})", row);
                res.push(assert);
                if row == "false" {
                    break
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
        Term::SpecConstant(spec_constant) => {

            // a number or string; cannot be Boolean
            let grounding = query_spec_constant(spec_constant);
            Ok(Grounding::NonBoolean(grounding))
        },
        Term::XSortedVar(symbol, sort) => {

            // a variable
            let base_table = if let Some(sort) = sort {  // finite domain
                    sort.to_string()
                } else {
                    "".to_string()
                };

            let g = query_for_variable(symbol, &base_table, index);

            if base_table == "bool" {
                Ok(Grounding::Boolean { tu: g.clone(), uf: g.clone(), g })
            } else {
                Ok(Grounding::NonBoolean(g))
            }
        },
        Term::Identifier(qual_identifier) => {

            // an identifier
            ground_compound(qual_identifier, &mut vec![], index, solver)
        },
        Term::Application(qual_identifier, sub_terms) => {

            // a compound term
            ground_compound(qual_identifier, sub_terms, index, solver)
        },
        Term::Let(..) => todo!(),
        Term::Forall(variables, term) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: _, uf: sub_uf, g: sub_g } => {

                    let mut free_variables = sub_g.variables.clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }

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
                        if top_level { "" } else { "and" },
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
        Term::Exists(variables, term) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: sub_tu, uf: _, g: sub_g } => {

                    let mut free_variables = sub_g.variables.clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }

                    let table_name = format!("Agg_{index}");
                    let tu = query_for_aggregate(
                        &sub_tu,
                        &free_variables,
                        &variables,
                        "or",
                        "",
                        TableName{base_table: table_name.clone() + "_TU", index: 0},
                        solver)?;

                    let uf = query_for_aggregate(
                        &sub_g,
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
        Term::Match(..) => todo!(),
        Term::Annotation(..) => todo!(),
    }
}

// Grounds a compound term
fn ground_compound(
    qual_identifier: &QualIdentifier,
    sub_terms: &Vec<Term>,
    index: usize,
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

    let function_is = match solver.functions.get(qual_identifier) {
        Some(f) => f,
        None => {
            // custom (non-boolean) constructor.  todo: this should not happen once constructors are declared
            let variant = Variant::Construct(View::G);
            let grounding_query = query_for_compound(qual_identifier, &mut vec![], &variant, solver)?;
            return Ok(Grounding::NonBoolean(grounding_query));
        }
    };

    match function_is {
        FunctionIs::Predefined { boolean: None } => { // ite
            // need to determine if boolean result or not
            todo!("ite not yet supported")
        },
        FunctionIs::Predefined { boolean: Some(boolean) } => {
            if *boolean {
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);

                if * qual_identifier == solver.and {

                    let variant = Variant::PredefinedBoolean(View::TU);
                    let tu = query_for_compound(qual_identifier, &mut tus, &variant, solver)?;

                    // todo: union query(qual_identifer, ufs).
                    let variant = Variant::PredefinedBoolean(View::UF);
                    let uf = query_for_compound(qual_identifier, &mut gqs.clone(), &variant, solver)?;

                    let variant = Variant::PredefinedBoolean(View::G);
                    let g = query_for_compound(qual_identifier, &mut gqs, &variant, solver)?;

                    Ok(Grounding::Boolean{tu, uf, g})

                } else if *qual_identifier == solver.or {

                    // todo: union query(qual_identifer, tus).
                    let variant = Variant::PredefinedBoolean(View::TU);
                    let tu = query_for_compound(qual_identifier, &mut gqs.clone(), &variant, solver)?;

                    let variant = Variant::PredefinedBoolean(View::UF);
                    let uf = query_for_compound(qual_identifier, &mut ufs, &variant, solver)?;

                    let variant = Variant::PredefinedBoolean(View::G);
                    let g = query_for_compound(qual_identifier, &mut gqs, &variant, solver)?;

                    Ok(Grounding::Boolean{tu, uf, g})

                } else if *qual_identifier == solver.not {
                    // return uf, tu, g with grounding G replaced by not(G)
                    match groundings.get(0) {
                        Some(Grounding::Boolean { tu, uf, g }) => {
                            // switch uf and tu
                            let (mut new_tu, mut new_uf, mut new_g) = (uf.clone(), tu.clone(), g.clone());
                            // negate the groundings
                            new_tu.grounding =
                                if new_tu.ids == Ids::All {
                                    SQLExpr::Boolean(true)  // all ids were false
                                } else {
                                    SQLExpr::Predefined(qual_identifier.clone(), Box::new(vec![new_tu.grounding]))
                                };
                            new_uf.grounding =
                                if uf.ids == Ids::All {
                                    SQLExpr::Boolean(false)  // all ids were true
                                } else {
                                    SQLExpr::Predefined(qual_identifier.clone(), Box::new(vec![new_uf.grounding]))
                                };
                            new_g.grounding = SQLExpr::Predefined(qual_identifier.clone(), Box::new(vec![new_g.grounding]));

                            Ok(Grounding::Boolean{tu:  new_tu, uf: new_uf, g: new_g})
                        },
                        Some(Grounding::NonBoolean(_))
                        | None => Err(InternalError(85896566))
                    }

                // "=>"
                // | "="
                // | "<="
                // | "<"
                // | ">="
                // | ">" => todo!(),
                } else {
                    Err(InternalError(58994512))
                }
            } else {  // not boolean
                // predefined non-boolean function
                todo!()
            }
        },
        FunctionIs::Constructed => {
            if *qual_identifier == solver.true_
            || *qual_identifier == solver.false_ {  // boolean
                let variant = Variant::Construct(View::TU);
                let tu = query_for_compound(qual_identifier, &mut vec![], &variant, solver)?;
                let variant = Variant::Construct(View::UF);
                let uf = query_for_compound(qual_identifier, &mut vec![], &variant, solver)?;
                let variant = Variant::Construct(View::G);
                let g = query_for_compound(qual_identifier, &mut vec![], &variant, solver)?;
                Ok(Grounding::Boolean{tu, uf, g})
            } else {
                let variant = Variant::Construct(View::G);
                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant, solver)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        FunctionIs::Calculated { signature: (_, _, boolean)} => { // custom function
            let variant = Variant::Apply;
            if *boolean {

                // custom boolean function
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);
                let  g = query_for_compound(qual_identifier, &mut gqs, &variant, solver)?;
                let tu = query_for_compound(qual_identifier, &mut tus, &variant, solver)?;
                let uf = query_for_compound(qual_identifier, &mut ufs, &variant, solver)?;

                Ok(Grounding::Boolean{tu, uf, g})
            } else {

                // custom non-boolean function
                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant, solver)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        FunctionIs::BooleanInterpreted { table_tu, table_uf, table_g } => {
            let (tus, ufs) = collect_tu_uf(&groundings);

            let mut new_queries = vec![];
            for (table, mut groundings) in [table_tu, table_uf, table_g].iter().zip([tus, ufs, gqs.to_vec()]) {

                let variant = match table {
                    Interpretation::Table{name, ids} => {
                        let table_name = TableName{base_table: name.to_string(), index};
                        Variant::Interpretation(table_name, ids.clone())
                    },
                    Interpretation::Infinite => Variant::Apply
                };
                let new_query = query_for_compound(qual_identifier, &mut groundings, &variant, solver)?;
                new_queries.push(new_query);
            };

            Ok(Grounding::Boolean{tu: new_queries[0].clone(), uf: new_queries[1].clone(), g: new_queries[2].clone()})
        },
    }
}


/// Collect the TU (resp. UF) grounding queries in the vector of groundings
fn collect_tu_uf(
    groundings: &Vec<Grounding>
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

