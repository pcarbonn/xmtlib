// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;
use itertools::Either::{Right, Left};
use rusqlite::Connection;

use crate::api::{Identifier, QualIdentifier, SortedVar, Term};
use crate::error::SolverError::{self, *};
use crate::private::b_fun::{FunctionObject, InterpretationType};
use crate::private::x_query::{Column, TableName, GroundingQuery, Ids, SQLExpr,
    query_spec_constant, query_for_aggregate, query_for_compound};
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
        // update statistics in DB
        solver.conn.execute("ANALYZE", []).unwrap();

        // extract terms and commands
        let (commands, terms) = solver.assertions_to_ground.iter()
            .map(|(command, term)| (command.clone(), term.clone()))
            .collect::<(Vec<_>, Vec<_>)>();

        for (term, command) in terms.iter().zip(commands) {
            // push and pop, to avoid polluting the SMT state
            yield_!(solver.backend.exec("(push)"));
            yield_!(solver.backend.exec(&command));
            yield_!(solver.backend.exec("(pop)"));

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
                                        yield_!(solver.backend.exec(&assert));
                                    }
                                },
                                Err(e) =>
                                    yield_!(Err(e))
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
            if let Some(sort) = sort {  // finite domain
                let base_table = sort.to_string();
                let table_name = TableName{base_table: base_table.clone(), index};
                let column = Column{table_name: table_name.clone(), column: "G".to_string()};
                let g = GroundingQuery{
                    variables: IndexMap::from([(symbol.clone(), column.clone())]),
                    conditions: vec![],
                    grounding: SQLExpr::Variable(symbol.clone()),
                    natural_joins: IndexMap::from([(table_name, Left(symbol.clone()))]),
                    theta_joins: vec![],
                    ids: Ids::All,
                };

                if base_table == "bool" {
                    Ok(Grounding::Boolean { tu: g.clone(), uf: g.clone(), g: g })
                } else {
                    Ok(Grounding::NonBoolean(g))
                }
            } else {  // infinite domain
                let qual_identifier = QualIdentifier::Identifier(Identifier::Simple(symbol.clone()));
                let variant = Right("apply".to_string());
                let g = query_for_compound(&qual_identifier, &mut vec![], &variant)?;
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
        Term::Exists(variables, term, Some(interpreted_vars)) => {
            match ground_term(term, false, solver)? {
                Grounding::NonBoolean(_) =>
                    Err(InternalError(42578548)),
                Grounding::Boolean { tu: sub_tu, uf: _, g: sub_g } => {

                    let mut free_variables = sub_g.variables.clone();
                    for SortedVar(symbol, _) in variables {
                        free_variables.shift_remove(symbol);
                    }
                    for SortedVar(symbol, _) in interpreted_vars {
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
        Term::Forall(_, _, None)
        | Term::Exists(_, _, None) => Err(InternalError(95788566)),  // expecting Some(vec![]) if no interpretation
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
                                let (mut tus, _) = collect_tu_uf(groundings);

                                let variant = Right("apply".to_string());
                                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant)?;

                                let tu = query_for_compound(qual_identifier, &mut tus, &variant)?;

                                // todo: union query(qual_identifer, ufs)  Use g in the mean time.
                                let uf = query_for_compound(qual_identifier, &mut gqs, &variant)?;

                                Ok(Grounding::Boolean{tu, uf, g: grounding_query})
                            },
                            "or" => {

                                // or
                                let (_, mut ufs) = collect_tu_uf(groundings);

                                let variant = Right("apply".to_string());
                                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant)?;

                                // todo: union query(qual_identifer, tus).  Use g in the mean time.
                                let tu = query_for_compound(qual_identifier, &mut gqs, &variant)?;

                                let uf = query_for_compound(qual_identifier, &mut ufs, &variant)?;

                                Ok(Grounding::Boolean{tu, uf, g: grounding_query})
                            },
                              "not" => {

                                // not
                                // return uf, tu, g with grounding G replaced by not(G)
                                match groundings.get(0) {
                                    Some(Grounding::Boolean { tu, uf, g }) => {
                                        let (mut tu, mut uf, mut g) = (tu.clone(), uf.clone(), g.clone());
                                        tu.grounding =
                                            if tu.ids == Ids::All {
                                                SQLExpr::Boolean(false)
                                            } else {
                                                SQLExpr::Apply(qual_identifier.clone(), Box::new(vec![tu.grounding]))
                                            };
                                        uf.grounding =
                                            if uf.ids == Ids::All {
                                                SQLExpr::Boolean(true)
                                            } else {
                                                SQLExpr::Apply(qual_identifier.clone(), Box::new(vec![uf.grounding]))
                                            };
                                         g.grounding = SQLExpr::Apply(qual_identifier.clone(), Box::new(vec![ g.grounding]));
                                        Ok(Grounding::Boolean{tu: uf, uf: tu, g})
                                    },
                                    Some(Grounding::NonBoolean(_))
                                    | None => Err(InternalError(85896566))
                                }
                              },
                            "=>"
                            | "="
                            | "<="
                            | "<"
                            | ">="
                            | ">" => todo!(),

                            _ => {

                                // custom boolean function with simple name
                                ground_boolean_compound(qual_identifier, groundings, &mut gqs, &typ, index)
                            }
                        }
                    },
                    QualIdentifier::Identifier(Identifier::Indexed(_,_))
                    | QualIdentifier::Sorted(_, _) => {

                        // custom boolean function with complex identifier
                        ground_boolean_compound(qual_identifier, groundings, &mut gqs, &typ, index)
                    },
                }

            } else {  // not boolean

                // custom non-boolean function
                let variant =
                    match typ {
                        InterpretationType::Calculated => Right("apply".to_string()),
                        // todo : Constructed
                        InterpretationType::Boolean {..} => return Err(InternalError(25963955))
                    };
                let grounding_query = query_for_compound(qual_identifier, &mut gqs, &variant)?;
                Ok(Grounding::NonBoolean(grounding_query))
            }
        },
        None => {
            // constructor.  todo: this should not happen once constructors are declared
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
    typ: &InterpretationType,
    index: usize
) -> Result<Grounding, SolverError> {
    // custom boolean function
    let (mut tus, mut ufs) = collect_tu_uf(groundings);
    match typ {
        InterpretationType::Calculated => {
            let variant = Right("apply".to_string());

            let  g = query_for_compound(qual_identifier, gqs, &variant)?;
            let tu = query_for_compound(qual_identifier, &mut tus, &variant)?;
            let uf = query_for_compound(qual_identifier, &mut ufs, &variant)?;

            Ok(Grounding::Boolean{tu, uf, g})
        },
        InterpretationType::Boolean { table_tu, table_uf, table_g, ids } => {
            let table_name = TableName{base_table: table_tu.clone(), index};
            let variant = Left((table_name, ids.clone()));
            let tu = query_for_compound(qual_identifier, &mut tus, &variant)?;

            let table_name = TableName{base_table: table_uf.clone(), index};
            let variant = Left((table_name, ids.clone()));
            let uf = query_for_compound(qual_identifier, &mut ufs, &variant)?;

            let table_name = TableName{base_table: table_g.clone(), index};
            let variant = Left((table_name, ids.clone()));
            let g = query_for_compound(qual_identifier, gqs, &variant)?;

            Ok(Grounding::Boolean{tu, uf, g})
        }
    }
}

