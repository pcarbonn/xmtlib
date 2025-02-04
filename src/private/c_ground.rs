// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;
use itertools::Either::{Left, Right};

use crate::api::{Identifier, QualIdentifier, SortedVar, Symbol, Term, VarBinding};
use crate::error::SolverError::{self, *};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, InterpretationType};
use crate::private::x_view::{GroundingQuery, query_compound, query_spec_constant};
use crate::solver::Solver;


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Grounding {
    NonBoolean(GroundingQuery),
    Boolean{tu: GroundingQuery, uf: GroundingQuery, g: GroundingQuery}
}
impl std::fmt::Display for Grounding {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Grounding::NonBoolean(view) => write!(f, " {view}"),
            Grounding::Boolean{tu, uf, g, ..} => {
                writeln!(f, "")?;
                writeln!(f, "    TU: {tu}")?;
                writeln!(f, "    UF: {uf}")?;
                write!  (f, "    G : {g}")
            },
        }
    }
}


/////////////////////  Command (assert ////////////////////////////////////////

pub(crate) fn assert_(
    term: &Term,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let mut variables = IndexMap::new();
    let new_term = annotate_term(term, &mut variables, solver)?;
    solver.assertions_to_ground.push((new_term, command));
    Ok("".to_string())
}


/// Removes ambiguity in identifiers by
/// - replacing each occurrence of a variable by a Term::XSortedVar
/// - todo: replace ambiguous simple identifier by a qualified identifier
pub(crate) fn annotate_term(
    term: &Term,
    variables: &mut IndexMap<Symbol, Option<SortedVar>>,  // can't use XSortedVar here because it's a term variant
    solver: &Solver
) -> Result<Term, SolverError> {

        // todo: disambiguate ambiguous simple identifier

        // Helper function to avoid code duplication
        fn process_quantification (
            sorted_vars: &Vec<SortedVar>,
            term: &Box<Term>,
            variables: &mut IndexMap<Symbol, Option<SortedVar>>,
            solver: &Solver
        ) -> Result<(Vec<SortedVar>, Term), SolverError> {
            let mut new_variables = variables.clone();
            let mut new_sorted_vars = vec![];  // keeps the variables with infinite domain
            for SortedVar(symbol, sort, ) in sorted_vars {
                match solver.sorts.get(sort) {
                    Some(SortObject::Normal{..}) => {
                        new_variables.insert(symbol.clone(), Some(SortedVar(symbol.clone(), sort.clone())));
                    },
                    Some(SortObject::Infinite)
                    | Some(SortObject::Recursive)
                    | Some(SortObject::Unknown) => {
                        new_variables.insert(symbol.clone(), None);  // shadow pre-existing variables
                        new_sorted_vars.push(SortedVar(symbol.clone(), sort.clone()));  // keep quantification over infinite variables
                    },
                    None => return Err(InternalError(2486645)),
                }
            };
            let new_term = annotate_term(term, &mut new_variables, solver)?;
            Ok((new_sorted_vars, new_term))
        }  // end helper function

    match term {
        Term::SpecConstant(_) => Ok(term.clone()),

        Term::Identifier(ref qual_identifier) => {
            match qual_identifier {
                QualIdentifier::Identifier(Identifier::Simple(ref symbol)) => {
                    match variables.get(symbol) {
                        Some(Some(SortedVar(_, ref sort))) => // a variable of uninterpreted type
                            Ok(Term::XSortedVar(symbol.clone(), Some(sort.clone()))),
                        Some(None) =>
                            Ok(Term::XSortedVar(symbol.clone(), None)),  // a variable of interpreted type
                        None =>
                            Ok(term.clone())  // a regular identifier
                    }
                },
                _ => Ok(term.clone()),
            }
        },

        Term::Application(qual_identifier, terms) => {
            let new_terms = terms.iter()
                .map(|t| annotate_term(t, variables, solver))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Term::Application(qual_identifier.clone(), new_terms))
        },

        Term::Let(var_bindings, term) => {
            // transform the t_i in var_bindings using variables, and term using new_variables for propoer shadowing
            let mut new_variables = variables.clone();
            let mut new_var_bindings = vec![];
            for VarBinding(symbol, binding) in var_bindings {
                let binding = annotate_term(&binding, variables, solver)?;
                new_variables.insert(symbol.clone(), None);  // don't try to interpret the variable during grounding of term
                new_var_bindings.push(VarBinding(symbol.clone(), binding))
            };
            let new_term = annotate_term(term, &mut new_variables, solver)?;
            Ok(Term::Let(new_var_bindings, Box::new(new_term)))
        },

        Term::Forall(sorted_vars, term) => {
            let (new_sorted_vars, new_term) = process_quantification(sorted_vars, term, variables, solver)?;
            Ok(Term::Forall(new_sorted_vars, Box::new(new_term)))
        },

        Term::Exists(sorted_vars, term) => {
            let (new_sorted_vars, new_term) = process_quantification(sorted_vars, term, variables, solver)?;
            Ok(Term::Exists(new_sorted_vars, Box::new(new_term)))
        },

        Term::Match(_, _) => {
            // let term = annotate_term(term, variables, solver)?;
            // let mut new_match_cases = vec![];
            // for MatchCase(pattern, result) in match_cases {
            //     let new_result = annotate_term(result, variables, solver)?;
            //     new_match_cases.push(MatchCase(pattern.clone(), new_result));
            // }
            // Ok(Term::Match(Box::new(term), new_match_cases))
            todo!("need to decide how to ground match term")
        },

        Term::Annotation(term, attributes) => {
            let new_term = annotate_term(&term, variables, solver)?;
            Ok(Term::Annotation(Box::new(new_term), attributes.clone()))
        },

        Term::XSortedVar(_, _) =>
            Err(InternalError(812685563)),
    }
}


/////////////////////  Command (x-ground //////////////////////////////////////

pub(crate) fn ground(
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        // extract terms and commands
        let (terms, commands) = solver.assertions_to_ground.iter()
            .map(|(term,command)| (term.clone(), command.clone()))
            .collect::<(Vec<_>, Vec<_>)>();

        for (term, command) in terms.iter().zip(commands) {
            // todo: push and pop, to avoid polluting the SMT state
            yield_!(solver.exec(&command));

            match ground_term(&term, true, solver) {
                Ok(i) => {
                    // todo: run the query, and solver.exec(the resulting grounding)
                },
                Err(e) => yield_!(Err(e))
            }
        }

        // reset terms to ground
        solver.assertions_to_ground = vec![];
    })
}


/// Adds the grounding of a term to the solver, if necessary.
/// This function is recursive.
///
/// # Arguments
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction)
///
fn ground_term(
    term: &Term,
    top_level: bool,
    solver: &mut Solver
) -> Result<usize, SolverError> {

    if let Some(i) = solver.groundings.get_index_of(term) {
        Ok(i)
    } else {
        let (new_term, grounding) = ground_term_(term, top_level, solver)?;
        let (i, _) = solver.groundings.insert_full(new_term, grounding);
        Ok(i)
    }
}

/// Helper function to ground a new term.
/// An identifier term representing a variable is replaced by a XSortedVar term.
///
/// # Arguments:
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction)
///
pub(crate) fn ground_term_(
    term: &Term,
    _top_level: bool,
    solver: &mut Solver
) -> Result<(Term, Grounding), SolverError> {

    match term {
        Term::SpecConstant(spec_constant) => {

            // a number or string
            let grounding = query_spec_constant(spec_constant);
            Ok((term.clone(), Grounding::NonBoolean(grounding)))
        },
        Term::XSortedVar(..) => todo!(),  // sorted var should be handled by the quantification
        Term::Identifier(qual_identifier) => {

            let grounding = ground_compound(qual_identifier, &mut vec![], solver)?;
            Ok((term.clone(), grounding))


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
            let grounding = ground_compound(qual_identifier, sub_terms, solver)?;
            Ok((term.clone(), grounding))
        },
        Term::Let(..) => todo!(),
        Term::Forall(..) => todo!(),
        Term::Exists(..) => todo!(),
        Term::Match(..) => todo!(),
        Term::Annotation(..) => todo!(),
    }
}

// grounds a compound term
fn ground_compound(
    qual_identifier: &QualIdentifier,
    sub_terms: &Vec<Term>,
    solver: &mut Solver
) -> Result<Grounding, SolverError> {

    // ground sub_terms, creating an entry in solver.groundings if necessary
    let groundings = sub_terms.iter()
        .map( |t| ground_term(t, false, solver))
        .collect::<Result<Vec<_>,_>>()?
        .iter().map( |i| solver.groundings.get_index(*i))
        .collect::<Option<Vec<_>>>()
        .ok_or(InternalError(749634))?;

    // collect the full grounding views
    let mut gqs = groundings.iter()
        .map( |(_,g)|
            match g {
                Grounding::NonBoolean(gq) => gq.clone(),
                Grounding::Boolean{g: gq, ..} => gq.clone()
            })
        .collect::<Vec<_>>();

    let grounding =
        match solver.functions.get(qual_identifier) {
            Some(FunctionObject { boolean: None, ..}) => { // pre-defined function
                match qual_identifier {
                    QualIdentifier::Identifier(Identifier::Simple(s)) => {
                        match s.0.as_str() {
                            "and" => { // todo
                                // todo: add interpretation table, lambda, ...
                                let variant = Right("".to_string());
                                let grounding_query = query_compound(qual_identifier, &mut gqs, variant, solver)?;
                                Grounding::NonBoolean(grounding_query)
                            },
                            "or" => { // todo
                                // todo: add interpretation table, lambda, ...
                                let variant = Right("".to_string());
                                let grounding_query = query_compound(qual_identifier, &mut gqs, variant, solver)?;
                                Grounding::NonBoolean(grounding_query)
                            },
                            _ => {
                                todo!()  // "=>", equality, comparison
                            }
                        }
                    },
                    QualIdentifier::Identifier(Identifier::Indexed(_,_))
                    | QualIdentifier::Sorted(_, _) => {
                        // todo: add interpretation table, lambda, ...
                        let variant = Right("".to_string());
                        let grounding_query = query_compound(qual_identifier, &mut gqs, variant, solver)?;
                        Grounding::NonBoolean(grounding_query)
                    },
                }
            },
            Some(FunctionObject { boolean: Some(boolean), typ, ..}) => { // custom function
                if *boolean {
                    // todo: add interpretation table, lambda, ...
                    let variant = Right("".to_string());
                    let grounding_query = query_compound(qual_identifier, &mut gqs, variant, solver)?;
                    let tu = grounding_query.clone();  // todo
                    let uf = grounding_query.clone();
                    Grounding::Boolean{tu, uf, g: grounding_query}
                } else {
                    // todo: add interpretation table, lambda, ...
                    let variant = Right("".to_string());
                    let grounding_query = query_compound(qual_identifier, &mut gqs, variant, solver)?;
                    Grounding::NonBoolean(grounding_query)
                }
            },
            None => {
                // todo this should not happend for constructors
                let variant = Right("".to_string());
                let grounding_query = query_compound(qual_identifier, &mut vec![], variant, solver)?;
                Grounding::NonBoolean(grounding_query)
            },
        };
    Ok(grounding)
}

// fn ground_application(
//     term: &Term,
//     qual_identifier: &QualIdentifier,
//     arguments: &Vec<Term>,
//     _variables: &mut IndexMap<Symbol, SortedVar>,
//     solver: &mut Solver
// ) -> Result<(Term, Grounding), SolverError> {

//     let function_object = match qual_identifier {
//         QualIdentifier::Identifier(identifier) => {
//             // todo detect operators, true, false
//             solver.functions.get(identifier)
//         },
//         QualIdentifier::Sorted(..) =>
//         // lookup solver.qualified_functions
//             todo!()
//     };

//     match function_object {
//         Some(FunctionObject{typ, boolean, ..}) => {
//             match typ {
//                 InterpretationType::Calculated => {
//                     if arguments.len() == 0 {

//                         // a constant
//                         // let g = View {
//                         //     variables: IndexMap::new(),
//                         //     condition: "".to_string(),
//                         //     grounding: format!("\"{qual_identifier}\""),
//                         //     joins: IndexMap::new(),
//                         //     where_: "".to_string(),
//                         //     group_by: "".to_string(),
//                         //     _ids: Ids::None,
//                         // };
//                         // let grounding =
//                         //     match boolean {
//                         //         Some(true) => Grounding::Boolean{tu: g.clone(), uf: g.clone(), g:g},
//                         //         Some(false) => Grounding::Function(g),
//                         //         None => todo!(),
//                         //     };
//                         // Ok((term.clone(), grounding))
//                         todo!()

//                     } else {

//                         // a true function application
//                         todo!()
//                     }
//                 }
//             }
//         },
//         None => todo!(),
//     }
// }