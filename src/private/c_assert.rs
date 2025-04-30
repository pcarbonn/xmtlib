// Copyright Pierre Carbonnelle, 2025.

use indexmap::{IndexMap, IndexSet};

use crate::ast::{Identifier, QualIdentifier, SortedVar, Symbol, Term, VarBinding};
use crate::error::{SolverError::{self, *}, Offset};
use crate::solver::Solver;

use crate::private::a_sort::SortObject;
use crate::ast::L;


/////////////////////  Command (assert ////////////////////////////////////////

pub(crate) fn assert_(
    term: &L<Term>,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let mut variables = IndexMap::new();
    let new_term = annotate_term(term, &mut variables, solver)?;
    solver.assertions_to_ground.push(new_term);
    Ok("".to_string())
}


/// Transform and annotate the formula:
/// - replace each occurrence of a variable by an XSorted term, with type
/// - replace p=>(q=>r) by ~p|~q|r
/// - merge nested conjunction (resp. disjunction)
/// - remove duplicate conjuncts/disjuncts
/// - push negation down disjunctions and conjunctions

/// - todo: replace ambiguous simple identifier (constructor) by a qualified identifier
pub(crate) fn annotate_term(
    term: &L<Term>,
    variables: &mut IndexMap<Symbol, Option<SortedVar>>,  // can't use XSortedVar here because it's a term variant
    //todo add expected_type to allow qualification of identifier
    solver: &Solver
) -> Result<L<Term>, SolverError> {

    match term {
        L(Term::SpecConstant(_), _) => Ok(term.clone()),

        L(Term::Identifier(ref qual_identifier), start) => {

            // replace variable by XSortedVar
            match qual_identifier {
                QualIdentifier::Identifier(L(Identifier::Simple(ref symbol), _)) => {
                    match variables.get(symbol) {
                        Some(Some(SortedVar(_, ref sort))) => // a regular variable
                            Ok(L(Term::XSortedVar(symbol.clone(), Some(sort.clone())), *start)),
                        Some(None) =>  // a variable introduced by a `let``
                            Ok(L(Term::XSortedVar(symbol.clone(), None), *start)),
                        None =>
                            Ok(term.clone())  // a regular identifier
                    }
                },
                _ => Ok(term.clone()),
            }
        },

        L(Term::Application(qual_identifier, terms), start) => {

            let and: QualIdentifier = QualIdentifier::Identifier(L(Identifier::Simple(Symbol("and".to_string())), Offset(0)));
            let or: QualIdentifier = QualIdentifier::Identifier(L(Identifier::Simple(Symbol("or".to_string())), Offset(0)));
            let not: QualIdentifier = QualIdentifier::Identifier(L(Identifier::Simple(Symbol("not".to_string())), Offset(0)));

            match qual_identifier.to_string().as_str() {
                "=>" => {
                    // annotate(p =>(q=>r)) becomes annotate(~p|~q|r)
                    // negate all terms, except the last one
                    let new_terms = terms.iter().enumerate()
                        .map( | (i, t) | if i < terms.len()-1 {
                            L(Term::Application(not.clone(), vec![t.clone()]), *start)
                        } else {
                            t.clone()
                        }).collect::<Vec<_>>();
                    let new_term = L(Term::Application(or.clone(), new_terms), *start);
                    annotate_term(&new_term, variables, solver)
                }
                "not" => {
                    assert_eq!(terms.len(), 1);
                    match terms.get(0) {
                        Some(sub_term) => {
                            match sub_term {
                                L(Term::Application(sub_identifier, sub_terms), start) => {
                                    match sub_identifier.to_string().as_str() {
                                        "and" => {
                                            // annotate(not((and ps))) becomes annotate((or (not ps)))
                                            // negate all terms
                                            let new_terms = sub_terms.iter()
                                                .map( | t | L(Term::Application(not.clone(), vec![t.clone()]), t.start()))
                                                .collect::<IndexSet<_>>();
                                            let new_term = L(Term::Application(or.clone(), new_terms.iter().cloned().collect()), *start);
                                            annotate_term(&new_term, variables, solver)
                                        },
                                        "or" => {
                                            // annotate(not((or ps))) becomes annotate((and (not ps)))
                                            // negate all terms
                                            let new_terms = sub_terms.iter()
                                                .map( | t | L(Term::Application(not.clone(), vec![t.clone()]), t.start()))
                                                .collect::<IndexSet<_>>();
                                            let new_term = L(Term::Application(and.clone(), new_terms.iter().cloned().collect()), *start);
                                            annotate_term(&new_term, variables, solver)
                                        },
                                        _ => {
                                            let new_term = annotate_term(sub_term, variables, solver)?;
                                            Ok(L(Term::Application(qual_identifier.clone(), vec![new_term]), *start))
                                        }
                                    }
                                }
                                _ => {
                                    let new_term = annotate_term(sub_term, variables, solver)?;
                                    Ok(L(Term::Application(qual_identifier.clone(), vec![new_term]), sub_term.start()))
                                }
                            }
                        }
                        None => Err(InternalError(4266))
                    }
                }
                "and" => {
                    // annotate(and p (and qs)) becomes (and annotate(p) annotate(qs)), without repetition
                    let mut new_sub_terms = vec![];
                    for sub_term in terms {
                        let sub_term = annotate_term(sub_term, variables, solver)?;
                        if let L(Term::Application(ref sub_identifier, ref sub_terms2), _) = sub_term {
                            if sub_identifier.to_string() == "and" {
                                new_sub_terms.append(&mut sub_terms2.clone());
                            } else {
                                new_sub_terms.push(sub_term);
                            }
                        } else {
                            new_sub_terms.push(sub_term);
                        }
                    };
                    Ok(L(Term::Application(and.clone(), new_sub_terms), *start))
                }
                "or" => {
                    // annotate(or p (or qs)) becomes (or annotate(p) annotate(qs)), without repetition
                    let mut new_sub_terms = vec![];
                    for sub_term in terms {
                        let sub_term = annotate_term(sub_term, variables, solver)?;
                        if let L(Term::Application(ref sub_identifier, ref sub_terms2), _) = sub_term {
                            if sub_identifier.to_string() == "or" {
                                new_sub_terms.append(&mut sub_terms2.clone());
                            } else {
                                new_sub_terms.push(sub_term);
                            }
                        } else {
                            new_sub_terms.push(sub_term);
                        }
                    };
                    Ok(L(Term::Application(or.clone(), new_sub_terms), *start))
                }
                _ => {
                    // a regular identifier
                    let new_terms = terms.iter()
                        .map(|t| annotate_term(t, variables, solver))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(L(Term::Application(qual_identifier.clone(), new_terms), *start))
                }
            }
        },

        L(Term::Let(var_bindings, term), start) => {
            // transform the t_i in var_bindings using variables, and term using new_variables for proper shadowing
            let mut new_variables = variables.clone();
            let mut new_var_bindings = vec![];
            for VarBinding(symbol, binding) in var_bindings {
                let binding = annotate_term(&binding, variables, solver)?;
                new_variables.insert(symbol.clone(), None);  // don't try to interpret the variable during grounding of term
                new_var_bindings.push(VarBinding(symbol.clone(), binding))
            };
            let new_term = annotate_term(term, &mut new_variables, solver)?;
            Ok(L(Term::Let(new_var_bindings, Box::new(new_term)), *start))
        },

        L(Term::Forall(sorted_vars, term), start) => {
            let new_term =
                process_quantification(sorted_vars, term, variables, solver)?;
            Ok(L(Term::Forall(sorted_vars.clone(), Box::new(new_term)), *start))
        },

        L(Term::Exists(sorted_vars, term), start) => {
            let new_term =
                process_quantification(sorted_vars, term, variables, solver)?;
            Ok(L(Term::Exists(sorted_vars.clone(), Box::new(new_term)), *start))
        },

        L(Term::Match(_, _), _) => {
            // let term = annotate_term(term, variables, solver)?;
            // let mut new_match_cases = vec![];
            // for MatchCase(pattern, result) in match_cases {
            //     let new_result = annotate_term(result, variables, solver)?;
            //     new_match_cases.push(MatchCase(pattern.clone(), new_result));
            // }
            // Ok(Term::Match(Box::new(term), new_match_cases))
            todo!("need to decide how to ground match term")
        },

        L(Term::Annotation(term, attributes), start) => {
            let new_term = annotate_term(&term, variables, solver)?;
            Ok(L(Term::Annotation(Box::new(new_term), attributes.clone()), *start))
        },

        L(Term::XSortedVar(_, _), _) =>
            Err(InternalError(812685563)),  // XSortedVar not expected here
    }
}


/// Process a quantification
///
/// The first element of the result is the subset of `variables` with an infinite domain;
/// The second element of the result is the annotated term with the updated variables;
/// The third element of the result is the subset of `variables` with finite domain.
fn process_quantification (
    sorted_vars: &Vec<SortedVar>,
    term: &Box<L<Term>>,
    variables: &mut IndexMap<Symbol, Option<SortedVar>>,
    solver: &Solver
) -> Result<L<Term>, SolverError> {

    let mut new_variables = variables.clone();
    for SortedVar(symbol, sort) in sorted_vars {
        match solver.sorts.get(sort) {
            Some(SortObject::Normal{..}) => {
                new_variables.insert(symbol.clone(), Some(SortedVar(symbol.clone(), sort.clone())));
            },
            Some(SortObject::Infinite)
            | Some(SortObject::Recursive)
            | Some(SortObject::Unknown) => {
                new_variables.insert(symbol.clone(), None);
            },
            None => return Err(InternalError(2486645)),
        }
    };
    let new_term = annotate_term(term, &mut new_variables, solver)?;
    Ok(new_term)
}