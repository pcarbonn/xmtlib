// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;

use crate::api::{Identifier, QualIdentifier, SortedVar, Symbol, Term, VarBinding};
use crate::error::SolverError::{self, *};
use crate::private::a_sort::SortObject;
use crate::solver::Solver;


/////////////////////  Command (assert ////////////////////////////////////////

pub(crate) fn assert_(
    term: &Term,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let mut variables = IndexMap::new();
    let new_term = annotate_term(term, &mut variables, solver)?;
    solver.assertions_to_ground.push((command, new_term));
    Ok("".to_string())
}


/// Transform and annotate the formula:
/// - replace each occurrence of a variable by an XSorted term, with type
/// - todo: replace ambiguous simple identifier (constructor) by a qualified identifier
/// - todo: annotate `ite` with the type
/// - todo: replace p=>q by ~p|q
/// - todo: push negation down
/// - todo: push universal quantification up disjunction, down conjunction
/// - todo: push existential quantification up conjunction, down disjunction
/// - todo: remove duplicate conjuncts/disjuncts, and merge nested conjunction/disjunction
/// - todo: merge nested quantification/aggregate of the same type
pub(crate) fn annotate_term(
    term: &Term,
    variables: &mut IndexMap<Symbol, Option<SortedVar>>,  // can't use XSortedVar here because it's a term variant
    //todo add expected_type
    solver: &Solver
) -> Result<Term, SolverError> {

        // Helper function to avoid code duplication.
        // `variables` is updated with the `sorted_vars`.
        //
        // The first element of the result is the subset of `variables` with an infinite domain;
        // The second element of the result is the annotated term with the updated variables;
        // The third element of the result is the subset of `variables` with finite domain.
        fn process_quantification (
            sorted_vars: &Vec<SortedVar>,
            term: &Box<Term>,
            variables: &mut IndexMap<Symbol, Option<SortedVar>>,
            solver: &Solver
        ) -> Result<(Vec<SortedVar>, Term, Option<Vec<SortedVar>>), SolverError> {

            let mut new_variables = variables.clone();
            let mut new_sorted_vars = vec![];  // keeps the variables with infinite domain
            let mut interpreted_vars = vec![];
            for SortedVar(symbol, sort, ) in sorted_vars {
                match solver.sorts.get(sort) {
                    Some(SortObject::Normal{..}) => {
                        new_variables.insert(symbol.clone(), Some(SortedVar(symbol.clone(), sort.clone())));
                        interpreted_vars.push(SortedVar(symbol.clone(), sort.clone()))
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
            Ok((new_sorted_vars, new_term, Some(interpreted_vars)))
        }  // end helper function

    match term {
        Term::SpecConstant(_) => Ok(term.clone()),

        Term::Identifier(ref qual_identifier) => {
            match qual_identifier {
                QualIdentifier::Identifier(Identifier::Simple(ref symbol)) => {
                    match variables.get(symbol) {
                        Some(Some(SortedVar(_, ref sort))) => // a variable of finite sort
                            Ok(Term::XSortedVar(symbol.clone(), Some(sort.clone()))),
                        Some(None) =>
                            Ok(Term::XSortedVar(symbol.clone(), None)),  // a variable of infinite sort
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

        Term::Forall(sorted_vars, term, _) => {
            let (new_sorted_vars, new_term, interpreted_vars) =
                process_quantification(sorted_vars, term, variables, solver)?;
            Ok(Term::Forall(new_sorted_vars, Box::new(new_term), interpreted_vars))
        },

        Term::Exists(sorted_vars, term, _) => {
            let (new_sorted_vars, new_term, interpreted_vars) =
                process_quantification(sorted_vars, term, variables, solver)?;
            Ok(Term::Exists(new_sorted_vars, Box::new(new_term), interpreted_vars))
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
            Err(InternalError(812685563)),  // XSortedVar not expected here
    }
}

