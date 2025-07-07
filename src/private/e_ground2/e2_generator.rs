

use crate::ast::{Term, L};
use crate::error::{Offset, SolverError::{self, *}};
use crate::solver::{Solver};

/// Contains what is needed to construct the grounding query of a term, in a composable way.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Generator {
    Empty,  // no variables
    Todo(String)
}

pub(crate) fn prepare_generators(
    term: &L<Term>,
    solver: &mut Solver
) -> Result<Generator, SolverError> {
    if let Some(generator) = solver.generators.get(term) {
        Ok(generator.clone())
    } else {
        let generator = generator(term, solver)?;
        solver.generators.insert(term.clone(),generator.clone());
        Ok(generator)
    }
}

pub(crate) fn generator (
    term: &L<Term>,
    solver: &mut Solver
) -> Result<Generator, SolverError> {

    let todo = Ok(Generator::Todo("TODO: generator".to_string()));

    match term {
        L(Term::SpecConstant(spec_constant), _) => {
            todo
        },
        L(Term::XSortedVar(symbol, sort, sorted_object), _) => {
            todo
        },
        L(Term::XLetVar(_, _), _) => {
            todo
        }
        L(Term::Identifier(qual_identifier), _) => {
            todo
        },
        L(Term::Application(qual_identifier, sub_terms), _) => {
            todo
        },
        L(Term::Let(..), _) =>
            todo,
        L(Term::Forall(variables, term), _) => {
            todo
        },
        L(Term::Exists(variables, term), _) => {
            todo
        },
        L(Term::Match(..), _) =>
            todo,
        L(Term::Annotation(..), _) =>
            todo,
    }
}


impl Generator {
    pub(crate) fn to_sql(
        &self,
        indent: &str
    ) -> String {
        match self {
            Generator::Empty => format!("{indent}Empty"),
            Generator::Todo(msg) => format!("{indent}{msg}")
        }
    }
}