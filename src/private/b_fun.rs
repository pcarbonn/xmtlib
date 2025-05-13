// Copyright Pierre Carbonnelle, 2025.


use std::fmt::Display;

use indexmap::{IndexMap, IndexSet};

use crate::ast::{Identifier, QualIdentifier, Sort, Symbol, Term};
use crate::error::SolverError;
use crate::solver::{Solver, CanonicalSort};
use crate::private::a_sort::instantiate_sort;
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::TableName;
use crate::private::e3_ground_sql::Predefined;
use crate::ast::L;


/////////////////////  Data structure for Function  ///////////////////////////


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FunctionObject {
    Predefined{function: Predefined, boolean: Option<bool>},  // None = unknown for `ite, let` --> need special code
    Constructor,
    NotInterpreted,
    Interpreted(Interpretation),
    BooleanInterpreted{table_tu: Interpretation, table_uf: Interpretation, table_g: Interpretation}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Interpretation {
    Table{name: TableName, ids: Ids},
    Infinite  // for UF, G of interpreted predicate over infinite domain
}


/////////////////////  Implementation  ////////////////////////////////////////


impl Display for FunctionObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Predefined{boolean, ..} =>
                if let Some(b) = boolean {
                    write!(f, "Predefined ({b})")
                } else {
                    write!(f, "Predefined (?)")
                },
            Self::Constructor =>
                write!(f, "Constructor"),
            Self::NotInterpreted =>
                write!(f,"Not interpreted"),
            Self::Interpreted(table_g) =>
                write!(f, "Non Boolean ({table_g})"),
            Self::BooleanInterpreted{table_tu, table_uf, table_g} =>
                write!(f, "Boolean ({table_tu}, {table_uf}, {table_g})"),
        }
    }
}


impl Display for Interpretation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Table{name, ids} => write!(f, "{name} {ids}"),
            Self::Infinite {} =>
                write!(f, "(infinite)"),
        }
    }
}

pub(crate) fn declare_fun(
    symbol: Symbol,
    domain: Vec<Sort>,
    co_domain: Sort,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;  // this also validates the declaration

    // instantiate the sorts, if needed
    let declaring = IndexSet::new();
    for sort in &domain {
        instantiate_sort(&sort, &declaring, solver)?;
    }
    instantiate_sort(&co_domain, &declaring, solver)?;

    let domain = domain.iter()
        .map( | sort | solver.canonical_sorts.get(sort).unwrap().clone())
        .collect::<Vec<_>>();
    let co_domain = solver.canonical_sorts.get(&co_domain)
        .ok_or(SolverError::ExprError("unknown co_domain".to_string()))?;

    let identifier = Identifier::new(&symbol);
    let function_is = FunctionObject::NotInterpreted;

    solver.interpretable_functions.insert(identifier.clone(), (domain.clone(), co_domain.clone()));
    solver.function_objects.insert((identifier.clone(), domain.clone()), IndexMap::from([(co_domain.clone(), function_is.clone())]));

    Ok(out)
}

/// # Arguments:
///
/// * term: a function application (used for error reporting)
///
pub(crate) fn get_function_object<'a>(
    term: &L<Term>,
    function: &'a QualIdentifier,
    sorts: &Vec<CanonicalSort>,
    solver: &'a Solver
) -> Result<(&'a CanonicalSort, &'a FunctionObject), SolverError> {

    match function {
        QualIdentifier::Identifier(identifier) => {
            match solver.function_objects.get(&(identifier.clone(), sorts.clone())) {
                Some(map) => {
                    if map.len() == 1 {
                        Ok(map.first().unwrap())
                    } else {
                        Err(SolverError::TermError("Ambiguous term application", term.clone()))  // ambiguous
                    }
                }
                None => Err(SolverError::TermError("Unknown symbol", term.clone()))
            }
        },
        QualIdentifier::Sorted(identifier, sort) =>
            match solver.function_objects.get(&(identifier.clone(), sorts.clone())) {
                Some(map) => {
                    if let Some(canonical) = solver.canonical_sorts.get(sort) {
                        match map.get(canonical) {
                            Some(function_object) =>
                                Ok((canonical, function_object)),
                            None => Err(SolverError::TermError("Inappropriate identifier qualification", term.clone()))
                        }
                    } else { Err(SolverError::TermError("Incorrect function application", term.clone())) }
                }
                None => Err(SolverError::TermError("Unknown symbol", term.clone()))
            }
    }
}