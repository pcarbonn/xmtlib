// Copyright Pierre Carbonnelle, 2025.


use std::fmt::Display;

use indexmap::{IndexMap, IndexSet};

use crate::ast::{Identifier, QualIdentifier, Sort, Symbol, Term};
use crate::error::{SolverError, Offset};
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
    NotInterpreted{signature: (Vec<CanonicalSort>, CanonicalSort, bool)},  // signature used to create table, when later interpreted
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
            Self::NotInterpreted{signature} => {
                let (domain, co_domain, boolean) = signature;
                let domain = domain.iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>().join(" * ");
                let co_domain = co_domain.to_string();
                write!(f,"{domain} -> {co_domain} ({boolean})")
            }
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

    let identifier = L(Identifier::Simple(symbol), Offset(0));
    let boolean = co_domain.to_string() == "Bool";
    let function_is = FunctionObject::NotInterpreted{signature: (domain.clone(), co_domain.clone(), boolean)};

    solver.interpretable_functions.insert(identifier.clone(), (domain.clone(), co_domain.clone()));
    solver.functions2.insert((identifier.clone(), domain.clone()), IndexMap::from([(co_domain.clone(), function_is.clone())]));

    Ok(out)
}

pub(crate) fn get_function_object<'a>(
    term: &L<Term>,  // a function application; used for error reporting
    function: &'a QualIdentifier,
    sorts: &Vec<CanonicalSort>,
    solver: &'a Solver
) -> Result<(&'a CanonicalSort, &'a FunctionObject), SolverError> {
    match function {
        QualIdentifier::Identifier(identifier) => {
            match solver.functions2.get(&(identifier.clone(), sorts.clone())) {
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
            match solver.functions2.get(&(identifier.clone(), sorts.clone())) {
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