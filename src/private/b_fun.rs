// Copyright Pierre Carbonnelle, 2025.


use std::fmt::Display;

use indexmap::IndexSet;

use crate::ast::{Sort, Symbol, Identifier, QualIdentifier};
use crate::error::{SolverError, Offset};
use crate::solver::{Solver, CanonicalSort};
use crate::private::a_sort::instantiate_parent_sort;
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::TableName;
use crate::ast::L;


/////////////////////  Data structure for Function  ///////////////////////////


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FunctionObject {
    Predefined{boolean: Option<bool>},  // None = unknown for `ite, let` --> need special code
    Constructor,
    NotInterpreted{signature: (Vec<CanonicalSort>, CanonicalSort, bool)},  // signature used to create table, when later interpreted
    NonBooleanInterpreted{ table_g: Interpretation},
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
            Self::Predefined{boolean} =>
                if let Some(b) = boolean {
                    write!(f, "Predefined ({})", b)
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
            Self::NonBooleanInterpreted{table_g} =>
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
        instantiate_parent_sort(&sort, &declaring, solver)?;
    }
    instantiate_parent_sort(&co_domain, &declaring, solver)?;

    let domain = domain.iter()
        .map( | sort | solver.canonical_sorts.get(sort).unwrap().clone())
        .collect();
    let co_domain = solver.canonical_sorts.get(&co_domain)
        .ok_or(SolverError::ExprError("unknown co_domain".to_string()))?;

    let identifier = QualIdentifier::Identifier(L(Identifier::Simple(symbol), Offset(0)));
    let boolean = co_domain.to_string() == "Bool";
    let function_is = FunctionObject::NotInterpreted{signature: (domain, co_domain.clone(), boolean)};
    solver.functions.insert(identifier, function_is);

    Ok(out)
}

pub(crate) fn get_function_object<'a>(
    function: &'a QualIdentifier,
    solver: &'a Solver
) -> Option<&'a FunctionObject> {
    solver.functions.get(function)
}