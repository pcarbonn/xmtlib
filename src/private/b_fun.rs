// Copyright Pierre Carbonnelle, 2025.


use std::fmt::Display;

use indexmap::IndexSet;

use crate::api::{Sort, Symbol, Identifier};
use crate::private::a_sort::instantiate_parent_sort;
use crate::{error::SolverError, solver::Solver};


pub(crate) struct FunctionObject {
    pub(crate) domain: Vec<Sort>,  // todo: is it needed ?
    pub(crate) co_domain: Sort,  // todo: is it needed ?
    pub(crate) typ: InterpretationType
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum InterpretationType {
    Calculated,  // custom function without interpretation; no table in DB
    // Constructed, // constructor; no table in DB

    // db_name is the sanitized function name (without any suffix)
    // it is used for the full view

    // FunctionPartial{db_name: String},  // + _K table, _U view
    // FunctionTotal{db_name: String},

    // PredicatePartialF{db_name: String}, // False default; + _T, _U tables: + _TU, _UF views
    // PredicatePartialU{db_name: String}, // False default; + _T, _F tables; + _TU, _UF views
    // PredicatePartialT{db_name: String}, // False default; + _F, _U tables: + _TU, _UF views
    // PredicateTotal{db_name: String},
}
impl Display for InterpretationType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterpretationType::Calculated => write!(f, "calculated")
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

    let identifier = Identifier::Simple(symbol);
    let typ = InterpretationType::Calculated;
    let object = FunctionObject{domain, co_domain, typ};
    solver.functions.insert(identifier, object);

    Ok(out)
}