// Copyright Pierre Carbonnelle, 2025.


use indexmap::IndexSet;

use crate::api::{Sort, Symbol};
use crate::private::a_sort::instantiate_parent_sort;
use crate::{error::SolverError, solver::Solver};


pub(crate) fn declare_fun(
    _symbol: Symbol,
    domain: Vec<Sort>,
    co_domain: Sort,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;  // this also validates the declaration

    // instantiate the sorts, if needed
    let declaring = IndexSet::new();
    for sort in domain {
        instantiate_parent_sort(&sort, &declaring, solver)?;
    }
    instantiate_parent_sort(&co_domain, &declaring, solver)?;

    Ok(out)
}