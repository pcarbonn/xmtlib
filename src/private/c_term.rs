// Copyright Pierre Carbonnelle, 2025.

/////////////////////  Command ///////////////////////////////////////////////

use crate::api::Term;
use crate::solver::Solver;
use crate::error::SolverError;

pub(crate) fn assert(
    _term: Term,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;  // this also validates the assertion

    Ok(out)
}