// Copyright Pierre Carbonnelle, 2025.

use itertools::Itertools;

use crate::api::{Symbol, XTuple};
use crate::error::SolverError;
use crate::solver::Solver;

pub(crate) fn interpret_pred(
    symbol: Symbol,
    tuples: Vec<XTuple>,
    _command: String,
    _solver: &mut Solver,
 ) -> Result<String, SolverError> {
    Ok(format!("(x-interpret-pred {symbol} {})", tuples.iter().format(" ")))
}