// Copyright Pierre Carbonnelle, 2025.

use crate::error::SolverError;

pub trait Backend {
    fn exec(&mut self, cmd: &str) -> Result<String, SolverError>;
}

pub struct NoSolver{}

impl Backend for NoSolver {
    fn exec(&mut self, cmd: &str) -> Result<String, SolverError> {
        Ok(cmd.to_string())
    }
}

