// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};


/////////////////////  Command ///////////////////////////////////////////////

use crate::solver::Solver;
use crate::error::SolverError;

pub(crate) fn ground(
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    let commands = solver.terms_to_ground.iter()
        .map(|(_,command)| command.clone()).collect::<Vec<_>>();

    gen!({
        for command in commands {
            yield_!(solver.exec(&command))
        }

        // reset terms to ground
        solver.terms_to_ground = vec![];
    })
}