// Copyright Pierre Carbonnelle, 2025.

use rusqlite::{functions::FunctionFlags, Connection};

use crate::error::SolverError;

pub(crate) fn init_db(
    conn: &mut Connection
) -> Result<(), SolverError> {

    // create convenience function "apply"
    conn.create_scalar_function(
        "apply",
        -1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let symbol: String = ctx.get(0)?; // Get the string
            let args: Vec<String> = (1..ctx.len())
                .map(|i| ctx.get::<String>(i)) // Retrieve each argument as a String
                .collect::<Result<_, _>>()?;     // Collect results or propagate errors
            Ok(format!("({} {})", symbol, args.join(" "))) // Reverse the string
        },
    )?;

    // create convenience function "construct"
    // similar to "apply", but adds a space in front of the result,
    // to indicate that the result is an identifier
    conn.create_scalar_function(
        "construct",
        -1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let symbol: String = ctx.get(0)?; // Get the string
            let args: Vec<String> = (1..ctx.len())
                .map(|i| ctx.get::<String>(i)) // Retrieve each argument as a String
                .collect::<Result<_, _>>()?;     // Collect results or propagate errors
            Ok(format!(" ({} {})", symbol, args.join(" "))) // Reverse the string
        },
    )?;

    Ok(())
}