// Copyright Pierre Carbonnelle, 2025.

use rusqlite::{Connection, Result};
use rusqlite::functions::{Context, FunctionFlags, Aggregate};

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
            Ok(format!("({} {})", symbol, args.join(" ")))
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
            Ok(format!(" ({} {})", symbol, args.join(" ")))
        },
    )?;

    // create convenience function "construct"
    // similar to "construct", but adds a space in front of the result,
    // only when each argument is an id
    conn.create_scalar_function(
        "construct2",
        -1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let symbol: String = ctx.get(0)?; // Get the string

            let args: Vec<String> = (1..ctx.len())
                .map(|i| ctx.get::<String>(i)) // Retrieve each argument as a String
                .collect::<Result<_, _>>()?;     // Collect results or propagate errors
            let all_ids = args.iter().all( |arg| ! arg.starts_with("(") );
            if all_ids {  // leading space
                Ok(format!(" ({} {})", symbol, args.join(" ")))
            } else {
                Ok(format!("({} {})", symbol, args.join(" ")))
            }
        },
    )?;

    conn.create_aggregate_function(
        "and_aggregate",
        1,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        AndState(Some(vec![])))?;

    conn.create_aggregate_function(
        "or_aggregate",
        1,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        OrState(Some(vec![])))?;

    Ok(())
}


//////////////////////////// AND aggregate ////////////////////////////////////

#[derive(Default, Clone)]
struct AndState ( Option<Vec<String>> );

/// Implement the `Aggregate` trait for `SumSquares`
impl Aggregate<AndState, String> for AndState {

    fn init(&self, _ctx: &mut Context<'_>)  -> Result<AndState> {
        Ok(AndState(Some(vec![])))
    }
    /// Called for each row in the query
    fn step(&self, ctx: &mut Context<'_>, acc: &mut AndState) -> rusqlite::Result<()> {
        let value: String = ctx.get(0)?;
        if let AndState(Some(terms)) = acc { // if not false already
            if value == "false" {
                *acc = AndState(None)
            } else if value != "true" {
                terms.push(value)
            };
        }
        Ok(())
    }

    /// Called at the end to return the final result
    fn finalize(&self, _ctx: &mut Context<'_>, acc: Option<AndState>) -> rusqlite::Result<String> {
        if let Some(AndState(Some(terms))) = acc {  // not false
            if terms.len() == 0 {
                Ok("true".to_string())
            } else if terms.len() == 1 {
                Ok(terms.join(" "))  // get the first one
            } else {
                Ok(format!("(and {})", terms.join(" ")))
            }
        } else {
            Ok("false".to_string())
        }
    }
}


//////////////////////////// OR aggregate ////////////////////////////////////

#[derive(Default, Clone)]
struct OrState ( Option<Vec<String>> );

/// Implement the `Aggregate` trait for `SumSquares`
impl Aggregate<OrState, String> for OrState {

    fn init(&self, _ctx: &mut Context<'_>)  -> Result<OrState> {
        Ok(OrState(Some(vec![])))
    }
    /// Called for each row in the query
    fn step(&self, ctx: &mut Context<'_>, acc: &mut OrState) -> rusqlite::Result<()> {
        let value: String = ctx.get(0)?;
        if let OrState(Some(terms)) = acc { // if not true already
            if value == "true" {
                *acc = OrState(None)
            } else if value != "false" {
                terms.push(value)
            };
        }
        Ok(())
    }

    /// Called at the end to return the final result
    fn finalize(&self, _ctx: &mut Context<'_>, acc: Option<OrState>) -> rusqlite::Result<String> {
        if let Some(OrState(Some(terms))) = acc {  // not true
            if terms.len() == 0 {
                Ok("false".to_string())
            } else if terms.len() == 1 {
                Ok(terms.join(" "))
            } else {
                Ok(format!("(or {})", terms.join(" ")))
            }
        } else {
            Ok("true".to_string())
        }
    }
}

// todo isid