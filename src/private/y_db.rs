// Copyright Pierre Carbonnelle, 2025.

use rusqlite::types::FromSql;
use rusqlite::{Connection, Result, Error};
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
            let (symbol, args) = get_symbol_args(ctx)?;
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
            let (symbol, args) = get_symbol_args(ctx)?;
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
            let (symbol, args) = get_symbol_args(ctx)?;
            let all_ids = args.iter().all( |arg| ! arg.starts_with("(") );
            if all_ids {  // leading space
                Ok(format!(" ({} {})", symbol, args.join(" ")))
            } else {
                Ok(format!("({} {})", symbol, args.join(" ")))
            }
        },
    )?;

    // create function "not_"
    conn.create_scalar_function(
        "not_",
        1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let value = ctx.get::<String>(0)?;
            if value == "true" {
                Ok("false".to_string())
            } else if value == "false" {
                Ok("true".to_string())
            } else {
                Ok(format!("(not {})", value))
            }
        },
    )?;

    // create function "and_"
    conn.create_scalar_function(
        "and_",
        -1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let mut state = AndState(Some(vec![]));
            for i in 0..ctx.len() {
                if let AndState(Some(ref mut terms)) = state { // if not false already
                    let value = ctx.get::<String>(i)?;
                    if value == "false" {
                        state = AndState(None);
                        break
                    } else if value != "true" {
                        terms.push(value)
                    };
                }
            }
            // finalize
            if let AndState(Some(terms)) = state {  // not false
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
        },
    )?;

    // create function "or_"
    conn.create_scalar_function(
        "or_",
        -1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let mut state = OrState(Some(vec![]));
            for i in 0..ctx.len() {
                if let OrState(Some(ref mut terms)) = state { // if not true already
                    let value = ctx.get::<String>(i)?;
                    if value == "true" {
                        state = OrState(None);
                        break
                    } else if value != "false" {
                        terms.push(value)
                    };
                }
            }
            // finalize
            if let OrState(Some(terms)) = state {  // not false
                if terms.len() == 0 {
                    Ok("false".to_string())
                } else if terms.len() == 1 {
                    Ok(terms.join(" "))  // get the first one
                } else {
                    Ok(format!("(or {})", terms.join(" ")))
                }
            } else {
                Ok("true".to_string())
            }
        },
    )?;

    // create function "implies_"
    conn.create_scalar_function(
        "implies_",
        2,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let a1 = ctx.get::<String>(0)?;
            let a2 = ctx.get::<String>(1)?;

            if a1 == "true" {
                Ok(a2.to_string())
            } else if a1 == "false" {
                Ok("true".to_string())
            } else if a2 == "true" {
                Ok("true".to_string())
            } else if a2 == "false" {
                Ok(format!("(not {})", a1))
            } else {
                Ok(format!("(=> {} {})", a1, a2))
            }
        },
    )?;

    conn.create_aggregate_function(
        "and_aggregate",
        1,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        AndState(None))?;  // `init` will be called

    conn.create_aggregate_function(
        "or_aggregate",
        1,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        OrState(None))?;  // `init` will be called

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


/// get the symbol and args from the context
fn get_symbol_args (ctx: &Context) -> Result<(String, Vec<String>), Error> {
    let symbol: String = ctx.get(0)?; // Get the string
    let args: Vec<String> = (1..ctx.len())
        .map(|i| {
            let value = ctx.get_raw(i);
            match value {
                rusqlite::types::ValueRef::Null =>
                    Err(Error::InvalidFunctionParameterType(i, value.data_type())),
                rusqlite::types::ValueRef::Integer(i) =>
                    Ok(i.to_string()),
                rusqlite::types::ValueRef::Real(r) =>
                    Ok(r.to_string()),
                rusqlite::types::ValueRef::Text(_) =>
                    FromSql::column_result(value)
                        .map_err(|_| Error::InvalidFunctionParameterType(i, value.data_type())),
                rusqlite::types::ValueRef::Blob(_) =>
                    Err(Error::InvalidFunctionParameterType(i, value.data_type())),
            }
        }).collect::<Result<_, Error>>()?;     // Collect results or propagate errors
    Ok((symbol, args))
}

