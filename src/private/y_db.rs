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

    // create function "is_id"
    conn.create_scalar_function(
        "is_id",
        1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC, // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let a1 = ctx.get::<String>(0)?;
            Ok(! a1.starts_with("("))
        },
    )?;

    // create function "if_"  : is_id(a1) OR a1 == a2
    conn.create_scalar_function(
        "if_",
        2,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        |ctx| {
            let value = ctx.get_raw(0);
            match value {
                rusqlite::types::ValueRef::Null =>
                    Err(Error::InvalidFunctionParameterType(0, value.data_type())),
                rusqlite::types::ValueRef::Integer(_) =>
                    Ok(true),
                rusqlite::types::ValueRef::Real(_) =>
                    Ok(true),
                rusqlite::types::ValueRef::Text(_) => {
                    let value = ctx.get::<String>(1)?;
                    if ! value.starts_with("(") {  // an id
                        Ok(true)
                    } else {
                        let col = ctx.get::<String>(1)?;
                        Ok(value == col)
                    }
                },
                rusqlite::types::ValueRef::Blob(_) =>
                    Err(Error::InvalidFunctionParameterType(0, value.data_type())),
            }
        })?;

    // create function "join_"  : NOT is_id(a1) OR a1 == a2
    conn.create_scalar_function(
        "join_",
        2,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        |ctx| {
            let value = ctx.get_raw(0);
            match value {
                rusqlite::types::ValueRef::Null =>
                    Err(Error::InvalidFunctionParameterType(0, value.data_type())),
                rusqlite::types::ValueRef::Integer(col) =>{
                    Ok(value == rusqlite::types::ValueRef::Integer(col))
                },
                rusqlite::types::ValueRef::Real(col) => {
                    Ok(value == rusqlite::types::ValueRef::Real(col))
                },
                rusqlite::types::ValueRef::Text(_) => {
                    let value = ctx.get::<String>(1)?;
                    if value.starts_with("(") {  // not an id
                        Ok(true)
                    } else {
                        let col = ctx.get::<String>(1)?;
                        Ok(value == col)
                    }
                }
                rusqlite::types::ValueRef::Blob(_) =>
                    Err(Error::InvalidFunctionParameterType(0, value.data_type())),
            }
        })?;

    // create function "eq_"
    conn.create_scalar_function(  // LINK src/doc.md#_Equality
        "eq_",
        -1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let args = get_args(ctx)?;
            if args.len() == 2 {  // most frequent case
                if args[0] == args[1] {  // they might not be ids !
                    Ok("true".to_string())
                } else if is_id(&args[0]) && is_id(&args[1]) {
                    Ok("false".to_string())
                } else {
                    Ok(format!("(= {})", args.join(" ")))
                }
            } else {
                // if two ids are different, return false
                // otherwise, if all are ids, return true
                // else return the equality
                let mut last_id: Option<&String> = None;
                let mut all_ids = true;
                for arg in &args {
                    if is_id(arg) {
                        if let Some(last_id) = last_id {
                            if *last_id != *arg {
                                return Ok("false".to_string())
                            }
                        } else {
                            last_id = Some(arg)
                        }
                    } else {
                        all_ids = false;
                    }
                }
                if all_ids {
                    Ok("true".to_string())
                } else {
                    Ok(format!("(= {})", args.join(" ")))
                }
            }
        },
    )?;

    conn.create_scalar_function(
        "compare_",
        -1,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        |ctx| {
            // split args into strs, ints, reals values
            // raise error if both ints and reals
            // compare ints and return false if incorrect
            // compare reals and return false if incorrect
            // return true if no strs
            // return apply to all args
            let operator: String = ctx.get(0)?;

            // split args into strs, ints, reals values
            // raise error if both ints and reals
            let mut args = vec![];
            let mut strs = vec![];
            let mut ints = vec![];
            let mut reals = vec![];
            for i in 1..ctx.len() {
                let value = ctx.get_raw(i);
                match value {
                    rusqlite::types::ValueRef::Null =>
                        return Err(Error::InvalidFunctionParameterType(i, value.data_type())),
                    rusqlite::types::ValueRef::Integer(val) => {
                        if 0 < reals.len() {
                            return Err(Error::InvalidFunctionParameterType(i, value.data_type()))
                        }
                        args.push(val.to_string());
                        ints.push(val);
                    }
                    rusqlite::types::ValueRef::Real(val) => {
                        if 0 < ints.len() {
                            return Err(Error::InvalidFunctionParameterType(i, value.data_type()))
                        }
                        args.push(val.to_string());
                        reals.push(val);
                    }
                    rusqlite::types::ValueRef::Text(_) => {
                        let val = ctx.get::<String>(i)?;
                        args.push(val.clone());
                        strs.push(val);
                    }
                    rusqlite::types::ValueRef::Blob(_) =>
                        return Err(Error::InvalidFunctionParameterType(i, value.data_type())),
                }
            }

            // compare ints and return false if incorrect
            for (a, b) in ints.iter().zip(ints.iter().skip(1)) {
                let result = match operator.as_str() {
                    "<" => a < b,
                    "<=" => a <= b,
                    "distinct" => a != b,  // todo perf: this is an incomplete test
                    ">" => a > b,
                    ">=" => a >= b,
                    _ => return Err(Error::InvalidParameterName(operator))
                };
                if ! result {
                    return Ok("false".to_string())
                }
            }

            // compare reals and return false if incorrect
            for (a, b) in reals.iter().zip(reals.iter().skip(1)) {
                let result = match operator.as_str() {
                    "<" => a < b,
                    "<=" => a <= b,
                    "distinct" => a != b,  // todo perf: this is an incomplete test
                    ">" => a > b,
                    ">=" => a >= b,
                    _ => return Err(Error::InvalidParameterName(operator))
                };
                if ! result {
                    return Ok("false".to_string())
                }
            }

            // return true if no strs
            // else return apply to all args
            if strs.len() == 0 {
                Ok("true".to_string())
            } else {
                Ok(format!("({} {})", operator, args.join(" ")))
            }
        })?;

    // left_ associative: + - * div
    conn.create_scalar_function(
        "left_",
        -1,
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
        |ctx| {
            let operator: String = ctx.get(0)?;

            // split args into strs, ints, reals values
            // raise error if both ints and reals
            let mut args = vec![];
            let mut strs = vec![];
            let mut ints = vec![];
            let mut reals = vec![];
            for i in 1..ctx.len() {
                let value = ctx.get_raw(i);
                match value {
                    rusqlite::types::ValueRef::Null =>
                        return Err(Error::InvalidFunctionParameterType(i, value.data_type())),
                    rusqlite::types::ValueRef::Integer(val) => {
                        if 0 < reals.len() {
                            return Err(Error::InvalidFunctionParameterType(i, value.data_type()))
                        }
                        args.push(val.to_string());
                        ints.push(val);
                    }
                    rusqlite::types::ValueRef::Real(val) => {
                        if 0 < ints.len() {
                            return Err(Error::InvalidFunctionParameterType(i, value.data_type()))
                        }
                        args.push(val.to_string());
                        reals.push(val);
                    }
                    rusqlite::types::ValueRef::Text(_) => {
                        let val = ctx.get::<String>(i)?;
                        args.push(val.clone());
                        strs.push(val);
                    }
                    rusqlite::types::ValueRef::Blob(_) =>
                        return Err(Error::InvalidFunctionParameterType(i, value.data_type())),
                }
            }

            // reduce literals
            if 0 < ints.len() {
                match operator.as_str() {
                    "+" => {
                        let val = ints.into_iter().sum::<i64>();
                        if val != 0 || strs.len() == 0 {
                            strs.push(val.to_string())
                        }
                    },
                    "-" => {
                        if let rusqlite::types::ValueRef::Integer(val) = ctx.get_raw(1) {
                            if ints.len() + strs.len() == 1 {  // (- 2)
                                return Ok((-val).to_string())
                            }
                            let mut acc = val;
                            for i in ints.iter().skip(1) {
                                acc -= i;
                            };
                            if acc != 0 || strs.len() == 0 {
                                strs.insert(0, acc.to_string())
                            }
                        } else {
                            let mut acc = 0;
                            for i in ints.iter().skip(1) {
                                acc += i;
                            };
                            if acc != 0 || strs.len() == 0 {
                                strs.push(acc.to_string())
                            }
                        }
                    }
                    "*" => {
                        let val = ints.into_iter().product::<i64>();
                        if val != 1 || strs.len() == 0 {
                            strs.push(val.to_string())
                        }
                    },
                    "div" => {
                        if let rusqlite::types::ValueRef::Integer(val) = ctx.get_raw(1) {
                            let mut acc = val;
                            for i in ints.iter().skip(1) {
                                acc /= i;
                            };
                            if acc != 1 || strs.len() == 0 {
                                strs.insert(0, acc.to_string())
                            }
                        } else {
                            let mut acc = 1;
                            for i in ints.iter().skip(1) {
                                acc *= i;
                            };
                            if acc != 1 || strs.len() == 0 {
                                strs.push(acc.to_string())
                            }
                        }
                    }
                    _ => unreachable!()
                }
            }

            if 0 < reals.len() {
                match operator.as_str() {
                    "+" => {
                        let val = reals.into_iter().sum::<f64>();
                        if val != 0.0 || strs.len() == 0 {
                            strs.push(val.to_string())
                        }
                    },
                    "-" => {
                        if let rusqlite::types::ValueRef::Real(val) = ctx.get_raw(1) {
                            if reals.len() + strs.len()  == 1 {  // (- 2.0)
                                return Ok((-val).to_string())
                            }
                            let mut acc = val;
                            for i in reals.iter().skip(1) {
                                acc -= i;
                            };
                            if acc != 0.0 || strs.len() == 0 {
                                strs.insert(0, acc.to_string())
                            }
                        } else {
                            let mut acc = 0.0;
                            for i in reals.iter().skip(1) {
                                acc += i;
                            };
                            if acc != 0.0 || strs.len() == 0 {
                                strs.push(acc.to_string())
                            }
                        }
                    }
                    "*" => {
                        let val = reals.into_iter().product::<f64>();
                        if val != 1.0 || strs.len() == 0 {
                            strs.push(val.to_string())
                        }
                    },
                    "div" => {
                        if let rusqlite::types::ValueRef::Real(val) = ctx.get_raw(1) {
                            let mut acc = val;
                            for i in reals.iter().skip(1) {
                                acc /= i;
                            };
                            if acc != 1.0 || strs.len() == 0 {
                                strs.insert(0, acc.to_string())
                            }
                        } else {
                            let mut acc = 1.0;
                            for i in reals.iter().skip(1) {
                                acc *= i;
                            };
                            if acc != 1.0 || strs.len() == 0 {
                                strs.push(acc.to_string())
                            }
                        }
                    }
                    _ => unreachable!()
                }
            }

            if strs.len() == 1 {
                Ok(strs.join(" "))
            } else {
                Ok(format!("({} {})", operator, strs.join(" ")))
            }
        })?;

    // create function "abs_"
    conn.create_scalar_function(
        "abs_",
        1,                     // Number of arguments the function takes
        FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,                  // Deterministic (same input gives same output)
        |ctx| {                // The function logic
            let value = ctx.get_raw(0);
            match value {
                rusqlite::types::ValueRef::Null =>
                    return Err(Error::InvalidFunctionParameterType(0, value.data_type())),
                rusqlite::types::ValueRef::Integer(val) =>
                    Ok(val.abs().to_string()),
                rusqlite::types::ValueRef::Real(val) =>
                    Ok(val.abs().to_string()),
                rusqlite::types::ValueRef::Text(_) => {
                    let value = ctx.get::<String>(0)?;
                    Ok(format!("(abs {})", value))
                }
                rusqlite::types::ValueRef::Blob(_) =>
                    return Err(Error::InvalidFunctionParameterType(0, value.data_type())),
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

/// get the args from the context
fn get_args (ctx: &Context) -> Result<Vec<String>, Error> {
    let args: Vec<String> = (0..ctx.len())
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
    Ok(args)
}

#[inline]
fn is_id(value: &str) -> bool {
    ! value.starts_with("(")
}