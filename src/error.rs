// Copyright Pierre Carbonnelle, 2025.

use peg::{error::ParseError, str::LineCol};
use rusqlite::Error as SqlError;
use thiserror::Error;

/// The number of characters since the begin of a source file.
///
/// Used for error reporting.
#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Offset(pub usize);

#[derive(Error, Debug, PartialEq)]
pub enum SolverError {

    #[error("{0}")]
    ParseError(#[from] ParseError<LineCol>),

    #[error("{0}")]
    ExprError(String, Option<Offset>),

    #[error("Database error: {0}")]
    DatabaseError(#[from] SqlError),

    #[error("{0}")]
    InternalError(usize),  // can't be fixed by the user
}

use crate::error::SolverError::*;


/// Show the error in the context of the relevant source code.
pub fn format_error(input: &str, e: SolverError) -> String {
    match e {

        ParseError(e) =>
            pretty_print(input, e.location, format!("Expected: {}", e.expected)),

        DatabaseError(e) => format!("****** Database Error: {}", e),

        ExprError(msg, offset) =>
            if let Some(offset_) = offset {
                match offset_to_line_col_utf8(&input, offset_) {
                    None => msg,
                    Some(location) =>
                        pretty_print(input, location, msg)
                }
            } else {
                format!("****** Error: {}", msg)
            },

        InternalError(n) => format!("****** Internal Error: {}", n)
    }
}

/// Show the error in the context of the `input` source code.
fn pretty_print(input: &str, location: LineCol, msg: String) -> String {
    let source = input.lines().nth(location.line-1).unwrap();
    chic::Error::new(format!("at position ({}, {}): {}", location.line, location.column, msg))
        .error(
            location.line,
            location.column - 1,
            location.column,
            &source,
            msg,
        )
        .to_string()

}

fn offset_to_line_col_utf8(s: &str, offset: Offset) -> Option<LineCol> {
    if offset.0 > s.len() {
        return None;
    }

    let mut current_offset = 0;

    for (line_number, line) in s.split('\n').enumerate() {
        let char_indices: Vec<_> = line.char_indices().collect();
        let line_length = line.len() + 1; // Include the newline character

        if current_offset + line_length > offset.0 {
            for (column, (byte_index, _)) in char_indices.iter().enumerate() {
                if current_offset + byte_index >= offset.0 {
                    return Some(LineCol{column: column + 1, line: line_number + 1, offset:offset.0});
                }
            }
        }

        current_offset += line_length;
    }

    None
}