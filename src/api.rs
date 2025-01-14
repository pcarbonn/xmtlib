// Copyright Pierre Carbonnelle, 2025.

//! This module defines the abstract syntax tree (AST) of XMT-Lib.

// It also contains macros to create XMT-Lib commands programmatically.

use crate::error::Offset;

#[derive(PartialEq, Eq, Debug)]
pub enum Command {
    CheckSat,
}


#[macro_export]
macro_rules! CheckSat {
    ( ) => { Command::CheckSat }
}


#[test]
fn parse_test() {
    use crate::api::Command::*;
    use crate::grammar::parse;
    assert_eq!(parse("(check-sat) "),
               Ok(vec![CheckSat]));
}
