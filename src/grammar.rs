// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.

use peg::{error::ParseError, str::LineCol};

use crate::api::Command::{self, *};
use crate::error::Offset;

peg::parser!{
    pub grammar smt_lib() for str {
        rule _  = [' ' | '\n']*
        rule __ = [' ' | '\n']+

        pub rule commands(state: &mut ParsingState) -> Vec<Command>
            = l:(command(state) * ) _ { l }

        rule command(state: &mut ParsingState) -> Command
            = _ "(" _
              command:( check_sat(state) )
              _ ")" { command }

        rule check_sat(state: &mut ParsingState) -> Command
            = "check-sat" { CheckSat }
    }
  }

/// Parses the source code in SMT-Lib format into a list of commands.
pub fn parse(source: &str) -> Result<Vec<Command>, ParseError<LineCol>> {
    let mut state = ParsingState::default();
    smt_lib::commands(source , &mut state)
}

/// A ParsingState contains the list of declared symbols,
/// and the list of variables in the current scope.
struct ParsingState {

}

impl Default for ParsingState {
    fn default() -> ParsingState {
        ParsingState {}
    }
}