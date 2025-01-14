// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.

use peg::{error::ParseError, str::LineCol};

use crate::api::Command::{self, *};
use crate::error::Offset;

peg::parser!{
    pub grammar smt_lib() for str {
        rule _  = [' ' | '\n']*
        rule __ = [' ' | '\n']+

        pub rule commands() -> Vec<Command>
            = l:(command() * ) _ { l }

        rule command() -> Command
            = _ "(" _
              command:( check_sat() )
              _ ")" { command }

        rule check_sat() -> Command
            = "check-sat" { CheckSat }
    }
  }

/// Parses the source code in SMT-Lib format into a list of commands.
pub fn parse(source: &str) -> Result<Vec<Command>, ParseError<LineCol>> {
    smt_lib::commands(source)
}
