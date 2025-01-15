// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.

use peg::{error::ParseError, str::LineCol};

use crate::api::Command::{self, *};
use crate::error::Offset;

peg::parser!{
    pub grammar smt_lib() for str {
        // optional whitespace.  Must precede any token
        rule _  = ( [ ' ' | '\n' | '\t' | '\r']
                  / (";" [^ '\n' | '\r']* ['\n' | '\r'])
                  )*
        // mandatory whitespace
        rule __ = ( [ ' ' | '\n' | '\t' | '\r']
        / (";" [^ '\t' | '\r']* ['\t' | '\r'])
        )+

        pub rule commands(state: &mut ParsingState) -> Vec<Command>
            = l:(command(state)* ) _
            { l }

        rule command(state: &mut ParsingState) -> Command
            = _ "("
              command:( check_sat(state)
                      / verbatim(state))
              _ ")"
            { command }

        rule check_sat(state: &mut ParsingState) -> Command
            = _ "check-sat"
            { CheckSat }

        rule verbatim(state: &mut ParsingState) -> Command
            = s:(s_expr(state)*)
            { Verbatim(format!("({})", s.join(" "))) }

        rule s_expr(state: &mut ParsingState) -> String
            = s:( s_expr_list(state) / symbol(state) )
            { s }

        rule s_expr_list(state: &mut ParsingState) -> String
            = _ "(" _
               s:( s_expr(state)* )
               _ ")"
            { format!("({})", s.join(" ")) }

        rule symbol(state: &mut ParsingState) -> String
            = s:( simple_symbol()
                / complex_symbol()
                )
            { s }

        rule simple_symbol() -> String
            = _ s:(quiet!{$([             'a'..='z' | 'A'..='Z' | '_' | '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '&' | '^' | '<' | '>' | '@']
                        [ '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' | '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '&' | '^' | '<' | '>' | '@']*
                        )}
                / expected!("identifier"))
            { s.to_string() }

        rule complex_symbol() -> String
            = _ s:(quiet!{$(['|'] [^ '|' | '\\' ]* ['|'])}
                / expected!("identifier"))
            { s.to_string() }
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