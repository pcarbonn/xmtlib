// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.
//! They are listed in the order given in Appendix B of the SMT-Lib standard.

use peg::{error::ParseError, str::LineCol};

use crate::api::{*, Command::*};
use crate::error::Offset;

peg::parser!{
    pub grammar smt_lib() for str {

        // //////////////////////////// Auxiliary ////////////////////////////

        // optional whitespace.  Must precede any token
        rule _  = ( [ ' ' | '\n' | '\t' | '\r']
                  / (";" [^ '\n' | '\r']* ['\n' | '\r'])
                  )*
        // mandatory whitespace
        rule __ = ( [ ' ' | '\n' | '\t' | '\r']
                  / (";" [^ '\t' | '\r']* ['\t' | '\r'])
                  )+
        // //////////////////////////// Other tokens ////////////////////////////

        rule numeral() -> Numeral
            = _ s:(quiet!{$(['0'..='9'] ['0'..='9']* )}
                / expected!("numeral"))
            { Numeral(s.to_string()) }

        rule symbol(state: &mut ParsingState) -> Symbol
            = s:( simple_symbol()
                / complex_symbol()
                )
            { Symbol(s) }

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

        // //////////////////////////// S-expressions ///////////////////////////

        rule s_expr(state: &mut ParsingState) -> SExpr
            = s: symbol(state)
            { SExpr::Symbol(s) }
            / _ "(" _
              s:( s_expr(state) ** __ )
              _ ")"
            { SExpr::Paren(s) }

        // //////////////////////////// Identifiers  ////////////////////////////

        rule index(state: &mut ParsingState) -> Index
            = n:numeral()
            { Index::Numeral(n) }
            / s:symbol(state)
            { Index::Symbol(s) }

        rule identifier(state: &mut ParsingState) -> Identifier
            = s:symbol(state)
            { Identifier::Simple(s) }
            / _ "(" _ "_"
              s:symbol(state)
              i:( index(state) ++ __ )
              _ ")"
            { Identifier::Indexed(s, i) }

        // //////////////////////////// Sorts        ////////////////////////////

        rule sort(state: &mut ParsingState) -> Sort
            = s:identifier(state)
            { Sort::Sort(s) }
            / _ "("
              s:identifier(state)
              i:( sort(state) ++ __ )
              _ ")"
            { Sort::Parametric(s, i) }

        // //////////////////////////// Attributes   ////////////////////////////
        // //////////////////////////// Terms        ////////////////////////////
        // //////////////////////////// Theories     ////////////////////////////
        // //////////////////////////// Logics       ////////////////////////////
        // //////////////////////////// Info flags   ////////////////////////////
        // //////////////////////////// Command Options /////////////////////////
        // //////////////////////////// Commands     ////////////////////////////

        rule selector_dec(state: &mut ParsingState) -> SelectorDec
            = _ "("
              s:symbol(state)
              ss:sort(state)
              _ ")"
            { SelectorDec(s, ss) }

        rule constructor_dec(state: &mut ParsingState) -> ConstructorDec
            = _ "("
              s:symbol(state)
              ss:( selector_dec(state) ** __ )
              _ ")"
            { ConstructorDec(s, ss) }

        rule datatype_dec(state: &mut ParsingState) -> DatatypeDec
            = _ "(" _ "par"
                      _ "("
                      v:( symbol(state) ++ __ )
                      _ ")" _ "("
                      c:( constructor_dec(state) ++ __ )
                      _ ")"
              _ ")"
            { DatatypeDec::Par(v, c) }
            / _ "("
              c:( constructor_dec(state) ++ __ )
              _ ")"
            { DatatypeDec::DatatypeDec(c) }

        rule command(state: &mut ParsingState) -> Command
            = _ "("
              command:( check_sat(state)
                      / declare_datatype(state)
                      / verbatim(state))
              _ ")"
            { command }

        rule check_sat(state: &mut ParsingState) -> Command
            = _ "check-sat"
            { CheckSat }

        rule declare_datatype(state: &mut ParsingState) -> Command
            = _ "declare-datatype"
              s:symbol(state)
              d:datatype_dec(state)
            { DeclareDatatype(s, d) }

        rule verbatim(state: &mut ParsingState) -> Command
            = s:(s_expr(state) ** __)
            { Verbatim(format!("{}", SExpr::Paren(s))) }

        pub rule script(state: &mut ParsingState) -> Vec<Command>
            = l:(command(state)* ) _
            { l }

        // //////////////////////////// Command responses ///////////////////////
    }
  }

/// Parses the source code in SMT-Lib format into a list of commands.
pub fn parse(source: &str) -> Result<Vec<Command>, ParseError<LineCol>> {
    let mut state = ParsingState::default();
    smt_lib::script(source , &mut state)
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