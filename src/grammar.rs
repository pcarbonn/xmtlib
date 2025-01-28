// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.
//! They are listed in the order given in Appendix B of the SMT-Lib standard.


use peg::{error::ParseError, str::LineCol};

use crate::api::{*, Command::*};

#[allow(unused_imports)]
use debug_print::debug_println as dprintln;

// TODO store offset in API


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
            { Numeral(s.to_string().parse().unwrap()) }

        rule symbol() -> Symbol
            = s:( simple_symbol()
                / complex_symbol()
                )
            { Symbol(s) }

            rule simple_symbol() -> String
                = _ s:(quiet!{$([           'a'..='z'|'A'..='Z'|'_'|'+'|'-'|'/'|'*'|'='|'%'|'?'|'!'|'.'|'$'|'_'|'&'|'^'|'<'|'>'|'@']
                                [ '0'..='9'|'a'..='z'|'A'..='Z'|'_'|'+'|'-'|'/'|'*'|'='|'%'|'?'|'!'|'.'|'$'|'_'|'&'|'^'|'<'|'>'|'@']*
                                )}
                    / expected!("identifier"))
                { s.to_string() }

            rule complex_symbol() -> String
                = _ s:(quiet!{$(['|'] [^ '|' | '\\' ]* ['|'])}
                    / expected!("identifier"))
                { s.to_string() }

        // //////////////////////////// S-expressions ///////////////////////////

        rule s_expr() -> SExpr
            = s: symbol()
            { SExpr::Symbol(s) }

            / _ "(" _
              s:( s_expr() ** __ )
              _ ")"
            { SExpr::Paren(s) }

        // //////////////////////////// Identifiers  ////////////////////////////

        rule index() -> Index
            = n:numeral()
            { Index::Numeral(n) }
            / s:symbol()
            { Index::Symbol(s) }

        rule identifier() -> Identifier
            = s:symbol()
            { Identifier::Simple(s) }

            / _ "(" _ "_"
              s:symbol()
              i:( index() ++ __ )
              _ ")"
            { Identifier::Indexed(s, i) }

        // //////////////////////////// Sorts        ////////////////////////////

        rule sort() -> Sort
            = id:identifier()
            { Sort::Sort(id) }

            / _ "("
              id:identifier()
              sorts:( sort() ++ __ )
              _ ")"
            { Sort::Parametric(id, sorts) }

        // //////////////////////////// Attributes   ////////////////////////////
        // //////////////////////////// Terms        ////////////////////////////
        // //////////////////////////// Theories     ////////////////////////////
        // //////////////////////////// Logics       ////////////////////////////
        // //////////////////////////// Info flags   ////////////////////////////
        // //////////////////////////// Command Options /////////////////////////
        // //////////////////////////// Commands     ////////////////////////////

        rule sort_dec() -> SortDec
            = _ "("
              s:symbol()
              n:numeral()
              _ ")"
            { SortDec(s, n) }

        rule selector_dec() -> SelectorDec
            = _ "("
              s:symbol()
              ss:sort()
              _ ")"
            { SelectorDec(s, ss) }

        rule constructor_dec() -> ConstructorDec
            = _ "("
              s:symbol()
              ss:( selector_dec() ** __ )
              _ ")"
            { ConstructorDec(s, ss) }

        rule datatype_dec() -> DatatypeDec
            = _ "(" _ "par"
                      _ "("
                      v:( symbol() ++ __ )
                      _ ")" _ "("
                      c:( constructor_dec() ++ __ )
                      _ ")"
              _ ")"
            { DatatypeDec::Par(v, c) }

            / _ "("
              c:( constructor_dec() ++ __ )
              _ ")"
            { DatatypeDec::DatatypeDec(c) }

        rule command() -> Command
            = _ "("
              command:( check_sat()
                      / declare_const()
                      / declare_datatype()
                      / declare_datatypes()
                      / declare_fun()
                      / declare_sort()
                      / define_sort()
                      / debug()
                      / verbatim())
              _ ")"
            { command }

        rule check_sat() -> Command
            = _ "check-sat"
            { CheckSat }

        rule declare_const() -> Command
            = _ "declare-const" symbol:symbol() sort:sort()
            { DeclareConst(symbol, sort) }

        rule declare_datatype() -> Command
            = _ "declare-datatype"
              s:symbol()
              decl:datatype_dec()
            { DeclareDatatype(s, decl) }

        rule declare_datatypes() -> Command
            = _ "declare-datatypes" _ "("
              s:(sort_dec() ++ __)
              _ ")" _ "("
              decl:(datatype_dec() ++ __)
              _ ")"
            { DeclareDatatypes(s, decl) }

        rule declare_fun() -> Command
            = _ "declare-fun"
              symbol:symbol()
              _ "(" domain:(sort() ** __) _ ")"
              co_domain:sort()
            { DeclareFun(symbol, domain, co_domain) }

        rule declare_sort() -> Command
            = _ "declare-sort" symbol:symbol() numeral:numeral()
            { DeclareSort(symbol, numeral) }

        rule define_sort() -> Command
            = _ "define-sort"
              symbol:symbol()
              _ "("
              variables:(symbol() ** _)
              _ ")"
              sort:sort()
            { DefineSort(symbol, variables, sort)}


        // //////////////////////////// S-Commands     ////////////////////////////

        rule debug() -> Command
            = _ "x-debug"
            __ typ:simple_symbol()
            __ object:simple_symbol()
            { XDebug (typ, object) }

        rule verbatim() -> Command
            = _ command: ( "assert"
                         / "check-sat-assuming"
                         / "define-fun"
                         / "define-fun-rec"
                         / "define-funs-rec"
                         / "echo"
                         / "get-assertions"
                         / "get-assignment"
                         / "get-info"
                         / "get-model"
                         / "get-option"
                         / "get-proof"
                         / "get-unsat-assumptions"
                         / "get-unsat-core"
                         / "get-value"
                         / "pop"
                         / "push"
                         / "reset"
                         / "reset-assertions"
                         / "set-info"
                         / "set-logic"
                         / "set-option"
                         / "simplify"
                         )
              s: (s_expr() ** __)
            { Verbatim(format!("{}", SExpr::Paren(s))) }

        pub rule script() -> Vec<Command>
            = l:(command()* ) _
            { l }

        // //////////////////////////// Command responses ///////////////////////
    }
  }


/// Parses the source code in SMT-Lib format into a list of commands.
pub(crate) fn parse(
    source: &str,

) -> Result<Vec<Command>, ParseError<LineCol>> {
    smt_lib::script(source)
}
