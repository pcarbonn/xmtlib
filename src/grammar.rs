// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.
//! They are listed in the order given in Appendix B of the SMT-Lib standard.


use indexmap::IndexSet;
use peg::{error::ParseError, str::LineCol};

use crate::api::{*, Command::*};
use crate::solver::Solver;
use crate::private::sort::create_sort;

#[allow(unused_imports)]
use debug_print::{debug_println as dprintln};

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
            { Numeral(s.to_string()) }

        rule symbol(state: &mut ParsingState) -> Symbol
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
            {?
                // check that the sort is known or a variable
                if let Identifier::Simple(ref s) = s {
                    if ! state.solver.sorts.contains_key(&Sort::Sort(Identifier::Simple(s.clone()))) {
                        if ! state.variables.contains(s) {
                            return Err("known sort")  // Expected: known sort
                        }
                    }
                }
                Ok(Sort::Sort(s))
            }

            / _ "("
              s:identifier(state)
              i:( sort(state) ++ __ )
              _ ")"
            {?
                let sort = Sort::Parametric(s, i);
                if state.variables.len() == 0 {  // => the sort does not contain variables
                    create_sort(&sort, state.solver)
                } else {
                    Ok(sort)
                }
            }

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
                      v:( sort_variable(state) ++ __ )
                      _ ")" _ "("
                      c:( constructor_dec(state) ++ __ )
                      _ ")"
              _ ")"
            {
                state.variables = IndexSet::new();
                DatatypeDec::Par(v, c)
            }

            / _ "("
              c:( constructor_dec(state) ++ __ )
              _ ")"
            { DatatypeDec::DatatypeDec(c) }

            // a variation of symbol() that updates the list of variables
            rule sort_variable(state: &mut ParsingState) -> Symbol
                = s:symbol(state)
                {
                    state.variables.insert(s.clone());
                    s
                }

        rule command(state: &mut ParsingState) -> Command
            = _ "("
              command:( check_sat(state)
                      / declare_datatype(state)
                      / debug()
                      / verbatim(state))
              _ ")"
            { command }

        rule check_sat(state: &mut ParsingState) -> Command
            = _ "check-sat"
            { CheckSat }

        rule declare_datatype(state: &mut ParsingState) -> Command
            = _ "declare-datatype"
              s:symbol(state)
              decl:datatype_dec(state)
            {
                match decl {
                    DatatypeDec::DatatypeDec(_) => {
                        let sort = Sort::Sort(Identifier::Simple(s.clone()));
                        state.solver.sorts.insert(sort, decl.clone());
                    },
                    DatatypeDec::Par(_, _) => {
                        state.solver.parametric_datatypes.insert(s.clone(), decl.clone());
                    }
                }
                DeclareDatatype(s, decl)
            }

        rule debug() -> Command
            = _ "x-debug" __ object:simple_symbol()
            { XDebug (object) }

        rule verbatim(state: &mut ParsingState) -> Command
            = _ command: ( "assert"
                         / "check-sat-assuming"
                         / "declare-const"
                         / "declare-datatypes"
                         / "declare-fun"
                         / "declare-sort"
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
              s: (s_expr(state) ** __)
            { Verbatim(format!("{}", SExpr::Paren(s))) }

        pub rule script(state: &mut ParsingState) -> Vec<Command>
            = l:(command(state)* ) _
            { l }

        // //////////////////////////// Command responses ///////////////////////
    }
  }

/// Parses the source code in SMT-Lib format into a list of commands.
pub(crate) fn parse(
    source: &str,
    state: &mut ParsingState
) -> Result<Vec<Command>, ParseError<LineCol>> {
    smt_lib::script(source , state)
}

/// A ParsingState contains the list of declared symbols,
/// and the list of variables in the current scope.
pub(crate) struct ParsingState<'a> {
    solver: &'a mut Solver,
    variables: IndexSet<Symbol>,
}

impl<'a> ParsingState<'a> {
    pub(crate) fn new(solver: &'a mut Solver) -> ParsingState {
        ParsingState { solver, variables: IndexSet::new(), }
    }
}