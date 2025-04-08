// Copyright Pierre Carbonnelle, 2025.

//! This module defines the grammar of XMT-Lib.
//! The nodes of the syntax tree are listed in the order given in Appendix B of the SMT-Lib standard.


use peg::{error::ParseError, str::LineCol};

use crate::api::{*, Command::*};
use crate::error::Offset;

#[allow(unused_imports)]
use debug_print::debug_println as dprintln;

// TODO store offset in API


peg::parser!{
    pub grammar smt_lib() for str {

        // //////////////////////////// Auxiliary ////////////////////////////

        // optional whitespace.  Must precede any token
        rule _  = ( [ ' ' | '\n' | '\t' | '\r']
                  / (";" [^ '\n' | '\r']* ['\n' | '\r' ])
                  )*

        // mandatory whitespace
        rule __ = ( [ ' ' | '\n' | '\t' | '\r']
                  / (";" [^ '\n' | '\r']* ['\n' | '\r' ])
                  )+
        // //////////////////////////// Other tokens ////////////////////////////

        rule numeral() -> Numeral
            = "0" { Numeral(0) }

            /  s:(quiet!{$("-"? ['1'..='9'] ['0'..='9']* )}
               / expected!("numeral"))
              { Numeral(s.to_string().parse().unwrap()) }

        rule decimal() -> Decimal
            = numerator:numeral() "." denominator:(quiet!{$(['0'..='9']+)} / expected!("numeral"))
             { Decimal(format!("{numerator}.{denominator}")) }

        rule hexadecimal() -> Hexadecimal
            = "#x" s:(quiet!{$( ['0'..='9' | 'A'..='F' | 'a'..='f']+ )}
                    / expected!("hexadecimal"))
           { Hexadecimal(format!("#x{s}")) }

        rule binary() -> Binary
            = "#b" s:(quiet!{$(['0' | '1']+ )}
            / expected!("binary"))
            { Binary(format!("#b{s}")) }

        rule string() -> String_
            = "\""
              string: string_char()*
              "\""
              { String_(string.join("")) }

              rule string_char() -> String
                  = chars: [^'"']+ { chars.iter().collect() }
                  / "\"\"" { "\"\"".to_string() }


        rule simple_symbol() -> String
            = s:(quiet!{$([           'a'..='z'|'A'..='Z'|'_'|'+'|'-'|'/'|'*'|'='|'%'|'?'|'!'|'.'|'$'|'_'|'&'|'^'|'<'|'>'|'@']
                          [ '0'..='9'|'a'..='z'|'A'..='Z'|'_'|'+'|'-'|'/'|'*'|'='|'%'|'?'|'!'|'.'|'$'|'_'|'&'|'^'|'<'|'>'|'@']*
                          )}
                / expected!("simple symbol"))
            { s.to_string() }

        rule symbol() -> Symbol
            = s:simple_symbol()
              { Symbol(s) }

            / s:(quiet!{$(['|'] [^ '|' | '\\' ]* ['|'] )}
                   / expected!("symbol"))
              { Symbol(s.to_string()) }

        rule keyword() -> Keyword
            = ":" symbol:simple_symbol()
              { Keyword(format!(":{symbol}")) }

        // //////////////////////////// S-expressions ///////////////////////////

        rule spec_constant() -> SpecConstant
            = decimal: decimal()
              { SpecConstant::Decimal(decimal) }

            / numeral:numeral()
              { SpecConstant::Numeral(numeral) }

            / hexadecimal:hexadecimal()
              { SpecConstant::Hexadecimal(hexadecimal) }

            / binary:binary()
              { SpecConstant::Binary(binary) }

            / string:string()
              { SpecConstant::String(string) }

        rule s_expr() -> SExpr
            = s: symbol()
            { SExpr::Symbol(s) }

            / "(" _
              s:( s_expr() ** __ ) _
              ")"
            { SExpr::Paren(s) }

        // //////////////////////////// Identifiers  ////////////////////////////

        rule index() -> Index
            = n:numeral()
            { Index::Numeral(n) }
            / s:symbol()
            { Index::Symbol(s) }

        rule identifier() -> Identifier
            = start:position!() s:symbol()
            { Identifier::Simple(s, Offset(start)) }

            / start:position!() "(" _
              "_" __
              s:symbol() __
              i:( index() ++ __ ) _
              ")"
            { Identifier::Indexed(s, i, Offset(start)) }

        // //////////////////////////// Sorts        ////////////////////////////

        rule sort() -> Sort
            = id:identifier()
            { Sort::Sort(id) }

            / "(" _
              id:identifier() _
              sorts:( sort() ++ __ ) _
              ")"
            { Sort::Parametric(id, sorts) }

        // //////////////////////////// Attributes   ////////////////////////////

        rule attribute_value() -> AttributeValue
            = spec_constant:spec_constant()
              { AttributeValue::SpecConstant(spec_constant) }

            / symbol:symbol()
              { AttributeValue::Symbol(symbol) }

            / "(" _
              s_expr:s_expr() _
              ")"
              { AttributeValue::Expr(s_expr) }

        rule attribute() -> Attribute
            = keyword:keyword() _
              attribute_value:attribute_value()
            { Attribute::WithValue(keyword, attribute_value)}

            / keyword:keyword()
            { Attribute::Keyword(keyword) }

        // //////////////////////////// Terms        ////////////////////////////

        rule qual_identifier() -> QualIdentifier
            = identifier:identifier()
              { QualIdentifier::Identifier(identifier) }

            / "(" _
               "as" _
               identifier:identifier() _
               sort:sort() _
               ")"
              { QualIdentifier::Sorted(identifier, sort)}

        rule var_binding() -> VarBinding
            = "(" _
              symbol:symbol() _
              term:term() _
              ")"
              { VarBinding(symbol, term) }

        rule sorted_var() -> SortedVar
            = "(" _
              symbol:symbol() _
              sort:sort() _
              ")"
              { SortedVar(symbol, sort) }

        rule pattern() -> Pattern
            = symbol:symbol()
              { Pattern::Symbol(symbol) }

            / "(" _
              symbol:symbol() _
              symbols:(symbol() ++ __) _
              ")"
              { Pattern::Application(symbol, symbols) }

        rule match_case() -> MatchCase
            = "(" _
              pattern:pattern() _
              term:term() _
              ")"
            { MatchCase(pattern, term) }

        rule term() -> Term
            = start:position!() spec_constant:spec_constant()
              { Term::SpecConstant(spec_constant, Offset(start)) }

            / start:position!() qual_identifier:qual_identifier()
              { Term::Identifier(qual_identifier, Offset(start)) }

            / start:position!() "(" _
              qual_identifier:qual_identifier() _
              terms:( term() ++ __ ) _
              ")"
              { Term::Application(qual_identifier, terms, Offset(start)) }

            / start:position!() "(" _
              "let" _
              "(" _
                  var_bindings:(var_binding() ++ __) _
              ")" _
              term:term() _
              ")"
              { Term::Let(var_bindings, Box::new(term), Offset(start)) }

            / start:position!() "(" _
              "forall" _
              "(" _
                sorted_vars:(sorted_var() ++ __) _
              ")" _
              term:term() _
              ")"
              { Term::Forall(sorted_vars, Box::new(term), Offset(start)) }

            / start:position!() "(" _
              "exists" _
              "(" _
                sorted_vars:(sorted_var() ++ __) _
              ")" _
              term:term() _
              ")"
              { Term::Exists(sorted_vars, Box::new(term), Offset(start)) }

            / start:position!() "(" _
              "match" _
              term:term() _
              "(" _
                match_cases:(match_case() ++ __) _
              ")" _
              ")"
              { Term::Match(Box::new(term), match_cases, Offset(start))}

            / start:position!() "(" _
              "!" _
              term:term() _
              attributes:(attribute() ++ __) _
              ")"
              { Term::Annotation(Box::new(term), attributes, Offset(start))}

        rule xid() -> Term  // an id
            = start:position!() spec_constant:spec_constant()
              { Term::SpecConstant(spec_constant, Offset(start)) }

            / start:position!() qual_identifier:qual_identifier()
              { Term::Identifier(qual_identifier, Offset(start)) }

            / start:position!() "(" _
              qual_identifier:qual_identifier() _
              terms:( xid() ++ __ ) _
              ")"
              { Term::Application(qual_identifier, terms, Offset(start)) }

        rule xtuple() -> XTuple
            = "(" _
              terms: ( xid() ** __ ) _
              ")"
              { XTuple(terms) }

        // //////////////////////////// Theories     ////////////////////////////
        // //////////////////////////// Logics       ////////////////////////////
        // //////////////////////////// Info flags   ////////////////////////////
        // //////////////////////////// Command Options /////////////////////////

        rule option() -> Option_
            = attribute: attribute()
            { Option_::Attribute(attribute) }

        // //////////////////////////// Commands     ////////////////////////////

        rule sort_dec() -> SortDec
            = "(" _
              s:symbol() _
              n:numeral() _
              ")"
            { SortDec(s, n) }

        rule selector_dec() -> SelectorDec
            = "(" _
              s:symbol() _
              ss:sort() _
              ")"
            { SelectorDec(s, ss) }

        rule constructor_dec() -> ConstructorDec
            = "(" _
              s:symbol() _
              ss:( selector_dec() ** __ ) _
              ")"
            { ConstructorDec(s, ss) }

        rule datatype_dec() -> DatatypeDec
            = "(" _
               "par" _
               "(" _
                  v:( symbol() ++ __ ) _
                ")" _
                "(" _
                    c:( constructor_dec() ++ __ ) _
                ")" _
                ")"
            { DatatypeDec::Par(v, c) }

            / "(" _
              c:( constructor_dec() ** _ ) _
              ")"
            { DatatypeDec::DatatypeDec(c) }

        rule set_option() -> Command
            = "set-option" _
              option:option()
            { SetOption(option) }

        rule command() -> Command
            = "(" _
              command:( assert()
                      / check_sat()
                      / declare_const()
                      / declare_datatype()
                      / declare_datatypes()
                      / declare_fun()
                      / declare_sort()
                      / define_sort()
                      / set_option()
                      / xinterpret_pred()
                      / xinterpret_fun()
                      / xdebug()
                      / xground()
                      / verbatim()) _
              ")"
            { command }

        rule assert() -> Command
            = "assert" __
              term:term()
            { Assert(term) }

        rule check_sat() -> Command
            = "check-sat"
            { CheckSat }

        rule declare_const() -> Command
            = "declare-const" _
              symbol:symbol() _
              sort:sort()
            { DeclareConst(symbol, sort) }

        rule declare_datatype() -> Command
            = "declare-datatype" _
              s:symbol() _
              decl:datatype_dec()
            { DeclareDatatype(s, decl) }

        rule declare_datatypes() -> Command
            ="declare-datatypes" _
             "(" _
                s:(sort_dec() ++ __) _
              ")" _
              "(" _
                decl:(datatype_dec() ++ __) _
              ")"
            { DeclareDatatypes(s, decl) }

        rule declare_fun() -> Command
            = "declare-fun" _
              symbol:symbol() _
              "(" _
                  domain:(sort() ** __) _
              ")" _
              co_domain:sort()
            { DeclareFun(symbol, domain, co_domain) }

        rule declare_sort() -> Command
            = "declare-sort" _
              symbol:symbol() _
              numeral:numeral()
            { DeclareSort(symbol, numeral) }

        rule define_sort() -> Command
            = "define-sort" _
              symbol:symbol() _
              "(" _
                variables:(symbol() ** _) _
              ")" _
              sort:sort()
            { DefineSort(symbol, variables, sort)}


        // //////////////////////////// X-Commands     ////////////////////////////

        rule xinterpret_pred() -> Command
            = "x-interpret-pred" _
              identifier: identifier() _
              tuples: ( xtuple() ** _ )
              { XInterpretPred(identifier, tuples) }

        rule ftuple() -> (XTuple, Term)
            = "(" _
              tuple: xtuple() _
              term: term() _
              ")"
            { (tuple, term) }

        rule xinterpret_fun() -> Command
            = "x-interpret-fun" _
              identifier: identifier() _
              "(" _
                tuples: (ftuple() ** _) _
              ")" _
              else_: term()?
              { XInterpretFun(identifier, tuples, else_) }

        rule xdebug() -> Command
            = "x-debug" _
              typ:identifier() _
              object:identifier()
              { XDebug (typ, object) }

        rule xground() -> Command
            = "x-ground"
            { XGround }

        rule verbatim() -> Command
            = command: ( "check-sat-assuming"
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
                         / "simplify"
                         ) _
              s: (s_expr() ** __)
            { Verbatim(format!("{}", SExpr::Paren(s))) }

        pub rule script() -> Vec<Command>
            = _ l:(command()** _ ) _
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
