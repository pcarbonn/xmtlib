// Copyright Pierre Carbonnelle, 2025.

//! This module defines the abstract syntax tree (AST) of XMT-Lib.
//!
//! The nodes are listed in the order given in Appendix B of the SMT-Lib standard.

// It also implements Display.

use itertools::Itertools;

// //////////////////////////// Other tokens ////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Numeral(pub String);
impl std::fmt::Display for Numeral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(rest) = self.0.strip_prefix('-') {
            write!(f, "(- {rest})")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);
impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// //////////////////////////// S-expressions ///////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SExpr {
    // /// `<spec_constant>`
    // SpecConstant(SpecConstant),
    /// `<symbol>`
    Symbol(Symbol),
    // /// `<reserved>`
    // Reserved(Reserved),
    // /// `<keyword>`
    // Keyword(Keyword),
    /// `(<s_expr>*)`
    Paren(Vec<SExpr>),
}
impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            // Self::SpecConstant(m0) => write!(f, "{}", m0),
            Self::Symbol(m0) => write!(f, "{}", m0),
            // Self::Reserved(m0) => write!(f, "{}", m0),
            // Self::Keyword(m0) => write!(f, "{}", m0),
            Self::Paren(m0) => write!(f, "({})", m0.iter().format(" ")),
        }
    }
}
// //////////////////////////// Identifiers  ////////////////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Index {
    /// `<numeral>`
    Numeral(Numeral),
    /// `<symbol>`
    Symbol(Symbol),
}
impl std::fmt::Display for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Numeral(m0) => write!(f, "{}", m0),
            Self::Symbol(m0) => write!(f, "{}", m0),
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Identifier {
    /// `<symbol>`
    Simple(Symbol),
    /// `(_ <symbol> <index>+)`
    Indexed(Symbol, Vec<Index>),
}
impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Simple(m0) => write!(f, "{}", m0),
            Self::Indexed(m0, m1) => write!(f, "(_ {} {})", m0, m1.iter().format(" ")),
        }
    }
}

// //////////////////////////// Sorts        ////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// `<identifier>`
    Sort(Identifier),
    /// `(<identifier> <sort>+)`
    Parametric(Identifier, Vec<Sort>),
}
impl std::fmt::Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Sort(m0) => write!(f, "{}", m0),
            Self::Parametric(m0, m1) => write!(f, "({} {})", m0, m1.iter().format(" ")),
        }
    }
}


// //////////////////////////// Attributes   ////////////////////////////
// //////////////////////////// Terms        ////////////////////////////
// //////////////////////////// Theories     ////////////////////////////
// //////////////////////////// Logics       ////////////////////////////
// //////////////////////////// Info flags   ////////////////////////////
// //////////////////////////// Command Options /////////////////////////
// //////////////////////////// Commands     ////////////////////////////

/// `(<symbol> <sort>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SelectorDec(pub Symbol, pub Sort);
impl std::fmt::Display for SelectorDec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

/// `(<symbol> <selector_dec>*)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorDec(pub Symbol, pub Vec<SelectorDec>);
impl std::fmt::Display for ConstructorDec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1.iter().format(" "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DatatypeDec {
    /// `(<constructor_dec>+)`
    DatatypeDec(Vec<ConstructorDec>),
    /// `(par (<symbol>+) (<constructor_dec>+))`
    Par(Vec<Symbol>, Vec<ConstructorDec>),
}
impl std::fmt::Display for DatatypeDec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::DatatypeDec(m0) => write!(f, "({})", m0.iter().format(" ")),
            Self::Par(m0, m1) => {
                write!(
                    f, "(par ({}) ({}))", m0.iter().format(" "), m1.iter().format(" ")
                )
            }
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum Command {
    CheckSat,
    DeclareDatatype(Symbol, DatatypeDec),
    XDebug(String),
    Verbatim(String),
}
impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            // Self::Assert(m0) => write!(f, "(assert {})", m0),
            Self::CheckSat => write!(f, "(check-sat)"),
            // Self::CheckSatAssuming(m0) => {
            //     write!(f, "(check-sat-assuming ({}))", m0.iter().format(" "))
            // }
            // Self::DeclareConst(m0, m1) => write!(f, "(declare-const {} {})", m0, m1),
            Self::DeclareDatatype(m0, m1) => {
                write!(f, "(declare-datatype {} {})", m0, m1)
            }
            // Self::DeclareDatatypes(m0, m1) => {
            //     write!(
            //         f, "(declare-datatypes ({}) ({}))", m0.iter().format(" "), m1.iter()
            //         .format(" ")
            //     )
            // }
            // Self::DeclareFun(m0, m1, m2) => {
            //     write!(f, "(declare-fun {} ({}) {})", m0, m1.iter().format(" "), m2)
            // }
            // Self::DeclareSort(m0, m1) => write!(f, "(declare-sort {} {})", m0, m1),
            // Self::DefineFun(m0) => write!(f, "(define-fun {})", m0),
            // Self::DefineFunRec(m0) => write!(f, "(define-fun-rec {})", m0),
            // Self::DefineFunsRec(m0, m1) => {
            //     write!(
            //         f, "(define-funs-rec ({}) ({}))", m0.iter().format(" "), m1.iter()
            //         .format(" ")
            //     )
            // }
            // Self::DefineSort(m0, m1, m2) => {
            //     write!(f, "(define-sort {} ({}) {})", m0, m1.iter().format(" "), m2)
            // }
            // Self::Echo(m0) => write!(f, "(echo {})", m0),
            // Self::Exit => write!(f, "(exit)"),
            // Self::GetAssertions => write!(f, "(get-assertions)"),
            // Self::GetAssignment => write!(f, "(get-assignment)"),
            // Self::GetInfo(m0) => write!(f, "(get-info {})", m0),
            // Self::GetModel => write!(f, "(get-model)"),
            // Self::GetOption(m0) => write!(f, "(get-option {})", m0),
            // Self::GetProof => write!(f, "(get-proof)"),
            // Self::GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)"),
            // Self::GetUnsatCore => write!(f, "(get-unsat-core)"),
            // Self::GetValue(m0) => write!(f, "(get-value ({}))", m0.iter().format(" ")),
            // Self::Pop(m0) => write!(f, "(pop {})", m0),
            // Self::Push(m0) => write!(f, "(push {})", m0),
            // Self::Reset => write!(f, "(reset)"),
            // Self::ResetAssertions => write!(f, "(reset-assertions)"),
            // Self::SetInfo(m0) => write!(f, "(set-info {})", m0),
            // Self::SetLogic(m0) => write!(f, "(set-logic {})", m0),
            // Self::SetOption(m0) => write!(f, "(set-option {})", m0),
            // Self::Simplify(m0) => write!(f, "(simplify {})", m0),

            Self::XDebug(s) => write!(f, "(x-debug {})", s),
            Self::Verbatim(s) => write!(f, "{}", s),
        }
    }
}


// //////////////////////////// Command responses ///////////////////////


#[test]
fn parse_test() {
    use crate::api::Command::*;
    use crate::grammar::{parse, ParsingState};
    use crate::solver::Solver;

    let mut solver = Solver::default();
    let mut state = ParsingState::new(&mut solver);

    assert_eq!(parse("(check-sat) ", &mut state),
               Ok(vec![CheckSat]));
}
