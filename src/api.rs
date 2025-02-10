// Copyright Pierre Carbonnelle, 2025.

//! This module defines the abstract syntax tree (AST) of XMT-Lib.
//!
//! The nodes are listed in the order given in Appendix B of the SMT-Lib standard.

// It also implements Display to generate a string in XMT-Lib format.

use std::fmt::Display;

use itertools::Itertools;


// //////////////////////////// Other tokens ////////////////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Numeral(pub i32);
impl Display for Numeral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 < 0 {
            write!(f, "(- {})", -self.0)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Decimal(pub String);
impl std::fmt::Display for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Hexadecimal(pub String);
impl std::fmt::Display for Hexadecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binary(pub String);
impl std::fmt::Display for Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct String_(pub String);
impl std::fmt::Display for String_ {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);
impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Keyword(pub String);  // with `:` prefix
impl std::fmt::Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}


// //////////////////////////// S-expressions ///////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]

pub enum SpecConstant {
    /// `<numeral>`
    Numeral(Numeral),
    /// `<decimal>`
    Decimal(Decimal),
    /// `<hexadecimal>`
    Hexadecimal(Hexadecimal),
    /// `<binary>`
    Binary(Binary),
    /// `<string>`
    String(String_),  // with duplicate `"`
}
impl std::fmt::Display for SpecConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Numeral(m0) => write!(f, "{}", m0),
            Self::Decimal(m0) => write!(f, "{}", m0),
            Self::Hexadecimal(m0) => write!(f, "{}", m0),
            Self::Binary(m0) => write!(f, "{}", m0),
            Self::String(m0) => write!(f, "{}", m0),
        }
    }
}

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
impl Display for SExpr {
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
impl Display for Index {
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
impl Display for Identifier {
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
impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Sort(m0) => write!(f, "{}", m0),
            Self::Parametric(m0, m1) => write!(f, "({} {})", m0, m1.iter().format(" ")),
        }
    }
}


// //////////////////////////// Attributes   ////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AttributeValue {
    /// `<spec_constant>`
    SpecConstant(SpecConstant),
    /// `<symbol>`
    Symbol(Symbol),
    /// `(<s_expr>)`
    Expr(SExpr),
}
impl std::fmt::Display for AttributeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::SpecConstant(m0) => write!(f, "{}", m0),
            Self::Symbol(m0) => write!(f, "{}", m0),
            Self::Expr(m0) => write!(f, "({})", m0),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Attribute {
    /// `<keyword>`
    Keyword(Keyword),
    /// `<keyword> <attribute_value>`
    WithValue(Keyword, AttributeValue),
}
impl std::fmt::Display for Attribute {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Keyword(m0) => write!(f, "{}", m0),
            Self::WithValue(m0, m1) => write!(f, "{} {}", m0, m1),
        }
    }
}

// //////////////////////////// Terms        ////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QualIdentifier {
    /// `<identifier>`
    Identifier(Identifier),
    /// `(as <identifier> <sort>)`
    Sorted(Identifier, Sort),
}
impl Display for QualIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Identifier(m0) => write!(f, "{}", m0),
            Self::Sorted(m0, m1) => write!(f, "(as {} {})", m0, m1),
        }
    }
}

/// `(<symbol> <term>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarBinding(pub Symbol, pub Term);
impl std::fmt::Display for VarBinding {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

/// `(<symbol> <sort>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortedVar(pub Symbol, pub Sort);
impl std::fmt::Display for SortedVar {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    /// `<symbol>`
    Symbol(Symbol),
    /// `(<symbol> <symbol>+)`
    Application(Symbol, Vec<Symbol>),
}
impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Symbol(m0) => write!(f, "{}", m0),
            Self::Application(m0, m1) => write!(f, "({} {})", m0, m1.iter().format(" ")),
        }
    }
}


/// `(<pattern> <term>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchCase(pub Pattern, pub Term);
impl std::fmt::Display for MatchCase {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// `<spec_constant>`
    SpecConstant(SpecConstant),
    /// `<qual_identifier>`
    Identifier(QualIdentifier),
    /// `(<qual_identifier> <term>+)`
    Application(QualIdentifier, Vec<Term>),
    /// `(let (<var_binding>+) <term>)`
    Let(Vec<VarBinding>, Box<Term>),
    /// `(forall (<sorted_var>+) <term>)`
    Forall(Vec<SortedVar>, Box<Term>, Option<Vec<SortedVar>>),  // the 3rd argument is the list of grounded variables
    /// `(exists (<sorted_var>+) <term>)`
    Exists(Vec<SortedVar>, Box<Term>, Option<Vec<SortedVar>>),
    /// `(match <term> (<match_case>+))`
    Match(Box<Term>, Vec<MatchCase>),
    /// `(! <term> <attribute>+)`
    Annotation(Box<Term>, Vec<Attribute>),
    XSortedVar(Symbol, Option<Sort>),  // sort is None if the variable has no interpretation
}
impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::SpecConstant(m0) => write!(f, "{}", m0),
            Self::Identifier(m0) => write!(f, "{}", m0),
            Self::Application(m0, m1) => write!(f, "({} {})", m0, m1.iter().format(" ")),
            Self::Let(m0, m1) => write!(f, "(let ({}) {})", m0.iter().format(" "), m1),
            Self::Forall(m0, m1, _) => {
                write!(f, "(forall ({}) {})", m0.iter().format(" "), m1)
            }
            Self::Exists(m0, m1, _) => {
                write!(f, "(exists ({}) {})", m0.iter().format(" "), m1)
            }
            Self::Match(m0, m1) => {
                write!(f, "(match {} ({}))", m0, m1.iter().format(" "))
            }
            Self::Annotation(m0, m1) => write!(f, "(! {} {})", m0, m1.iter().format(" ")),
            Self::XSortedVar(symbol, _) => write!(f, "{symbol}", )
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct XTuple(pub Vec<Term>);
impl std::fmt::Display for XTuple {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({})", self.0.iter().format(" "))
    }
}

// //////////////////////////// Theories     ////////////////////////////
// //////////////////////////// Logics       ////////////////////////////
// //////////////////////////// Info flags   ////////////////////////////
// //////////////////////////// Command Options /////////////////////////
// //////////////////////////// Commands     ////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortDec(pub Symbol, pub Numeral);
impl Display for SortDec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

/// `(<symbol> <sort>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SelectorDec(pub Symbol, pub Sort);
impl Display for SelectorDec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}


/// `(<symbol> <selector_dec>*)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorDec(pub Symbol, pub Vec<SelectorDec>);
impl Display for ConstructorDec {
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
impl Display for DatatypeDec {
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
    Assert(Term),
    CheckSat,
    DeclareConst(Symbol, Sort),
    DeclareDatatype(Symbol, DatatypeDec),
    DeclareDatatypes(Vec<SortDec>, Vec<DatatypeDec>),
    DeclareFun(Symbol, Vec<Sort>, Sort),
    DeclareSort(Symbol, Numeral),
    DefineSort(Symbol, Vec<Symbol>, Sort),
    XDebug(String, String),
    XGround,
    XInterpretPred(Symbol, Vec<XTuple>),
    Verbatim(String),
}
impl Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Assert(m0) => write!(f, "(assert {m0})"),
            Self::CheckSat => write!(f, "(check-sat)"),
            // Self::CheckSatAssuming(m0) => {
            //     write!(f, "(check-sat-assuming ({}))", m0.iter().format(" "))
            // }
            Self::DeclareConst(m0, m1) => write!(f, "(declare-const {m0} {m1})"),
            Self::DeclareDatatype(m0, m1) => {
                write!(f, "(declare-datatype {m0} {m1})")
            }
            Self::DeclareDatatypes(m0, m1) => {
                let sorts = m0.iter().format(" ");
                let dec = m1.iter()
                .format(" ");
                write!(f, "(declare-datatypes ({sorts}) ({dec}))")
            }
            Self::DeclareFun(m0, m1, m2) => {
                let sorts = m1.iter().format(" ");
                write!(f, "(declare-fun {m0} ({sorts}) {m2})")
            }
            Self::DeclareSort(m0, m1) => write!(f, "(declare-sort {m0} {m1})"),
            // Self::DefineFun(m0) => write!(f, "(define-fun {})", m0),
            // Self::DefineFunRec(m0) => write!(f, "(define-fun-rec {})", m0),
            // Self::DefineFunsRec(m0, m1) => {
            //     write!(
            //         f, "(define-funs-rec ({}) ({}))", m0.iter().format(" "), m1.iter()
            //         .format(" ")
            //     )
            // }
            Self::DefineSort(m0, m1, m2) => {
                let variables = m1.iter().format(" ");
                write!(f, "(define-sort {m0} ({variables}) {m2})")
            }
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

            Self::XInterpretPred(s1, s2 ) => write!(f, "(x-interpreted-pred {s1} {})", s2.iter().format(" ")),
            Self::XDebug(s1, s2) => write!(f, "(x-debug {s1} {s2})"),
            Self::XGround => write!(f, "(x-ground)"),
            Self::Verbatim(s) => write!(f, "{s}"),
        }
    }
}


// //////////////////////////// Command responses ///////////////////////


#[test]
fn parse_test() {
    use crate::api::Command::*;
    use crate::grammar::parse;

    assert_eq!(parse("(check-sat) "),
               Ok(vec![CheckSat]));
}
