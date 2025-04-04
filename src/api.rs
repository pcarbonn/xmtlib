// Copyright Pierre Carbonnelle, 2025.

//! This module defines the abstract syntax tree (AST) of XMT-Lib.
//!
//! The nodes are listed in the order given in Appendix B of the SMT-Lib standard.

// It also implements Display to generate a string in XMT-Lib format.

use std::fmt::Display;

use itertools::Itertools;

use crate::error::Offset;

// //////////////////////////// Other tokens ////////////////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Numeral(pub i32);
impl Display for Numeral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
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


#[derive(Debug, Clone)]
pub enum Identifier {
    /// `<symbol>`
    Simple(Symbol, Offset),
    /// `(_ <symbol> <index>+)`
    Indexed(Symbol, Vec<Index>, Offset),
}
impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Simple(m0, _) => write!(f, "{}", m0),
            Self::Indexed(m0, m1, _) => write!(f, "(_ {} {})", m0, m1.iter().format(" ")),
        }
    }
}
impl PartialEq for Identifier {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Simple(l0, _), Self::Simple(r0, _)) => l0 == r0,
            (Self::Indexed(l0, l1, _), Self::Indexed(r0, r1, _)) => l0 == r0 && l1 == r1,
            _ => false,
        }
    }
}
impl Eq for Identifier {}
impl std::hash::Hash for Identifier {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Simple(symbol, _) => symbol.hash(state),
            Self::Indexed(symbol, indices, _) => {
                symbol.hash(state);
                indices.hash(state);
            }
        }
    }
}
impl Identifier {
    pub(crate) fn start(&self) -> Offset {
        match self {
            Self::Simple(_, start)
            | Self::Indexed(_, _, start) => *start,
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


#[derive(Debug, Clone)]
pub enum Term {
    /// `<spec_constant>`
    SpecConstant(SpecConstant, Offset),  // offset is start position
    /// `<qual_identifier>`
    Identifier(QualIdentifier, Offset),
    /// `(<qual_identifier> <term>+)`
    Application(QualIdentifier, Vec<Term>, Offset),
    /// `(let (<var_binding>+) <term>)`
    Let(Vec<VarBinding>, Box<Term>, Offset),
    /// `(forall (<sorted_var>+) <term>)`
    Forall(Vec<SortedVar>, Box<Term>, Offset),
    /// `(exists (<sorted_var>+) <term>)`
    Exists(Vec<SortedVar>, Box<Term>, Offset),
    /// `(match <term> (<match_case>+))`
    Match(Box<Term>, Vec<MatchCase>, Offset),
    /// `(! <term> <attribute>+)`
    Annotation(Box<Term>, Vec<Attribute>, Offset),
    XSortedVar(Symbol, Option<Sort>, Offset),  // sort is None if the variable has no interpretation
}
impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::SpecConstant(m0, _) => write!(f, "{}", m0),
            Self::Identifier(m0, _) => write!(f, "{}", m0),
            Self::Application(m0, m1, _) => write!(f, "({} {})", m0, m1.iter().format(" ")),
            Self::Let(m0, m1, _) => write!(f, "(let ({}) {})", m0.iter().format(" "), m1),
            Self::Forall(m0, m1, _) => {
                write!(f, "(forall ({}) {})", m0.iter().format(" "), m1)
            }
            Self::Exists(m0, m1, _) => {
                write!(f, "(exists ({}) {})", m0.iter().format(" "), m1)
            }
            Self::Match(m0, m1, _) => {
                write!(f, "(match {} ({}))", m0, m1.iter().format(" "))
            }
            Self::Annotation(m0, m1, _) => write!(f, "(! {} {})", m0, m1.iter().format(" ")),
            Self::XSortedVar(symbol, _, _) => write!(f, "{symbol}", )
        }
    }
}
impl Term {
    pub(crate) fn start(&self) -> Offset {
        match self {
            Self::SpecConstant(_, start)
            | Self::Identifier(_, start)
            | Self::Application(_, _, start)
            | Self::Let(_, _, start)
            | Self::Forall(_, _, start)
            | Self::Exists(_, _, start)
            | Self::Match(_, _, start)
            | Self::Annotation(_, _, start)
            | Self::XSortedVar(_, _, start) => *start
        }
    }
}
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::SpecConstant(l0, _), Self::SpecConstant(r0, _)) => l0 == r0,
            (Self::Identifier(l0, _), Self::Identifier(r0, _)) => l0 == r0,
            (Self::Application(l0, l1, _), Self::Application(r0, r1, _)) => l0 == r0 && l1 == r1,
            (Self::Let(l0, l1, _), Self::Let(r0, r1, _)) => l0 == r0 && l1 == r1,
            (Self::Forall(l0, l1, _), Self::Forall(r0, r1, _)) => l0 == r0 && l1 == r1,
            (Self::Exists(l0, l1, _), Self::Exists(r0, r1, _)) => l0 == r0 && l1 == r1,
            (Self::Match(l0, l1, _), Self::Match(r0, r1, _)) => l0 == r0 && l1 == r1 ,
            (Self::Annotation(l0, l1, _), Self::Annotation(r0, r1, _)) => l0 == r0 && l1 == r1,
            (Self::XSortedVar(l0, l1, _), Self::XSortedVar(r0, r1, _)) => l0 == r0 && l1 == r1,
            _ => false,
        }
    }
}
impl Eq for Term {}
impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::SpecConstant(m0, _) => m0.hash(state),
            Self::Identifier(m0, _) => m0.hash(state),
            Self::Application(m0, m1, _) => {
                m0.hash(state);
                m1.hash(state);
            }
            Self::Let(m0, m1, _) => {
                m0.hash(state);
                m1.hash(state);
            }
            Self::Forall(m0, m1, _) => {
                m0.hash(state);
                m1.hash(state);
            }
            Self::Exists(m0, m1, _) => {
                m0.hash(state);
                m1.hash(state);
            }
            Self::Match(m0, m1, _) => {
                m0.hash(state);
                m1.hash(state);
            }
            Self::Annotation(m0, m1, _) => {
                m0.hash(state);
                m1.hash(state);
            }
            Self::XSortedVar(symbol, sort, _) => {
                symbol.hash(state);
                sort.hash(state);
            }
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


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Option_ {
    /// `<attribute>`
    Attribute(Attribute),
}
impl std::fmt::Display for Option_ {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Attribute(m0) => write!(f, "{}", m0),
        }
    }
}


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
    SetOption(Option_),
    XDebug(Identifier, Identifier),
    XGround,
    XInterpretPred(Identifier, Vec<XTuple>),
    XInterpretFun(Identifier, Vec<(XTuple, Term)>, Option<Term>),
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
            Self::SetOption(m0) => write!(f, "(set-option {})", m0),
            // Self::Simplify(m0) => write!(f, "(simplify {})", m0),

            Self::XInterpretPred(s1, s2 ) => write!(f, "(x-interpret-pred {s1} {})", s2.iter().format(" ")),
            Self::XInterpretFun(s1, s2, s3 ) => {
                let tuples = s2.iter()
                    .map(|(args, value)| format!("({args} {value})"))
                    .collect::<Vec<_>>().join(" ");
                let else_ = if let Some(else_) = s3 { else_.to_string() }
                    else { "".to_string() };
                write!(f, "(x-interpret-fun {s1} ( {tuples} ) {else_})")
            },
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
