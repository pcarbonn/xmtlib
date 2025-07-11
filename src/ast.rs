// Copyright Pierre Carbonnelle, 2025.

//! This module defines the abstract syntax tree (AST) of XMT-Lib.



// The nodes are listed in the order given in Appendix B of the SMT-Lib standard.

// It also implements Display to generate a string in XMT-Lib format.

#![allow(private_interfaces)]  // for public XSortedVar using private SortObject

use std::fmt::Display;
use std::hash::Hash;

use itertools::Itertools;
use itertools::Either::{self, Left, Right};

use crate::error::Offset;
use crate::solver::CanonicalSort;
use crate::private::a_sort::SortObject;


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
impl SpecConstant {
    pub(crate) fn to_canonical_sort(&self) -> CanonicalSort {
        match self {
            SpecConstant::Numeral(_) =>
                CanonicalSort(Sort::new(&Symbol("Int".to_string()))),
            SpecConstant::Decimal(_) =>
                CanonicalSort(Sort::new(&Symbol("Real".to_string()))),
            SpecConstant::Hexadecimal(_) =>
                CanonicalSort(Sort::new(&Symbol("Int".to_string()))),
            SpecConstant::Binary(_) =>
                CanonicalSort(Sort::new(&Symbol("Int".to_string()))),
            SpecConstant::String(_) =>
                CanonicalSort(Sort::new(&Symbol("String".to_string()))),
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SExpr {
    /// `<spec_constant>`
    SpecConstant(SpecConstant),
    /// `<symbol>`
    Symbol(Symbol),
    // /// `<reserved>`
    // Reserved(Reserved),
    /// `<keyword>`
    Keyword(Keyword),
    /// `(<s_expr>*)`
    Paren(Vec<SExpr>),
}
impl Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::SpecConstant(m0) => write!(f, "{}", m0),
            Self::Symbol(m0) => write!(f, "{}", m0),
            // Self::Reserved(m0) => write!(f, "{}", m0),
            Self::Keyword(m0) => write!(f, "{}", m0),
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

impl Identifier {
    #[inline]
    pub(crate) fn new(symbol: &Symbol) -> L<Identifier> {
        L(Identifier::Simple(symbol.clone()), Offset(0))
    }
}


// //////////////////////////// Sorts        ////////////////////////////


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// `<identifier>`
    Sort(L<Identifier>),
    /// `(<identifier> <sort>+)`
    Parametric(L<Identifier>, Vec<Sort>),
}
impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Sort(m0) => write!(f, "{}", m0),
            Self::Parametric(m0, m1) => write!(f, "({} {})", m0, m1.iter().format(" ")),
        }
    }
}
impl Sort {
    #[inline]
    pub(crate) fn new(symbol: &Symbol) -> Sort {
        Sort::Sort(Identifier::new(symbol))
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
    Identifier(L<Identifier>),
    /// `(as <identifier> <sort>)`
    Sorted(L<Identifier>, Sort),
}
impl Display for QualIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Identifier(m0) => write!(f, "{}", m0),
            Self::Sorted(m0, m1) => write!(f, " (as {} {})", m0, m1),  // must be a constructor  TODO SMT 2.7
        }
    }
}
impl QualIdentifier {
    #[inline]
    pub(crate) fn new(symbol: &Symbol, sort: Option<Sort>) -> QualIdentifier {
        let id = Identifier::new(symbol);
        if let Some(sort) = sort {
            QualIdentifier::Sorted(id, sort)
        } else {
            QualIdentifier::Identifier(id)
        }
    }
}

/// `(<symbol> <term>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarBinding(pub Symbol, pub L<Term>);
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
pub struct MatchCase(pub Pattern, pub L<Term>);
impl std::fmt::Display for MatchCase {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// `<spec_constant>`
    SpecConstant(SpecConstant),  // offset is start position
    /// `<qual_identifier>`
    Identifier(QualIdentifier),
    /// `(<qual_identifier> <term>+)`
    Application(QualIdentifier, Vec<L<Term>>),
    /// `(let (<var_binding>+) <term>)`
    Let(Vec<VarBinding>, Box<L<Term>>),
    /// `(forall (<sorted_var>+) <term>)`
    Forall(Vec<SortedVar>, Box<L<Term>>),
    /// `(exists (<sorted_var>+) <term>)`
    Exists(Vec<SortedVar>, Box<L<Term>>),
    /// `(match <term> (<match_case>+))`
    Match(Box<L<Term>>, Vec<MatchCase>),
    /// `(! <term> <attribute>+)`
    Annotation(Box<L<Term>>, Vec<Attribute>),
    XSortedVar(Symbol, Sort, SortObject),
    XLetVar(Symbol, Box<L<Term>>),
}
impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::SpecConstant(m0) => write!(f, "{}", m0),
            Self::Identifier(m0) => write!(f, "{}", m0),
            Self::Application(m0, m1) => write!(f, "({} {})", m0, m1.iter().format(" ")),
            Self::Let(m0, m1) => write!(f, "(let ({}) {})", m0.iter().format(" "), m1),
            Self::Forall(m0, m1) => {
                write!(f, "(forall ({}) {})", m0.iter().format(" "), m1)
            }
            Self::Exists(m0, m1) => {
                write!(f, "(exists ({}) {})", m0.iter().format(" "), m1)
            }
            Self::Match(m0, m1) => {
                write!(f, "(match {} ({}))", m0, m1.iter().format(" "))
            }
            Self::Annotation(m0, m1) => write!(f, "(! {} {})", m0, m1.iter().format(" ")),
            Self::XSortedVar(symbol, _, _) => write!(f, "{symbol}", ),
            Self::XLetVar(symbol, _) => write!(f, "{symbol}", )
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct XTuple(pub Vec<L<Term>>);
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
        if self.1.len() == 0 {
            write!(f, "({})", self.0)
        } else {
            write!(f, "({} {})", self.0, self.1.iter().format(" "))
        }
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


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionDef {
    /// `<symbol> (` <sorted_var> * ) <sort> <term>
    pub symbol: Symbol,
    pub sorted_vars: Vec<SortedVar>,
    pub co_domain: Sort,
    pub term: L<Term>
}
impl Display for FunctionDef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let FunctionDef{symbol, sorted_vars, co_domain, term} = self;
        write!(f, "{symbol} ({}) {co_domain} {term}", sorted_vars.iter().format(" "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionDec {
    /// `<symbol> (` <sorted_var> * ) <sort> <term>
    pub symbol: Symbol,
    pub sorted_vars: Vec<SortedVar>,
    pub co_domain: Sort
}
impl Display for FunctionDec{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let FunctionDec{symbol, sorted_vars, co_domain} = self;
        write!(f, "({symbol} ({}) {co_domain})", sorted_vars.iter().format(" "))
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum XSet {
    XSet(Vec<XTuple>),
    XRange(Vec<L<Term>>),
    XSql(String_)
}
impl std::fmt::Display for XSet {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            XSet::XSet(els) => write!(f, "(x-set {})", els.iter().format(" ")),
            XSet::XRange(els) => write!(f, "(x-range {})", els.iter().format(" ")),
            XSet::XSql(sql) => write!(f, "(x-sql {sql})"),  // with quotes around sql
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum Command {
    Assert(L<Term>),
    CheckSat,
    DeclareConst(Symbol, Sort),
    DeclareDatatype(Symbol, DatatypeDec),
    DeclareDatatypes(Vec<SortDec>, Vec<DatatypeDec>),
    DeclareFun(Symbol, Vec<Sort>, Sort),
    DeclareSort(Symbol, Numeral),
    DefineFun(FunctionDef, bool),  // true for recursive
    DefineFunsRec(Vec<FunctionDec>, Vec<L<Term>>),
    DefineSort(Symbol, Vec<Symbol>, Sort),
    Echo(String_),
    GetInfo(Keyword),
    SetOption(Option_),
    XDebug(L<Identifier>, L<Identifier>),
    XDuration(String_),
    XGround{no: bool, debug: bool, sql: bool},
    XInterpretPred(L<Identifier>, XSet),
    XInterpretFun(L<Identifier>, Either<Vec<(XTuple, L<Term>)>, String_>, Option<L<Term>>),
    Verbatim(String),
}
impl Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Assert(m0) => write!(f, "(assert {m0})\n"),
            Self::CheckSat => write!(f, "(check-sat)\n"),
            // Self::CheckSatAssuming(m0) => {
            //     write!(f, "(check-sat-assuming ({}))\n", m0.iter().format(" "))
            // }
            Self::DeclareConst(m0, m1) => write!(f, "(declare-const {m0} {m1})\n"),
            Self::DeclareDatatype(m0, m1) => {
                write!(f, "(declare-datatype {m0} {m1})\n")
            }
            Self::DeclareDatatypes(m0, m1) => {
                let sorts = m0.iter().format(" ");
                let dec = m1.iter()
                .format(" ");
                write!(f, "(declare-datatypes ({sorts}) ({dec}))\n")
            }
            Self::DeclareFun(m0, m1, m2) => {
                let sorts = m1.iter().format(" ");
                write!(f, "(declare-fun {m0} ({sorts}) {m2})\n")
            }
            Self::DeclareSort(m0, m1) => write!(f, "(declare-sort {m0} {m1})\n"),
            Self::DefineFun(m0, recursive) =>
                if *recursive {
                    write!(f, "(define-fun-rec {})\n", m0)
                } else {
                    write!(f, "(define-fun {})\n", m0)
                },
            Self::DefineFunsRec(m0, m1) => {
                write!(
                    f, "(define-funs-rec ({}) ({}))\n", m0.iter().format(" "), m1.iter()
                    .format(" ")
                )
            }
            Self::DefineSort(m0, m1, m2) => {
                let variables = m1.iter().format(" ");
                write!(f, "(define-sort {m0} ({variables}) {m2})\n")
            }
            Self::Echo(m0) => write!(f, "(echo {m0})\n"),
            // Self::Exit => write!(f, "(exit)\n"),
            // Self::GetAssertions => write!(f, "(get-assertions)\n"),
            // Self::GetAssignment => write!(f, "(get-assignment)\n"),
            Self::GetInfo(m0) => write!(f, "(get-info {})\n", m0),
            // Self::GetModel => write!(f, "(get-model)\n"),
            // Self::GetOption(m0) => write!(f, "(get-option {})\n", m0),
            // Self::GetProof => write!(f, "(get-proof)\n"),
            // Self::GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)\n"),
            // Self::GetUnsatCore => write!(f, "(get-unsat-core)\n"),
            // Self::GetValue(m0) => write!(f, "(get-value ({}))\n", m0.iter().format(" ")),
            // Self::Pop(m0) => write!(f, "(pop {})\n", m0),
            // Self::Push(m0) => write!(f, "(push {})\n", m0),
            // Self::Reset => write!(f, "(reset)\n"),
            // Self::ResetAssertions => write!(f, "(reset-assertions)\n"),
            // Self::SetInfo(m0) => write!(f, "(set-info {})\n", m0),
            // Self::SetLogic(m0) => write!(f, "(set-logic {})\n", m0),
            Self::SetOption(m0) => write!(f, "(set-option {})", m0),
            // Self::Simplify(m0) => write!(f, "(simplify {})\n", m0),

            Self::XDebug(s1, s2) => write!(f, "(x-debug {s1} {s2})\n"),
            Self::XDuration(m0) => write!(f, "(x-duration {m0})\n"),
            Self::XGround{no, debug, sql}=>
                write!(f, "(x-ground{}{}{})\n",
                            if *no {" :no"} else {""},
                            if *debug {" :debug"} else {""},
                            if *sql {" :sql"} else {""}
                        ),
            Self::XInterpretPred(s1, s2 ) => write!(f, "(x-interpret-pred {s1} {s2})\n"),
            Self::XInterpretFun(s1, s2, s3 ) => {
                let else_ =
                    if let Some(else_) = s3 {
                        else_.to_string()
                    } else {
                        "".to_string()
                    };
                match s2 {
                    Left(tuples) => {
                        let tuples = tuples.iter()
                            .map(|(args, value)| format!("({args} {value})"))
                            .collect::<Vec<_>>().join(" ");
                        write!(f, "(x-interpret-fun {s1} (x-mapping {tuples} ) {else_})\n")
                    },
                    Right(s) =>
                        write!(f, "(x-interpret-fun {s1} (x-sql {s} ) {else_})\n")
                }
            },
            Self::Verbatim(s) => write!(f, "{s}\n"),
        }
    }
}


// //////////////////////////// Command responses ///////////////////////


#[test]
fn parse_test() {
    use crate::ast::Command::*;
    use crate::grammar::parse;

    assert_eq!(parse("(check-sat) "),
               Ok(vec![CheckSat]));
}


//////////////////////////    L          //////////////////////////////////////


#[derive(Debug, Clone)]
pub struct L<T: Display+ Hash + Eq>(pub T, pub Offset);

impl<T: Display+ Hash + Eq> Display for L<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<T: Display+ Hash + Eq> PartialEq for L<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<T: Display+ Hash + Eq> Eq for L<T> {}
impl<T: Display+ Hash + Eq> Hash for L<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T: Display+ Hash + Eq> L<T> {
    pub(crate) fn start(&self) -> Offset {
        self.1
    }
}