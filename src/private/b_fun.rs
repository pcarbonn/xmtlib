// Copyright Pierre Carbonnelle, 2025.


use std::fmt::Display;

use indexmap::IndexSet;

use crate::api::{Sort, Symbol, Identifier, QualIdentifier, Term};
use crate::error::{SolverError, Offset};
use crate::solver::Solver;
use crate::private::a_sort::instantiate_parent_sort;
use crate::private::e1_ground_view::Ids;
use crate::private::z_option_map::L;


/////////////////////  Data structure for Function  ///////////////////////////


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FunctionObject {
    Predefined{boolean: Option<bool>},  // None for `ite` --> need special code
    Constructor,
    NotInterpreted{signature: (Vec<Sort>, Sort, bool)},  // signature used to create table, when later interpreted
    NonBooleanInterpreted{ table_g: Interpretation},
    BooleanInterpreted{table_tu: Interpretation, table_uf: Interpretation, table_g: Interpretation}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Interpretation {
    Table{name: String, ids: Ids, else_: Option<Option<L<Term>>>},  // None if complete, Some(None) if no `else` value, or Some(Some(value))
    Infinite  // for UF, G of interpreted predicate over infinite domain
}


/////////////////////  Implementation  ////////////////////////////////////////


impl Display for FunctionObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Predefined{boolean} =>
                if let Some(b) = boolean {
                    write!(f, "Predefined ({})", b)
                } else {
                    write!(f, "Predefined (?)")
                },
            Self::Constructor =>
                write!(f, "Constructor"),
            Self::NotInterpreted{signature} =>
                write!(f, "NotInterpreted({:?})", signature),
            Self::NonBooleanInterpreted{table_g} =>
                write!(f, "NonBooleanInterpreted ({table_g})"),
            Self::BooleanInterpreted{table_tu, table_uf, table_g} =>
                write!(f, "BooleanInterpreted ({table_tu}, {table_uf}, {table_g})"),
        }
    }
}


impl Display for Interpretation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Table{name, ids, else_} => {
                if let Some(Some(else_)) = else_ {
                    write!(f, "{name}?{else_} {ids}")
                } else if let Some(None) = else_ {
                    write!(f, "{name}?? {ids}")
                } else {
                    write!(f, "{name} {ids}")
                }
            },
            Self::Infinite {} =>
                write!(f, "(infinite)"),
        }
    }
}

pub(crate) fn declare_fun(
    symbol: Symbol,
    domain: Vec<Sort>,
    co_domain: Sort,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;  // this also validates the declaration

    // instantiate the sorts, if needed
    let declaring = IndexSet::new();
    for sort in &domain {
        instantiate_parent_sort(&sort, &declaring, solver)?;
    }
    instantiate_parent_sort(&co_domain, &declaring, solver)?;

    let identifier = QualIdentifier::Identifier(L(Identifier::Simple(symbol), Offset(0)));
    let boolean = match co_domain {
        Sort::Sort(L(Identifier::Simple(Symbol(ref s)), _)) => s=="Bool",
        _ => false
    };
    let function_is = FunctionObject::NotInterpreted{signature: (domain, co_domain, boolean)};
    solver.functions.insert(identifier, function_is);

    Ok(out)
}