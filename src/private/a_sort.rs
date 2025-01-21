// Copyright Pierre Carbonnelle, 2025.

use either::Either::{self, Left, Right};
use indexmap::{IndexMap, IndexSet};

use crate::api::{ConstructorDec, DatatypeDec, Identifier, SelectorDec, Sort, Symbol};
use crate::{error::SolverError, solver::Solver};

#[allow(unused_imports)]
use debug_print::debug_println as dprintln;


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SortTable {
    Table(String),
    Infinite,
    Recursive,
    Unknown
}


/// Resolve variables and identifiers, and adds the declaration to the solver, if correct.
/// Also adds any required instantiation of a parametric sort.
/// This function is not recursive.
pub(crate) fn annotate_sort_decl(
    symb: &Symbol,
    decl: &DatatypeDec,
    declaring: &IndexSet<Symbol>,  // to detect recursive datatypes
    solver: &mut Solver
) -> Result<(), SolverError> {

    match decl {
        DatatypeDec::DatatypeDec(constructor_decls) => {
            let vars = IndexSet::new();
            annotate_constructor_decls(&constructor_decls, &vars, declaring, solver)?;

            let key = Sort::Sort(Identifier::Simple(symb.clone()));
            if ! solver.sorts.contains_key(&key) {
                insert_sort(key, Some(decl.clone()), declaring, solver)?;
            } else {
                return Err(SolverError::ExprError("duplicate sort".to_string(), None))
            }
        },
        DatatypeDec::Par(vars, constructor_decls) => {
            let vars = vars.iter().cloned().collect();
            annotate_constructor_decls(&constructor_decls, &vars, declaring, solver)?;

            if ! solver.parametric_datatypes.contains_key(symb) {
                solver.parametric_datatypes.insert(symb.clone(), decl.clone());
            } else {
                return Err(SolverError::ExprError("duplicate parametric sort".to_string(), None))
            }
        }
    };
    Ok(())
}


/// Annotates each sort occurring in the constructor declaration.
/// This function is not recursive
fn annotate_constructor_decls(
    constructor_decls: &Vec<ConstructorDec>,
    vars: &IndexSet<Symbol>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver
) -> Result<(), SolverError> {
    for constructor_decl in constructor_decls {
        let ConstructorDec(_, selectors) = constructor_decl;
        for SelectorDec(_, sort) in selectors {
            annotate_parametered_sort(&sort, &vars, declaring, solver)?;
        }
    }
    Ok(())
}

/// Annotate a parametered sort in a sort declaration.
/// The non-parametric sorts occurring in this sort declaration must be either variables listed in vars, or known by the solver.
/// When vars is empty, the parametric sorts occurring in this sort declaration are instantiated and added to the solver.
/// This function is recursive.
pub(crate) fn annotate_parametered_sort(
    parametered_sort: &Sort,
    vars: &IndexSet<Symbol>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<(), SolverError> {

    match parametered_sort {
        Sort::Sort(ref id) => {
            if ! solver.sorts.contains_key(parametered_sort) {
                if let Identifier::Simple(symb) = id {
                    if ! vars.contains(symb) && ! declaring.contains(symb) {
                        return Err(SolverError::ExprError("Unknown sort".to_string(), None))
                    }
                } else {
                    return Err(SolverError::ExprError("Unexpected indexed identifier".to_string(), None))
                }
            }
        },
        Sort::Parametric(id, parameters) => {
            for sort in parameters {  // check the non-parametric sorts
                annotate_parametered_sort(&sort, &vars, declaring, solver)?;  // recursive
            }

            if vars.len() == 0 {
                // instantiate the parametric sort
                if let Identifier::Simple(name) = id {
                    let parametric_decl = solver.parametric_datatypes.get(name)
                        .ok_or(SolverError::ExprError("Unknown parametric sort".to_string(), None))?;

                    match parametric_decl.clone() {
                        DatatypeDec::Par(variables, constructors) => {
                            if variables.len() == parameters.len() {

                                // build substitution map : Sort -> Sort
                                let old_variables: Vec<Sort> = variables.iter()
                                    .map(|s| { Sort::Sort(Identifier::Simple(s.clone()))})
                                    .collect();
                                let subs: IndexMap<Sort, Sort> = old_variables.into_iter()
                                    .zip(parameters.iter().cloned())
                                    .collect();

                                // instantiate constructors
                                let new_constructors = constructors.into_iter()
                                    .map(|c| substitute_in_constructor(c, &subs, vars, declaring, solver))
                                    .collect::<Result<Vec<_>, _>>()?;

                                // add the declaration to the solver
                                let new_decl = DatatypeDec::DatatypeDec(new_constructors);
                                insert_sort(parametered_sort.clone(), Some(new_decl), declaring, solver)?;

                                return Ok(())
                            } else {
                                return Err(SolverError::ExprError("Incorrect number of parameters".to_string(), None))
                            }
                        },
                        DatatypeDec::DatatypeDec(_) =>
                            return Err(SolverError::ExprError("Not a parametric type".to_string(), None))
                    }
                } else {  // indexed identifier
                    panic!("dead code oe;cpzk")
                }
            }
        }
    }
    Ok(())
}


fn substitute_in_constructor(
    constructor: ConstructorDec,
    subs: &IndexMap<Sort, Sort>,
    vars: &IndexSet<Symbol>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<ConstructorDec, SolverError> {

    // instantiate the selector declarations
    let new_selector_decs = constructor.1.iter()
        .map(|s| { substitute_in_selector(s, subs, vars, declaring, solver) })
        .collect::<Result<Vec<_>,_>>()?;

    Ok(ConstructorDec(constructor.0.clone(), new_selector_decs))
}


fn substitute_in_selector(
    selector: &SelectorDec,
    subs: &IndexMap<Sort, Sort>,
    vars: &IndexSet<Symbol>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<SelectorDec, SolverError> {

    let new_sort = substitute_in_sort(&selector.1, subs, vars, declaring, solver)?;
    return Ok(SelectorDec(selector.0.clone(), new_sort))

}


fn substitute_in_sort(
    sort: &Sort,
    subs: &IndexMap<Sort, Sort>,
    vars: &IndexSet<Symbol>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<Sort, SolverError> {

    match sort {

        Sort::Sort(_) => {
            // substitute if in the map
            if let Some(new_sort) = subs.get(sort) {
                return Ok(new_sort.clone())
            } else {
                return Ok(sort.clone())
            }
        },

        Sort::Parametric(name, sorts) => {
            let new_sorts = sorts.iter()
                .map(|s| { substitute_in_sort(s, subs, vars, declaring, solver) })
                .collect::<Result<Vec<_>, _>>()?;
            let new_sort = Sort::Parametric(name.clone(), new_sorts);
            annotate_parametered_sort(&new_sort, vars, declaring, solver)?;
            Ok(new_sort)
        }
    }
}


/// Make the sort known to the solver, and create its table
fn insert_sort(
    sort: Sort,
    decl: Option<DatatypeDec>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<(), SolverError> {

    // update solver.sort_tables
    if ! solver.sorts.contains_key(&sort) { // a new sort
        // update solver.sorts
        let i = solver.sorts.len();

        match decl {
            None => {
                todo!();  // for declare-sort ?
                //solver.sort_tables.push(SortTable::Unknwon)
            },
            Some(ref decl) => {
                let selectors = collect_selectors(decl, declaring, solver);
                match selectors {
                    Left(_selectors) => {
                        solver.sort_tables.push(SortTable::Table(format!("Sort_{}", i)));
                    },
                    Right(table) => {
                        solver.sort_tables.push(table);
                    }
                }

            },
        }
        solver.sorts.insert_full(sort, decl);
    }

    Ok(())
}


/// Collects all the selectors in the (non-parametric) datatype declaration.
/// Returns None if a selector has a sort without a table,
/// or if a sort is being declared recursively  (or if an error occurs)
fn collect_selectors(
    decl: &DatatypeDec,
    declaring: &IndexSet<Symbol>,
    solver: &Solver,
) -> Either<IndexSet<String>, SortTable> {
    match decl {
        DatatypeDec::DatatypeDec(constructor_decls) => {
            let mut result = IndexSet::new();
            for constructor_decl in constructor_decls {
                let ConstructorDec(_, selectors) = constructor_decl;
                for SelectorDec(selector, sort) in selectors {
                    // get the symbol of the sort
                    let symbol =
                        match sort {
                            Sort::Sort(Identifier::Simple(symbol)) => symbol,
                            Sort::Parametric(Identifier::Simple(symbol), _) => symbol,
                            Sort::Sort(Identifier::Indexed(_, _ ))
                            | Sort::Parametric(Identifier::Indexed(_, _ ), _) => {
                                return Right(SortTable::Unknown)
                            }
                        };
                    // check if the sort is being declared recursively
                    if declaring.contains(symbol) {
                        return Right(SortTable::Recursive)
                    }
                    // check if the sort has a table
                    if let Some(i) = solver.sorts.get_index_of(sort) {
                        let sort_table = solver.sort_tables.get(i).unwrap();
                        match sort_table {
                            SortTable::Table(_) => {result.insert(selector.0.clone());},
                            SortTable::Infinite
                            | SortTable::Recursive
                            | SortTable::Unknown => return Right(sort_table.clone()),
                        }
                    } else {
                        panic!("dead code pcyevpg")  // indexed sort
                    }
                }
            }
            Left(result)
        },
        DatatypeDec::Par(_, _) => panic!("dead code ddjoghx")
    }
}