// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;

use crate::{api::{ConstructorDec, DatatypeDec, Identifier, SelectorDec, Sort, Symbol}, solver::Solver};

#[allow(unused_imports)]
use debug_print::{debug_println as dprintln};

/// parametric sort: adds the instantiation of the declaration of a parametric sort to the solver.
/// non-parametric: ensures that it is in the solver
/// returns the input sort or error
pub(crate) fn create_sort(
    sort: &Sort,
    solver: &mut Solver,
) -> Result<Sort, &'static str> {

    // do nothing if already in the solver state
    if let Some(_) = solver.sorts.get(sort) {
        return Ok(sort.clone())
    }

    match sort {

        Sort::Parametric(name, parameters) => {

            // check that the parameters are known sorts
            let _ = parameters.iter()
                .map(|s| { solver.sorts.get(s) })
                .collect::<Option<Vec<_>>>()
                .ok_or("unknown sort")?;

            // instantiate its declaration with the parameters
            if let Identifier::Simple(name) = name {
                let symbol = Symbol(name.0.clone());
                let param_decl = solver.parametric_datatypes.get(&symbol)
                    .ok_or("unknown parametric sort")?;

                match param_decl.clone() {
                    DatatypeDec::Par(variables, constructors) => {
                        if variables.len() == parameters.len() {

                            // build substitution map : Sort -> Sort
                            let old_variables: Vec<Sort> = variables.iter()
                                .map(|s| { Sort::Sort(Identifier::Simple(Symbol(s.0.clone())))})
                                .collect();
                            let subs: IndexMap<Sort, Sort> = old_variables.into_iter()
                                .zip(parameters.iter().cloned())
                                .collect();

                            // instantiate constructors
                            let new_constructors = constructors.into_iter()
                                .map(|c| substitute_in_constructor(c, &subs, solver))
                                .collect::<Result<Vec<_>, _>>()?;

                            // add the declaration to the solver
                            let new_decl = DatatypeDec::DatatypeDec(new_constructors);
                            solver.sorts.insert(sort.clone(), new_decl);

                            return Ok(sort.clone())
                        } else {
                            return Err("wrong number of parameters")
                        }
                    },
                    _ => return Err("not a parametric datatype")
                }
            } else {
                return Err("TODO: not a simple symbol")
            }
        },

        Sort::Sort(_) => {
            return Err("unknown sort")
        },
    }
}

fn substitute_in_constructor(
    constructor: ConstructorDec,
    subs: &IndexMap<Sort, Sort>,
    solver: &mut Solver
) -> Result<ConstructorDec, &'static str> {

    // instantiate the selector declarations
    let new_selector_decs = constructor.1.iter()
        .map(|s| { substitute_in_selector(s, subs, solver) })
        .collect::<Result<Vec<_>,_>>()?;

    Ok(ConstructorDec(constructor.0.clone(), new_selector_decs))
}

fn substitute_in_selector(
    selector: &SelectorDec,
    subs: &IndexMap<Sort, Sort>,
    solver: &mut Solver
) -> Result<SelectorDec, &'static str> {

    let new_sort = substitute_in_sort(&selector.1, subs, solver)?;
    return Ok(SelectorDec(selector.0.clone(), new_sort))

}

fn substitute_in_sort(
    sort: &Sort,
    subs: &IndexMap<Sort, Sort>,
    solver: &mut Solver
) -> Result<Sort, &'static str> {

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
                .map(|s| { substitute_in_sort(s, subs, solver) })
                .collect::<Result<Vec<_>, _>>()?;
            let new_sort = Sort::Parametric(name.clone(), new_sorts);
            create_sort(&new_sort, solver)?;
            return Ok(new_sort)
        }
    }
}