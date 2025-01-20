// Copyright Pierre Carbonnelle, 2025.

use indexmap::IndexMap;

use crate::{api::{ConstructorDec, DatatypeDec, Identifier, SelectorDec, Sort}};
use crate::grammar::ParsingState;

#[allow(unused_imports)]
use debug_print::{debug_println as dprintln};


/// returns a Sort if the identifier is known or a variable
pub(crate) fn sort_from_identifier(
    identifier: Identifier,
    state: &ParsingState
) -> Result<Sort, &'static str> {

    let sort = Sort::Sort(identifier.clone());
    if ! state.solver.sorts.contains_key(&sort) {
        if let Identifier::Simple(ref symb) = identifier {  // is it a variable ?
            if ! state.variables.contains(symb) {
                return Err("known sort")  // Expected: known sort
            }
        } else {
            return Err("known sort")
        }
    }
    return Ok(sort)
}


/// returns true if the sort is known or constructed from known sorts
fn is_known_sort(
    sort: &Sort,
    state: &ParsingState
) -> bool {

    if state.solver.sorts.contains_key(sort) {
        return true
    }
    match sort {
        Sort::Sort(Identifier::Simple(ref symb)) => {
            return state.variables.contains(symb)
        },
        Sort::Parametric(Identifier::Simple(ref symb), sorts) => {
            if ! state.solver.parametric_datatypes.contains_key(symb) {
                return false
            }
            return sorts.iter().all(|s| is_known_sort(s, state))
        },
        _ => return false  // I don't see how this could happen
    }
}


/// also adds any required instantiation of a parametric sort to the solver.
pub(crate) fn create_parametered_sort(
    id: Identifier,
    parameters: Vec<Sort>,
    state: &mut ParsingState,
) -> Result<Sort, &'static str> {

    let sort = Sort::Parametric(id.clone(), parameters.clone());

    if ! is_known_sort(&sort, state) {
        return Err("known sort")
    }

    if state.variables.len() != 0 {  // can't instantiate yet
        return Ok(sort)
    }

    // do nothing if already in the solver state
    if let Some(_) = state.solver.sorts.get(&sort) {
        return Ok(sort)
    }

    // instantiate the declaration with the parameters
    if let Identifier::Simple(name) = id {
        let param_decl = state.solver.parametric_datatypes.get(&name)
            .ok_or("known parametric sort")?;

        match param_decl.clone() {
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
                        .map(|c| substitute_in_constructor(c, &subs, state))
                        .collect::<Result<Vec<_>, _>>()?;

                    // add the declaration to the solver
                    let new_decl = DatatypeDec::DatatypeDec(new_constructors);
                    state.solver.sorts.insert(sort.clone(), new_decl);

                    return Ok(sort)
                } else {
                    return Err("correct number of parameters")
                }
            },
            _ => return Err("a parametric datatype")
        }
    } else {
        return Err("TODO: not a simple symbol")  // I don't see how this could happen
    }
}


fn substitute_in_constructor(
    constructor: ConstructorDec,
    subs: &IndexMap<Sort, Sort>,
    state: &mut ParsingState
) -> Result<ConstructorDec, &'static str> {

    // instantiate the selector declarations
    let new_selector_decs = constructor.1.iter()
        .map(|s| { substitute_in_selector(s, subs, state) })
        .collect::<Result<Vec<_>,_>>()?;

    Ok(ConstructorDec(constructor.0.clone(), new_selector_decs))
}

fn substitute_in_selector(
    selector: &SelectorDec,
    subs: &IndexMap<Sort, Sort>,
    state: &mut ParsingState
) -> Result<SelectorDec, &'static str> {

    let new_sort = substitute_in_sort(&selector.1, subs, state)?;
    return Ok(SelectorDec(selector.0.clone(), new_sort))

}

fn substitute_in_sort(
    sort: &Sort,
    subs: &IndexMap<Sort, Sort>,
    state: &mut ParsingState
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
                .map(|s| { substitute_in_sort(s, subs, state) })
                .collect::<Result<Vec<_>, _>>()?;
            create_parametered_sort(name.clone(), new_sorts, state)
        }
    }
}