// Copyright Pierre Carbonnelle, 2025.

use crate::{api::{ConstructorDec, DatatypeDec, Identifier, Sort, Symbol}, error::SolverError, solver::Solver};

pub(crate) fn instantiate_sort(
    sort: &Sort,
    solver: &mut Solver
) -> Result<(), SolverError> {
    match sort {
        Sort::Parametric(name, values) => {
            let symbol = Sort::Sort(name.clone());
            if let Some(decl) = solver.sorts.get(&symbol) {
                match decl {
                    DatatypeDec::Par(variables, constructors) => {
                        if variables.len() != values.len() {
                            return Err(SolverError::ExprError("wrong number of parameters".to_string(), None));
                        }
                        let new_constructors = constructors.iter().map(|c| {
                            substitute_in_constructors(c, &variables, &values, solver)?;
                        }).collect();
                        solver.sorts.insert(Sort::Sort(name.clone()), DatatypeDec::DatatypeDec(new_constructors));
                        return Ok(())
                    },
                    _ => return Err(SolverError::ExprError("not a parametric datatype".to_string(), None))
                }
            };
            Err(SolverError::ExprError("unknown sort".to_string(), None))
        },
        _ => Ok(())
    }
}

pub(crate) fn substitute_in_constructors(
    constructor: &ConstructorDec,
    variables: &[Symbol],
    values: &[Sort],
    solver: &mut Solver
) -> Result<ConstructorDec, SolverError> {
    let new_selector_decs = constructor.1.iter().map(|s| {
        substitute_in_selector_dec(s, variables, values, solver)
    }).collect();
    Ok(ConstructorDec(constructor.0.clone(), new_selector_decs))
}