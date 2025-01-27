// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use rusqlite::Connection;

use crate::api::{ConstructorDec, DatatypeDec, Identifier, Numeral, SelectorDec, Sort, SortDec, Symbol};
use crate::{error::SolverError, solver::Solver};

#[allow(unused_imports)]
use debug_print::debug_println as dprintln;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ParametricObject {
    Datatype(DatatypeDec),
    Definition(Vec<Symbol>, Sort),
    Recursive,
    Unknown
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SortObject{
    Normal(DatatypeDec, String),  // table name
    Recursive,
    Infinite,  // Int, Real, and derived
    Unknown
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Grounding{
    Normal,  // lowest
    Unknown,
    Infinite,
    Recursive  // highest
}

/////////////////////  Commands ///////////////////////////////////////////////


pub(crate) fn declare_datatype(
    symb: Symbol,
    dec: DatatypeDec,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    declare_datatypes(
        vec![SortDec(symb, Numeral(0))],  // don't care for the numeral
        vec![dec],
        command,
        solver
    )
}


pub(crate) fn declare_datatypes(
    sort_decs: Vec<SortDec>,
    decs: Vec<DatatypeDec>,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;  // this also validates the declaration

    // collect the declared symbols, for recursivity detection
    let declaring = sort_decs.iter().map(|sd| {
            let SortDec(symb, _) = sd;
            symb.clone()
        })
        .collect();

    for (SortDec(symb, _), dec) in sort_decs.into_iter().zip(decs.into_iter()) {
        match dec {
            DatatypeDec::Par(_, ref constructor_decs) =>
                create_parametric_sort(&symb, &dec, &constructor_decs, &declaring, solver)?,
            DatatypeDec::DatatypeDec(_) =>
                create_sort(&symb, &dec, &declaring, solver)?,
        };
    }

    Ok(out)
}

pub(crate) fn declare_sort(
    symb: Symbol,
    numeral: Numeral,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;

    if numeral.0 == 0 {
        let sort = Sort::Sort(Identifier::Simple(symb));
        insert_sort(sort, None, Grounding::Unknown, None, solver)?;
    } else {
        let dt_object = ParametricObject::Unknown;
        solver.parametric_sorts.insert(symb, dt_object);
    }

    Ok(out)
}

pub(crate) fn define_sort(
    symb: Symbol,
    variables: Vec<Symbol>,
    definiendum: Sort,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;

    if variables.len() == 0 {  // non-parametric
        let declaring = IndexSet::new();
        let g = instantiate_parent_sort(&definiendum, &declaring, solver)?;

        let new_decl = solver.sorts.get(&definiendum)
            .ok_or(SolverError::InternalError(482664))?;
        let (new_decl, table_name) =
            match new_decl.clone()
             {
                SortObject::Normal(datatype_dec, table_name) => {
                    (Some(datatype_dec.clone()), Some(format!(" {table_name}")))  // front space to say that the table exists already
                },
                SortObject::Recursive
                | SortObject::Infinite
                | SortObject::Unknown => (None, None),
            };
        let new_sort = Sort::Sort(Identifier::Simple(symb));
        insert_sort(new_sort, new_decl, g, table_name, solver)?;

    } else {  // sort must be parametric
        solver.parametric_sorts.insert(symb, ParametricObject::Definition(variables, definiendum));
    }

    Ok(out)
}


///////////////////////  create_parametric_sort  //////////////////////////////


/// adds a parametric declaration to the solver.
pub(crate) fn create_parametric_sort(
    symb: &Symbol,
    dec: &DatatypeDec,
    constructor_decs: &Vec<ConstructorDec>,  // this redundant argument is for convenience
    declaring: &IndexSet<Symbol>,  // to detect mutually-recursive datatypes
    solver: &mut Solver
) -> Result<(), SolverError> {

    // Helper function that returns true if the sort is recursive.
    // This function is recursive.
    fn recursive_sort(
        sort: &Sort,
        declaring: &IndexSet<Symbol>
    ) -> bool {
        match sort {
            Sort::Sort(Identifier::Simple(symb)) => {
                if declaring.contains(symb) { return true }
            },
            Sort::Parametric(Identifier::Simple(symb), sorts) => {
                if declaring.contains(symb) { return true }

                for sort in sorts {
                    if recursive_sort(sort, declaring) { return true }
                }
            },
            _ => ()  // indexed sort
        }
        return false
    }

    let mut recursive = false;
    for constructor_dec in constructor_decs {
        for SelectorDec(_, sort) in &constructor_dec.1 {
            if recursive_sort(sort, declaring) {
                recursive = true;
                break
            }
        }
    }

    if recursive {
        solver.parametric_sorts.insert(symb.clone(), ParametricObject::Recursive);
    } else {
        let value = ParametricObject::Datatype(dec.clone());
        solver.parametric_sorts.insert(symb.clone(), value);
    }
    Ok(())
}


///////////////////////  create non-parametric sort  //////////////////////////


/// Adds a non-parametric declaration to the solver.
/// Also adds any required instantiation of parent sorts.
pub(crate) fn create_sort(
    symb: &Symbol,
    decl: &DatatypeDec,
    declaring: &IndexSet<Symbol>,  // to detect mutually-recursive datatypes
    solver: &mut Solver
) -> Result<(), SolverError> {

    if let DatatypeDec::DatatypeDec(constructor_decls) = decl {

        let mut grounding = Grounding::Normal;
        // instantiate parent sorts first
        for constructor_decl in constructor_decls {
            let ConstructorDec(_, selectors) = constructor_decl;
            for SelectorDec(_, sort) in selectors {
                let g = instantiate_parent_sort(&sort, declaring, solver)?;
                grounding = max(grounding, g);
            }
        }

        //
        let key = Sort::Sort(Identifier::Simple(symb.clone()));
        insert_sort(key, Some(decl.clone()), grounding, None, solver)?;
        Ok(())

    } else {
        Err(SolverError::InternalError(5428868))  // unexpected parametric datatype
    }
}

/// Create the sort and its parents in the solver, if not present.
/// Returns the type of grounding of the sort.
/// This function is recursive.
fn instantiate_parent_sort(
    parent_sort: &Sort,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<Grounding, SolverError> {

    // Helper function
    fn mapping(
        variables: Vec<Symbol>,
        values: &Vec<Sort>
    ) -> IndexMap<Sort, Sort> {
        let old_variables: Vec<Sort> = variables.iter()
            .map(|s| { Sort::Sort(Identifier::Simple(s.clone()))})
            .collect();
        old_variables.into_iter()
            .zip(values.iter().cloned())
            .collect()
    }

    if let Some(sort_object) = solver.sorts.get(parent_sort) {
        match sort_object {
            SortObject::Normal(_, _) => Ok(Grounding::Normal),
            SortObject::Unknown      => Ok(Grounding::Unknown),
            SortObject::Infinite     => Ok(Grounding::Infinite),
            SortObject::Recursive    => Ok(Grounding::Recursive),
        }
    } else {
        match parent_sort {
            Sort::Sort(id) =>   // check if recursive
                if let Identifier::Simple(symb) = id {
                    if declaring.contains(symb) {
                        insert_sort(parent_sort.clone(), None, Grounding::Recursive, None, solver)
                    } else {
                        Err(SolverError::InternalError(741265)) // it should be in the solver already
                    }
                } else {
                    Err(SolverError::InternalError(821652)) // unexpected indexed identifier
                },

            Sort::Parametric(id, parameters) => {
                if let Identifier::Simple(symb) = id {

                    // check if recursive
                    if declaring.contains(symb) {
                        return insert_sort(parent_sort.clone(), None, Grounding::Recursive, None, solver)
                    }

                    let parent_decl = solver.parametric_sorts.get(symb)
                        .ok_or(SolverError::InternalError(2785648))?;  // the parametric type should be in the solver

                    match parent_decl.clone() {
                        ParametricObject::Datatype(DatatypeDec::Par(variables, constructors)) => {
                            // we assume variables.len() = parameters.len()

                            // build substitution map : Sort -> Sort
                            let subs = mapping(variables, parameters);

                            // instantiate constructors
                            let mut grounding = Grounding::Normal;
                            let mut new_constructors = vec![];
                            for c in constructors {
                                let mut new_selectors = vec![];
                                for s in c.1 {
                                    let (new_g, new_sort) = substitute_in_sort(&s.1, &subs, declaring, solver)?;
                                    grounding = max(grounding, new_g);
                                    let new_selector = SelectorDec(s.0, new_sort);
                                    new_selectors.push(new_selector)
                                }
                                let new_c = ConstructorDec(c.0.clone(), new_selectors);
                                new_constructors.push(new_c);
                            }

                            // add the declaration to the solver
                            let new_decl = DatatypeDec::DatatypeDec(new_constructors);
                            insert_sort(parent_sort.clone(), Some(new_decl), grounding, None, solver)
                        },
                        ParametricObject::Definition(variables, definiendum, ) => {
                            // substitute to get new sort
                            let subs = mapping(variables, parameters);
                            let (new_g, new_sort) = substitute_in_sort(&definiendum, &subs, declaring, solver)?;

                            // get the name of the table
                            let sort_object = solver.sorts.get(&new_sort)
                                .ok_or(SolverError::InternalError(7842966))?;

                            // create sort object
                            match sort_object {
                                SortObject::Normal(_, table) => {
                                    let table_name = Some(format!(" {table}"));
                                    insert_sort(parent_sort.clone(), None, new_g, table_name, solver)  // front space to say that the table exists already
                                },
                                SortObject::Infinite
                                | SortObject::Recursive
                                | SortObject::Unknown => {
                                    insert_sort(parent_sort.clone(), None, new_g, None, solver)
                                }
                            }

                        }
                        ParametricObject::Datatype(DatatypeDec::DatatypeDec(_)) => {
                            Err(SolverError::InternalError(1786496))  // Unexpected non-parametric type
                        },
                        ParametricObject::Recursive => {
                            insert_sort(parent_sort.clone(), None, Grounding::Recursive, None, solver)
                        },
                        ParametricObject::Unknown => {
                            insert_sort(parent_sort.clone(), None, Grounding::Unknown, None, solver)
                        }
                    }
                } else {
                    Err(SolverError::InternalError(71845846))  // unexpected indexed identifier
                }
            },
        }}
}


fn substitute_in_sort(
    sort: &Sort,
    subs: &IndexMap<Sort, Sort>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<(Grounding, Sort), SolverError> {

    match sort {

        Sort::Sort(_) => {
            // substitute if in the substitution map
            let new_sort = subs.get(sort).unwrap_or(sort).clone();
            let new_g = instantiate_parent_sort(&new_sort, declaring, solver)?;
            Ok((new_g, new_sort))
        },

        Sort::Parametric(id, sorts) => {
            let mut grounding = Grounding::Normal;
            let mut new_sorts = vec![];
            for s in sorts {
                let (new_g, new_s) = substitute_in_sort(s, subs, declaring, solver)?;
                grounding = max(grounding, new_g);
                new_sorts.push(new_s);
            }
            let new_sort = Sort::Parametric(id.clone(), new_sorts);
            let new_g = instantiate_parent_sort(&new_sort, declaring, solver)?;
            Ok((new_g, new_sort))
        }
    }
}


///////////////////////  insert sort  /////////////////////////////////////////


/// Make the non-parametric sort known to the solver, and create its table
fn insert_sort(
    sort: Sort,
    decl: Option<DatatypeDec>,
    grounding: Grounding,
    table_name: Option<String>,
    solver: &mut Solver,
) -> Result<Grounding, SolverError> {

    // update solver.sort
    if ! solver.sorts.contains_key(&sort) { // a new sort

        let i = solver.sorts.len();
        let sort_object =
            match grounding {
                Grounding::Normal => {
                    if let Some(decl) = decl {
                        match decl {
                            DatatypeDec::DatatypeDec(_) => {
                                if let Some(name) = table_name {
                                    SortObject::Normal(decl, name.to_string())
                                } else if let Sort::Sort(Identifier::Simple(Symbol(ref name))) = sort {
                                    SortObject::Normal(decl, name.to_string())
                                } else {
                                    SortObject::Normal(decl, format!("Sort_{}", i))
                                }
                            },
                            DatatypeDec::Par(_, _) => {
                                SortObject::Normal(decl, format!("Sort_{}", i))
                            },
                        }

                    } else {
                        SortObject::Unknown
                    }
                },
                Grounding::Unknown => SortObject::Unknown,
                Grounding::Infinite => SortObject::Infinite,
                Grounding::Recursive => SortObject::Recursive,
            };

        // update solver.sorts
        create_table(sort_object.clone(), solver)?;
        solver.sorts.insert(sort, sort_object);
    }

    Ok(grounding)
}

fn create_table(
    sort_object: SortObject,
    solver: &mut Solver
) -> Result<(), SolverError> {
    if let SortObject::Normal(datatype_dec, table_name) = sort_object {
        if ! table_name.starts_with(' ') {
            if let DatatypeDec::DatatypeDec(constructor_decls) = datatype_dec {

                // 1st pass: collect nullary constructors and selectors
                let mut nullary: Vec<String> = vec![];
                let mut columns: IndexSet<String> = IndexSet::new();
                for constructor_decl in constructor_decls {
                    let ConstructorDec(constructor, selectors) = constructor_decl;
                    if selectors.len() == 0 {
                        nullary.push(constructor.0)
                    } else {
                        for SelectorDec(selector, _) in selectors {
                            columns.insert(selector.0.clone());
                        }
                    }
                }

                // helper function
                fn core_table(
                    table_name: String,
                    values: Vec<String>,
                    conn: &mut Connection
                ) -> Result<(), SolverError> {
                    conn.execute(format!("CREATE TABLE {table_name} (G TEXT)").as_str(), ())?;
                    for value in values {
                        conn.execute(format!("INSERT INTO {table_name} (G) VALUES (?1)").as_str(), [value])?;
                    }
                    Ok(())
                }

                if columns.len() == 0 {  // nullary constructors only
                    core_table(table_name, nullary, &mut solver.conn)?;
                } else {
                    core_table(format!("{table_name}_core"), nullary, &mut solver.conn)?;
                    // if selectors: create table as (Select...)
                    //     fill it with the nullary constructors
                    //     fill it with the other constructors
                }

            } else {
                return Err(SolverError::InternalError(84585455));
            }
        }
    }
    Ok(())
}


