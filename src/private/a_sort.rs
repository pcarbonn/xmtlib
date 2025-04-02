// Copyright Pierre Carbonnelle, 2025.

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rusqlite::{params, Connection};

use crate::api::{ConstructorDec, DatatypeDec, Identifier, Numeral, SelectorDec, Sort, SortDec, Symbol, QualIdentifier};
use crate::{error::SolverError::{self, InternalError}, solver::Solver};
use crate::private::b_fun::FunctionIs;

#[allow(unused_imports)]
use debug_print::debug_println as dprintln;


/////////////////////  Data structure for Sort  ///////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ParametricObject {
    Datatype(DatatypeDec),
    Definition{ variables: Vec<Symbol>, definiendum: Sort },
    Recursive,
    Unknown
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SortObject{
    Normal{datatype_dec: DatatypeDec, table: String, count: usize},  // table name, number of rows
    Recursive,
    Infinite,  // Int, Real, and derived
    Unknown
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum TypeInterpretation{
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
        insert_sort(sort, None, TypeInterpretation::Unknown, None, solver)?;
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
            .ok_or(InternalError(482664))?;
        let (new_decl, table_name) =
            match new_decl.clone()
             {
                SortObject::Normal{datatype_dec, table, count} => {
                    (Some(datatype_dec.clone()), Some((format!(" {table}"), count)))  // front space to say that the table exists already
                },
                SortObject::Recursive
                | SortObject::Infinite
                | SortObject::Unknown => (None, None),
            };
        let new_sort = Sort::Sort(Identifier::Simple(symb));
        insert_sort(new_sort, new_decl, g, table_name, solver)?;

    } else {  // sort must be parametric
        solver.parametric_sorts.insert(symb, ParametricObject::Definition{variables, definiendum});
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


// Returns true if the sort is recursive.
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
        Sort::Sort(Identifier::Indexed(..))
        | Sort::Parametric(Identifier::Indexed(..), _) => ()
    }
    return false
}


///////////////////////  create non-parametric sort  //////////////////////////


/// Adds a non-parametric declaration to the solver,
/// and create database table of its extension.
/// Also adds any required instantiation of parent sorts.
pub(crate) fn create_sort(
    symb: &Symbol,
    decl: &DatatypeDec,
    declaring: &IndexSet<Symbol>,  // to detect mutually-recursive datatypes
    solver: &mut Solver
) -> Result<(), SolverError> {

    if let DatatypeDec::DatatypeDec(constructor_decls) = decl {

        let mut grounding = TypeInterpretation::Normal;
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
        Err(InternalError(5428868))  // unexpected parametric datatype
    }
}

/// Create the sort and its parents in the solver, if not present.
/// Returns the type of grounding of the sort.
/// This function is recursive.
pub(crate) fn instantiate_parent_sort(
    parent_sort: &Sort,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<TypeInterpretation, SolverError> {

    if let Some(sort_object) = solver.sorts.get(parent_sort) {
        // already instantiated
        match sort_object {
            SortObject::Normal{..} => Ok(TypeInterpretation::Normal),
            SortObject::Unknown    => Ok(TypeInterpretation::Unknown),
            SortObject::Infinite   => Ok(TypeInterpretation::Infinite),
            SortObject::Recursive  => Ok(TypeInterpretation::Recursive),
        }
    } else {
        match parent_sort {
            Sort::Sort(id) =>   // check if recursive
                if let Identifier::Simple(symb) = id {
                    if declaring.contains(symb) {
                        insert_sort(parent_sort.clone(), None, TypeInterpretation::Recursive, None, solver)
                    } else {
                        Err(InternalError(741265)) // it should be in the solver already
                    }
                } else {  // indexed identifier
                    insert_sort(parent_sort.clone(), None, TypeInterpretation::Unknown, None, solver)
                },

            Sort::Parametric(id, parameters) => {
                // running example: Pair Color Color
                if let Identifier::Simple(symb) = id {

                    // check if recursive
                    if declaring.contains(symb) {
                        return insert_sort(parent_sort.clone(), None, TypeInterpretation::Recursive, None, solver)
                    }

                    // (declare-datatype Pair (par (X Y) ( ( white ) (pair (first X) (second Y)))))
                    let parent_decl = solver.parametric_sorts.get(symb)
                        .ok_or(InternalError(2785648))?;  // the parametric type should be in the solver

                    match parent_decl.clone() {
                        ParametricObject::Datatype(DatatypeDec::Par(variables, constructors)) => {
                            // variables: (X Y)
                            // constructors: ( ( white ) (pair (first X) (second Y))))
                            // we assume variables.len() = parameters.len()

                            // build substitution map : Sort -> Sort
                            // X->Color, Y->Color
                            let subs = sort_mapping(variables, parameters);

                            // instantiate constructors
                            let mut grounding = TypeInterpretation::Normal;
                            let mut new_constructors = vec![]; // ( ( white ) (pair (first Color) (second Color))))
                            for c in constructors {
                                let mut new_selectors = vec![]; // first Color, second Color
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
                        ParametricObject::Definition{variables, definiendum, } => {
                            // running example: parent_sort is (MyPair Color Color)
                            // parent_decl: (define-sort MyPair (T) (Pair T T))

                            // substitute to get new sort
                            let subs = sort_mapping(variables, parameters); // T->Color
                            let (new_g, new_sort) = substitute_in_sort(&definiendum, &subs, declaring, solver)?; // (Pair Color Color)

                            // get the name of the table
                            let sort_object = solver.sorts.get(&new_sort)
                                .ok_or(InternalError(7842966))?;

                            // create sort object
                            match sort_object {
                                SortObject::Normal{table, count, ..} => {
                                    let alias = Some((format!(" {table}"), count.clone()));
                                    insert_sort(parent_sort.clone(), None, new_g, alias, solver)  // front space to say that the table exists already
                                },
                                SortObject::Infinite
                                | SortObject::Recursive
                                | SortObject::Unknown => {
                                    insert_sort(parent_sort.clone(), None, new_g, None, solver)
                                }
                            }

                        }
                        ParametricObject::Datatype(DatatypeDec::DatatypeDec(_)) => {
                            Err(InternalError(1786496))  // Unexpected non-parametric type
                        },
                        ParametricObject::Recursive => {
                            insert_sort(parent_sort.clone(), None, TypeInterpretation::Recursive, None, solver)
                        },
                        ParametricObject::Unknown => {
                            insert_sort(parent_sort.clone(), None, TypeInterpretation::Unknown, None, solver)
                        }
                    }
                } else {  // indexed identifier
                    insert_sort(parent_sort.clone(), None, TypeInterpretation::Unknown, None, solver)
                }
            },
        }}
}


/// Creates a mapping from Sort-variables to Sort
fn sort_mapping(
    variables: Vec<Symbol>,  // a variable representing a sort
    values: &Vec<Sort>
) -> IndexMap<Sort, Sort> {
    let old_variables: Vec<Sort> = variables.iter()
        .map(|s| { Sort::Sort(Identifier::Simple(s.clone()))})
        .collect();
    old_variables.into_iter()
        .zip(values.iter().cloned())
        .collect()
}


fn substitute_in_sort(
    sort: &Sort,
    subs: &IndexMap<Sort, Sort>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver,
) -> Result<(TypeInterpretation, Sort), SolverError> {

    match sort {

        Sort::Sort(_) => {
            // substitute if in the substitution map
            let new_sort = subs.get(sort).unwrap_or(sort).clone();
            let new_g = instantiate_parent_sort(&new_sort, declaring, solver)?;
            Ok((new_g, new_sort))
        },

        Sort::Parametric(id, sorts) => {
            let mut grounding = TypeInterpretation::Normal;
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
    grounding: TypeInterpretation,
    alias: Option<(String, usize)>,  // name and size of the table that `sort` is an alias for.
    solver: &mut Solver,
) -> Result<TypeInterpretation, SolverError> {

    if ! solver.sorts.contains_key(&sort) { // a new sort

        let i = solver.sorts.len();
        let sort_object =
            match grounding {
                TypeInterpretation::Normal => {
                    if let Some(datatype_dec) = decl {
                        match datatype_dec {
                            DatatypeDec::DatatypeDec(ref constructor_decls) => {
                                if let Some((table, count)) = alias {
                                    SortObject::Normal{datatype_dec, table, count}
                                } else {
                                    let table = if let Sort::Sort(Identifier::Simple(Symbol(ref name))) = sort {
                                        name.to_string()  // todo: sanitize name (several places)
                                    } else {
                                        format!("Sort_{}", i)
                                    };
                                    let count = create_table(&table, &constructor_decls, solver)?;
                                    SortObject::Normal{datatype_dec, table, count}
                                }
                            },
                            DatatypeDec::Par(..) => {
                                return Err(InternalError(8458555))
                            },
                        }
                    } else {
                        SortObject::Unknown
                    }
                },
                TypeInterpretation::Unknown => SortObject::Unknown,
                TypeInterpretation::Infinite => SortObject::Infinite,
                TypeInterpretation::Recursive => SortObject::Recursive,
            };

        // update solver.sorts
        solver.sorts.insert(sort, sort_object);
    }

    Ok(grounding)
}


fn create_table(
    table: &str,
    constructor_decls: &Vec<ConstructorDec>,
    solver: &mut Solver
) -> Result<usize, SolverError> {
    let mut count;

    // running example: (declare-datatype P ((white ) (pair (first Color) (second Color))))

    // 1st pass: collect nullary constructors and selectors
    // in ((white ) (pair (first Color) (second Color)))
    let mut nullary: Vec<String> = vec![]; // white
    let mut column_names: IndexMap<String, String> = IndexMap::new();  // first: Text, second: Int
    for constructor_decl in constructor_decls {
        let ConstructorDec(constructor, selectors) = constructor_decl;
        if selectors.len() == 0 {
            nullary.push(constructor.0.clone());
            let qual_identifier = QualIdentifier::Identifier(Identifier::Simple(constructor.clone()));
            solver.functions.insert(qual_identifier, FunctionIs::Constructor);
        } else {
            for SelectorDec(selector, sort) in selectors {
                let type_ = match sort.to_string().as_str() {
                    "Int" => "INTEGER",
                    "Real" => "REAL",
                    _ => "TEXT"
                };
                column_names.insert(selector.0.clone(), type_.to_string());
            }
        }
    }
    count = nullary.len();

    if column_names.len() == 0 {  // nullary constructors only

        create_core_table(table, nullary, &mut solver.conn)?;

    } else {  // with constructors

        let mut selects: Vec<String> = vec![];

        if 0 < nullary.len() {
            let core = format!("{table}_core");
            create_core_table(&core, nullary, &mut solver.conn)?;

            //  "NULL as first, NULL as second"
            let projection = column_names.iter().map(|(n, _)| format!("NULL AS {n}")).collect::<Vec<_>>().join(", ");

            // the first select is "SELECT NULL as constructor, NULL as first, NULL as second, Color_core.G as G from Color_core"
            selects.push(format!("SELECT NULL as constructor, {projection}, {core}.G AS G from {core}"));
        }

        // add "select "pair" as constructor, T1.G as first, T2.G as second, construct("pair", T1.G, T2.G) as G
        //      from Color as T1 join Color as T2"
        for constructor_decl in constructor_decls { // e.g. (pair (first Color) (second Color))
            let ConstructorDec(constructor, selectors) = constructor_decl;

            let qual_identifier = QualIdentifier::Identifier(Identifier::Simple(constructor.clone()));
            solver.functions.insert(qual_identifier, FunctionIs::Constructor);

            if selectors.len() != 0 {  // otherwise, already in core table

                // compute the list of tables and column sort_mapping
                let mut tables = Vec::with_capacity(selectors.len()); // [Color, Color]
                let mut columns = IndexMap::with_capacity(column_names.len());  // {first->T1.G, second->T2.G}; the value can be NULL
                for (column_name, _) in &column_names {
                    columns.insert(column_name, "NULL".to_string());
                }
                let mut row_product = 1;
                for (i, SelectorDec(selector, sort)) in selectors.iter().enumerate() {
                    let sort_object = solver.sorts.get(&sort.clone())
                        .ok_or(InternalError(7459455))?;
                    if let SortObject::Normal{table, count, ..} = sort_object {
                        tables.push(table.clone());
                        columns.insert(&selector.0, format!("T{i}.G"));
                        row_product *= count;
                    } else {
                        return Err(InternalError(7529545))
                    }
                }
                count += row_product;

                // "pair"
                let constructor = &constructor.0;

                // "T1.G AS first, T2.G as second"
                let projection = columns.iter()
                    .map(|(k, v)| format!("{v} AS {k}")) // v can also be NULL
                    .collect::<Vec<String>>().join(", ");

                // "T1.G, T2.G"
                let parameters = (0..selectors.len()).map(|i| format!("T{i}.G")).collect::<Vec<_>>().join(", ");
                // construct("pair", T1.G, T2.G) AS G
                let g = format!("construct(\"{}\", {}) AS G", constructor, parameters);

                // "Color as T1 join Color as T2"
                let joins = tables.iter().enumerate().map(|(i, t)| format!("{t} as T{i}")).join(" JOIN ");

                selects.push(format!("SELECT \"{constructor}\" AS constructor, {projection}, {g} FROM {joins}"))
            }
        }
        let columns = column_names.iter()
            .map( |(name, type_)| format!("{name} {type_}"))
            .collect::<Vec<_>>().join(", ");
        let create = format!("CREATE TABLE {table} (constructor TEXT, {columns}, G TEXT PRIMARY KEY)");
        solver.conn.execute(&create, ())?;

        let columns = column_names.iter()
            .map( |(name, _)| name.to_string())
            .collect::<Vec<_>>().join(", ");
        let insert = format!("INSERT INTO {table} (constructor, {columns}, G) {}", selects.join( " UNION "));
        solver.conn.execute(&insert, ())?;
    }
    Ok(count)
}

/// creates a table in the DB containing the nullary constructors
fn create_core_table(
    table: &str,
    values: Vec<String>,
    conn: &mut Connection
) -> Result<(), SolverError> {

    conn.execute(&format!("CREATE TABLE {table} (G TEXT PRIMARY KEY)"), ())?;

    let mut stmt = conn.prepare(&format!("INSERT INTO {table} (G) VALUES (?)"))?;
    for value in values {
        stmt.execute(params![value])?;
    }
    Ok(())
}