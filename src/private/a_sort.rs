// Copyright Pierre Carbonnelle, 2025.

// Sorts have 3 main attributes:
// * monomorphic or polymorphic (having variables)
// * non-parametric or parametric (a concretisation of a polymorphic sort)
// * base or defined (by a `(define-sort` command)

use std::cmp::max;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rusqlite::{params, Connection};

use crate::ast::{ConstructorDec, DatatypeDec, Identifier, Index, Numeral, QualIdentifier, SelectorDec, Sort, SortDec, Symbol, L};
use crate::error::{SolverError::{self, InternalError}, Offset};
use crate::solver::{CanonicalSort, Solver, TableType};
use crate::private::b_fun::{Interpretation, FunctionObject};
use crate::private::e1_ground_view::Ids;
use crate::private::e2_ground_query::TableName;

#[allow(unused_imports)]
use debug_print::debug_println as dprintln;


/////////////////////  Data structure for Sort  ///////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum PolymorphicObject {
    SortDefinition{ variables: Vec<Symbol>, definiendum: Sort }, // (define-sort
    Datatype(DatatypeDec), // (declare-datatype
    RecursiveDT(DatatypeDec), // (declare-datatype
    Unknown  // (declare-sort
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SortObject{
    Normal{datatype_dec: DatatypeDec, table: TableName, row_count: usize},  // table name, number of rows.  DatatypeDec is monomorphic
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

    for (SortDec(symb, _), dec) in sort_decs.iter().zip(decs.iter()) {
        match dec {
            DatatypeDec::Par(_, ref constructor_decs) => {
                // for recursivity detection
                let declaring = sort_decs.iter()
                    .map(|sd| sd.0.clone())
                    .collect();
                create_polymorphic_sort(&symb, &dec, &constructor_decs, &declaring, solver)?
            }
            DatatypeDec::DatatypeDec(_) => {
                // for recursivity detection
                let declaring = sort_decs.iter()
                    .map(|sd| Sort::new(&sd.0))
                    .collect();
                create_monomorphic_sort(&symb, &dec, &declaring, solver)?
            }
        };
    }

    Ok(out)
}

pub(crate) fn declare_sort(
    symb: Symbol,
    arity: Numeral,
    command: String,
    solver: &mut Solver
) -> Result<String, SolverError> {

    let out = solver.exec(&command)?;

    if arity.0 == 0 {
        let sort = Sort::new(&symb);
        insert_sort(sort, TypeInterpretation::Unknown, None, solver)?;
    } else {
        let dt_object = PolymorphicObject::Unknown;
        solver.polymorphic_sorts.insert(symb, dt_object);
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

    if variables.len() == 0 {  // monomorphic
        let new_sort = Sort::new(&symb);
        let declaring = IndexSet::new();
        let g = instantiate_sort(&definiendum, &declaring, solver)?;

        let canonical = solver.canonical_sorts.get(&definiendum)
            .ok_or(InternalError(845667))?;
        let new_sort_object = solver.sort_objects.get(canonical)
            .ok_or(InternalError(482664))?;
        insert_alias(new_sort, g, canonical.clone(), new_sort_object.clone(), solver)?;

    } else {  // sort must is polymorphic
        solver.polymorphic_sorts.insert(symb, PolymorphicObject::SortDefinition{variables, definiendum});
    }

    Ok(out)
}


///////////////////////  create_polymorphic_sort  //////////////////////////////


/// adds a polymorphic declaration to the solver.
///
/// # Arguments:
///
/// * constructor_decs: this redundant argument is for convenience
/// * declaring:  to detect mutually-recursive datatypes
///
pub(crate) fn create_polymorphic_sort(
    symb: &Symbol,
    dec: &DatatypeDec,
    constructor_decs: &Vec<ConstructorDec>,
    declaring: &IndexSet<Symbol>,
    solver: &mut Solver
) -> Result<(), SolverError> {

    let mut recursive = false;
    let mut constructor_set = IndexSet::new();  // to check for duplicate
    for constructor_decl in constructor_decs {
        let ConstructorDec(constructor, selectors) = constructor_decl;
        constructor_set.insert(constructor);

        for SelectorDec(_, sort) in selectors {
            if recursive_sort(sort, declaring) {
                recursive = true;
                break
            }
        }
    }
    if constructor_set.len() != constructor_decs.len() {
        return Err(SolverError::ExprError(format!("Duplicate constructor for {symb}.").to_string()))
    }

    if recursive {
        solver.polymorphic_sorts.insert(symb.clone(), PolymorphicObject::RecursiveDT(dec.clone()));
    } else {
        let value = PolymorphicObject::Datatype(dec.clone());
        solver.polymorphic_sorts.insert(symb.clone(), value);
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
        Sort::Sort(L(Identifier::Simple(symb), _)) => {
            if declaring.contains(symb) { return true }
        },
        Sort::Parametric(L(Identifier::Simple(symb), _), sorts) => {
            if declaring.contains(symb) { return true }

            for sort in sorts {
                if recursive_sort(sort, declaring) { return true }
            }
        },
        Sort::Sort(L(Identifier::Indexed(..), _))
        | Sort::Parametric(L(Identifier::Indexed(..), _), _) =>
            ()  // cannot match symbol
    }
    return false
}


///////////////////////  create monomorphic sort  //////////////////////////


/// Adds a monomorphic declaration to the solver,
/// and create database table of its extension.
/// Also adds any required instantiation of parent sorts.
///
/// # Arguments:
///
/// * declaring: to detect mutually-recursive datatypes
///
pub(crate) fn create_monomorphic_sort(
    symb: &Symbol,
    decl: &DatatypeDec,
    declaring: &IndexSet<Sort>,
    solver: &mut Solver
) -> Result<(), SolverError> {

    if let DatatypeDec::DatatypeDec(constructor_decls) = decl {

        let key = Sort::new(symb);

        let mut grounding = TypeInterpretation::Normal;
        let mut qualify = IndexMap::new();
        // instantiate parent sorts first
        let mut constructor_set = IndexSet::new();  // to check for duplicate
        for constructor_decl in constructor_decls {
            let ConstructorDec(constructor, selectors) = constructor_decl;
            constructor_set.insert(constructor);

            for SelectorDec(_, sort) in selectors {
                let g = instantiate_sort(&sort, declaring, solver)?;
                grounding = max(grounding, g);
            }
            // no qualification needed
            let qualified = QualIdentifier::new(constructor, None);
            qualify.insert(constructor.clone(), qualified);
        }
        if constructor_set.len() != constructor_decls.len() {
            return Err(SolverError::ExprError(format!("Duplicate constructor for {symb}").to_string()))
        }

        insert_sort(key, grounding, Some((decl.clone(), qualify)), solver)?;
        Ok(())

    } else {
        Err(InternalError(5428868))  // unexpected polymorphic datatype
    }
}


/// Create a monomorphic sort and its parents in the solver, if not present.
/// Returns the type of grounding of the sort.
/// This function is recursive.
pub(crate) fn instantiate_sort(
    sort: &Sort,
    declaring: &IndexSet<Sort>,
    solver: &mut Solver,
) -> Result<TypeInterpretation, SolverError> {

    if let Some(sort_object) = get_sort_object(sort, solver) {
        // already instantiated
        match sort_object {
            SortObject::Normal{..} => Ok(TypeInterpretation::Normal),
            SortObject::Unknown    => Ok(TypeInterpretation::Unknown),
            SortObject::Infinite   => Ok(TypeInterpretation::Infinite),
            SortObject::Recursive  => Ok(TypeInterpretation::Recursive),
        }
    } else if declaring.contains(sort) {
        insert_sort(sort.clone(), TypeInterpretation::Recursive, None, solver)
    } else {
        match sort {
            Sort::Sort(_) =>   // check if recursive
                Err(SolverError::ExprError(format!("Unknown sort: {sort}"))),

            Sort::Parametric(id, parameters) => {
                // running example: sort is (Pair Color Color)
                if let L(Identifier::Simple(symb), _) = id {

                    // (declare-datatype Pair (par (X Y) ( ( white ) (pair (first X) (second Y)))))
                    let polymorphic_object = solver.polymorphic_sorts.get(symb)
                        .ok_or(InternalError(2785648))?;  // the parametric type should be in the solver

                    let mut grounding = TypeInterpretation::Normal;
                    match polymorphic_object.clone() {
                        PolymorphicObject::Datatype(DatatypeDec::Par(variables, constructors))
                        | PolymorphicObject::RecursiveDT(DatatypeDec::Par(variables, constructors)) => {
                            // variables: (X Y)
                            // constructors: ( ( white ) (pair (first X) (second Y))))
                            // we assume variables.len() = parameters.len()

                            // build substitution map : Sort -> Sort
                            // X->Color, Y->Color
                            let subs = sort_mapping(&variables, parameters);

                            let var_count = variables.len();
                            let mut variable_set = IndexSet::new();
                            variable_set.extend(variables.into_iter());
                            if variable_set.len() != var_count {
                                return Err(SolverError::IdentifierError("Duplicate variable", id.clone()))
                            }

                            // instantiate constructors
                            let mut declaring = declaring.clone();
                            declaring.insert(sort.clone());
                            let mut new_constructors = vec![]; // ( ( white ) (pair (first Color) (second Color))))
                            let mut qualify = IndexMap::new();
                            for c in constructors {  // ( white ), (pair (first X) (second Y))
                                let mut new_selectors = vec![];
                                let mut variables_found= IndexSet::new();
                                for s in c.1 {  // (first X), (second Y)
                                    let (new_g, new_sort) = substitute_in_sort(&s.1, &subs, &declaring, solver)?;
                                    grounding = max(grounding, new_g);
                                    let new_selector = SelectorDec(s.0, new_sort);  // (pair (first Color) (second Color))
                                    new_selectors.push(new_selector);

                                    variables_of(&s.1, &variable_set, &mut variables_found);
                                }
                                let new_c = ConstructorDec(c.0.clone(), new_selectors);
                                new_constructors.push(new_c);

                                let qualified = if variables_found.len() != var_count {
                                        // constructor is potentially ambiguous
                                        // -> use a qualified identifier
                                        QualIdentifier::new(&c.0, Some(sort.clone()))
                                    } else {
                                        QualIdentifier::new(&c.0, None)
                                    };
                                qualify.insert(c.0.clone(), qualified);
                            }

                            // add the declaration to the solver
                            let new_decl = DatatypeDec::DatatypeDec(new_constructors);
                            insert_sort(sort.clone(), grounding, Some((new_decl, qualify)), solver)
                        },
                          PolymorphicObject::Datatype(DatatypeDec::DatatypeDec(_))
                        | PolymorphicObject::RecursiveDT(DatatypeDec::DatatypeDec(_))=> {
                            Err(InternalError(1786496))  // Unexpected non-parametric type
                        },
                        PolymorphicObject::SortDefinition{variables, definiendum, } => {
                            // running example: parent_sort is (MyPair Color Color)
                            // parent_decl: (define-sort MyPair (T) (Pair T T))

                            // substitute to get new sort
                            let subs = sort_mapping(&variables, parameters); // T->Color
                            let (new_g, new_sort) = substitute_in_sort(&definiendum, &subs, declaring, solver)?; // (Pair Color Color)

                            // get the name of the table
                            let canonical = solver.canonical_sorts.get(&new_sort)
                                .ok_or(InternalError(78429656))?;
                            let sort_object = solver.sort_objects.get(canonical)
                                .ok_or(InternalError(7842966))?;

                            // create sort object
                            insert_alias(sort.clone(), new_g, canonical.clone(), sort_object.clone(), solver)
                        }
                        PolymorphicObject::Unknown => {
                            insert_sort(sort.clone(), TypeInterpretation::Unknown, None, solver)
                        }
                    }
                } else {  // indexed identifier
                    insert_sort(sort.clone(), TypeInterpretation::Unknown, None, solver)
                }
            },
        }}
}


/// Creates a mapping from Sort-variables to Sort
///
/// # Arguments
///
/// * variables: list of variables representing a sort
/// * values: list of monomorphic sorts
///
fn sort_mapping(
    variables: &Vec<Symbol>,
    values: &Vec<Sort>
) -> IndexMap<Sort, Sort> {

    let old_variables: Vec<Sort> = variables.iter()
        .map(|s| { Sort::new(s) })
        .collect();
    old_variables.into_iter()
        .zip(values.iter().cloned())
        .collect()
}


/// Converts a polymorphic sort to a monomorphic sort.
fn substitute_in_sort(
    sort: &Sort,
    subs: &IndexMap<Sort, Sort>,
    declaring: &IndexSet<Sort>,
    solver: &mut Solver,
) -> Result<(TypeInterpretation, Sort), SolverError> {

    match sort {

        Sort::Sort(_) => {
            // substitute if in the substitution map
            let new_sort = subs.get(sort).unwrap_or(sort).clone();
            let new_g = instantiate_sort(&new_sort, declaring, solver)?;
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
            let new_g = instantiate_sort(&new_sort, declaring, solver)?;
            Ok((new_g, new_sort))
        }
    }
}


///////////////////////  insert sort  /////////////////////////////////////////


/// Make the monomorphic sort known to the solver, and create its table
///
/// # Arguments:
///
/// * decl: only when `grounding` is TypeInterpretation::Normal
///
fn insert_sort(
    sort: Sort,
    grounding: TypeInterpretation,
    decl: Option<(DatatypeDec, IndexMap<Symbol, QualIdentifier>)>,
    solver: &mut Solver,
) -> Result<TypeInterpretation, SolverError> {

    if ! solver.canonical_sorts.contains_key(&sort) { // a new sort

        let (canonical, sort_object) =
            match grounding {
                TypeInterpretation::Unknown => (CanonicalSort(sort.clone()), SortObject::Unknown),
                TypeInterpretation::Infinite => (CanonicalSort(sort.clone()), SortObject::Infinite),
                TypeInterpretation::Recursive => (CanonicalSort(sort.clone()), SortObject::Recursive),
                TypeInterpretation::Normal => {  // create table for the sort
                    match decl {
                        Some((DatatypeDec::DatatypeDec(ref constructor_decls), ref qualify)) => {
                            let datatype_dec = decl.clone().unwrap().0;  // can't fail
                            let i = solver.sort_objects.len();
                            let (table, canonical) =
                                match sort {
                                    Sort::Sort(L(Identifier::Simple(Symbol(ref name)), _)) =>
                                        (solver.create_table_name(name.to_string(), TableType::Sort),
                                        CanonicalSort(sort.clone())),
                                    Sort::Sort(_) =>
                                        (TableName(format!("Sort_{}", i)),
                                        CanonicalSort(sort.clone())),
                                    Sort::Parametric(ref id, ref sorts) => {
                                        let canonicals = sorts.iter()
                                            .map(|s|
                                                solver.canonical_sorts.get(s)
                                                    .cloned()
                                                    .ok_or(SolverError::ExprError("unknown sort".to_string())))
                                            .collect::<Result<Vec<_>,_>>()?
                                            .into_iter()  // decanonicalize them
                                            .map(|canonical| canonical.0)
                                            .collect();

                                        (TableName(format!("Sort_{}", i)),
                                        CanonicalSort(Sort::Parametric(id.clone(), canonicals)))
                                    }
                                };
                            let row_count = create_table(&table, &canonical, &constructor_decls, qualify, solver)?;
                            (canonical, SortObject::Normal{datatype_dec, table, row_count})
                        }
                        Some((DatatypeDec::Par(..), _)) => {
                            return Err(InternalError(8458555))
                        }
                        None => unreachable!()
                    }
                },
            };
        solver.canonical_sorts.insert(sort, canonical.clone());
        solver.sort_objects.insert(canonical, sort_object);
    }

    Ok(grounding)
}


/// Make the monomorphic sort known to the solver, and create its table
fn insert_alias(
    sort: Sort,
    grounding: TypeInterpretation,
    canonical: CanonicalSort,
    sort_object: SortObject,
    solver: &mut Solver,
) -> Result<TypeInterpretation, SolverError> {

    if ! solver.canonical_sorts.contains_key(&sort) { // a new sort
        solver.canonical_sorts.insert(sort, canonical.clone());
        solver.sort_objects.insert(canonical, sort_object);
    }

    Ok(grounding)
}


fn create_table(
    table: &TableName,
    canonical_sort: &CanonicalSort,
    constructor_decls: &Vec<ConstructorDec>,
    qualify: &IndexMap<Symbol, QualIdentifier>,
    solver: &mut Solver
) -> Result<usize, SolverError> {

    let mut row_count;

    // running example: (declare-datatype P ((white ) (pair (first Color) (second Color))))

    // LINK src/doc.md#_Constructor
    // 1st pass: collect nullary constructors and selectors
    // in ((white ) (pair (first Color) (second Color)))
    let mut nullary = vec![]; // white
    let mut column_names: IndexMap<String, String> = IndexMap::new();  // first: Text, second: Int
    for constructor_decl in constructor_decls {
        let ConstructorDec(constructor, selectors) = constructor_decl;
        if selectors.len() == 0 {
            let mut code = qualify.get(constructor)
                .ok_or(InternalError(1785965))?
                .to_string();
            if code.starts_with("(") {
                code = format!(" {code}")  // ` (as nil T)` is a constructor (with leading space)
            }
            nullary.push((constructor.clone(), code));
        } else {
            for SelectorDec(selector, sort) in selectors {
                // LINK src/doc.md#_Infinite
                let type_ = match sort.to_string().as_str() {
                    "Int" => "INTEGER",
                    "Real" => "REAL",
                    _ => "TEXT"
                };
                column_names.insert(selector.0.clone(), type_.to_string());
            }
        }

        // add constructor function to solver
        let domain = selectors.iter()
            .map(|SelectorDec(_, sort)|
                solver.canonical_sorts.get(sort)
                    .ok_or(InternalError(78845662)))
            .collect::<Result<Vec<_>,_>>()?
            .into_iter().cloned().collect();
        let identifier = Identifier::new(constructor);
        set_function_object(&identifier, &domain, &canonical_sort, FunctionObject::Constructor, solver)?;
    }
    row_count = nullary.len();

    if column_names.len() == 0 {  // nullary constructors only

        create_core_table(table, nullary, &mut solver.conn)?;

    } else {  // with constructors

        let mut selects: Vec<String> = vec![];

        if 0 < nullary.len() {
            let core = TableName(format!("{table}_core"));
            create_core_table(&core, nullary, &mut solver.conn)?;

            //  "NULL as first, NULL as second"
            let projection = column_names.iter().map(|(n, _)| format!("NULL AS {n}")).collect::<Vec<_>>().join(", ");

            // the first select is "SELECT "white" as constructor, NULL as first, NULL as second, Color_core.G as G from Color_core"
            selects.push(format!("SELECT {core}.constructor AS constructor, {projection}, {core}.G AS G FROM {core}"));
        }

        // LINK src/doc.md#_Constructor
        // add "select "pair" as constructor, T1.G as first, T2.G as second, construct("pair", T1.G, T2.G) as G
        //      from Color as T1 join Color as T2"
        for constructor_decl in constructor_decls { // e.g. (pair (first Color) (second Color))
            let ConstructorDec(constructor, selectors) = constructor_decl;

            if selectors.len() != 0 {  // otherwise, already in core table

                // compute the list of tables and column sort_mapping
                let mut tables = Vec::with_capacity(selectors.len()); // [Color, Color]
                let mut columns = IndexMap::with_capacity(column_names.len());  // {first->T1.G, second->T2.G}; the value can be NULL
                for (column_name, _) in &column_names {
                    columns.insert(column_name, "NULL".to_string());
                }
                let mut row_product = 1;
                for (i, SelectorDec(selector, sort)) in selectors.iter().enumerate() {
                    let canonical = solver.canonical_sorts.get(sort)
                        .ok_or(InternalError(74594855))?;
                    let sort_object = solver.sort_objects.get(canonical)
                        .ok_or(InternalError(7459455))?;
                    if let SortObject::Normal{table, row_count, ..} = sort_object {
                        tables.push(table.clone());
                        columns.insert(&selector.0, format!("T{i}.G"));
                        row_product *= row_count;
                    } else {
                        return Err(InternalError(7529545))
                    }
                }
                row_count += row_product;

                // "pair"
                let mut qualified = qualify.get(constructor)
                    .ok_or(InternalError(79443695256))?
                    .to_string();
                if qualified.starts_with("(") {
                    qualified = format!(" {qualified}")  // ` (as nil T)` is a constructor (with leading space)
                }

                // "T1.G AS first, T2.G as second"
                let projection = columns.iter()
                    .map(|(k, v)| format!("{v} AS {k}")) // v can also be NULL
                    .collect::<Vec<String>>().join(", ");

                // "T1.G, T2.G"
                let parameters = (0..selectors.len()).map(|i| format!("T{i}.G")).collect::<Vec<_>>().join(", ");
                // construct("pair", T1.G, T2.G) AS G
                let g = format!("construct(\"{qualified}\", {parameters}) AS G");

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
        let insert = format!("INSERT INTO {table} (constructor, {columns}, G) {}", selects.join( " UNION ALL "));
        solver.conn.execute(&insert, ())?;
    }

    // add tester function in solver
    for constructor_decl in constructor_decls { // e.g. (pair (first Color) (second Color))
        let ConstructorDec(constructor, selectors) = constructor_decl;

        { // tester: (_ is pair)
        let identifier = L(Identifier::Indexed(Symbol("is".to_string()), vec![Index::Symbol(constructor.clone())]), Offset(0));

        let view_g = solver.create_table_name(format!("{table}_{constructor}_G"), TableType::Tester);
        let sql = format!(r#"
            CREATE VIEW {view_g} AS
            SELECT G AS a_1,
                   CASE constructor WHEN "{constructor}" THEN "true" ELSE "false" END AS G
              FROM {table}"#);
        solver.conn.execute(&sql, ())?;

        let table_g = Interpretation::Table { name: view_g.clone(), ids: Ids::All };

        let view_t = solver.create_table_name(format!("{table}_{constructor}_T"), TableType::Tester);
        let sql = format!("CREATE VIEW {view_t} AS SELECT * FROM {view_g} WHERE G = \"true\"");
        solver.conn.execute(&sql, ())?;
        let table_tu = Interpretation::Table { name: view_t, ids: Ids::All };

        let view_f = solver.create_table_name(format!("{table}_{constructor}_F"), TableType::Tester);
        let sql = format!("CREATE VIEW {view_f} AS SELECT * FROM {view_g} WHERE G = \"false\"");
        solver.conn.execute(&sql, ())?;
        let table_uf = Interpretation::Table { name: view_f, ids: Ids::All };

        let function = FunctionObject::BooleanInterpreted{table_g, table_tu, table_uf};
        let bool_sort = CanonicalSort(Sort::new(&Symbol("Bool".to_string())));
        set_function_object(&identifier, &vec![canonical_sort.clone()], &bool_sort, function, solver)?;
        }
        { // selectors: first P->Color, second P->Color
        let canonicals = selectors.iter()
            .map( |SelectorDec(_, sort)|
                solver.canonical_sorts.get(sort)
                .ok_or(InternalError(84552662)))
            .collect::<Result<Vec<_>,_>>()?
            .into_iter().cloned().collect::<Vec<_>>();
        for (SelectorDec(selector, _), canonical) in selectors.iter().zip(canonicals.iter()) {
            let identifier = Identifier::new(selector);
            let view_g = solver.create_table_name(format!("{table}_{selector}_G"), TableType::Selector);
            let sql = format!(r#"
                CREATE VIEW {view_g} AS
                SELECT G AS a_1,
                      {selector} AS G
                  FROM {table}"#);
            solver.conn.execute(&sql, ())?;

            let table_g = Interpretation::Table { name: view_g, ids: Ids::All };
            let function = FunctionObject::Interpreted(table_g);
            set_function_object(&identifier, &vec![canonical_sort.clone()], canonical, function, solver)?;
        }
        }
    }
    Ok(row_count)
}


/// creates a table in the DB containing the nullary constructors
fn create_core_table(
    table: &TableName,
    values: Vec<(Symbol, String)>,
    conn: &mut Connection
) -> Result<(), SolverError> {

    conn.execute(&format!("CREATE TABLE {table} (constructor, G TEXT TEXT PRIMARY KEY)"), ())?;

    let mut stmt = conn.prepare(&format!("INSERT INTO {table} (constructor, G) VALUES (?, ?)"))?;
    for (symbol, code) in values {
        stmt.execute(params![symbol.to_string(), code])?;
    }
    Ok(())
}

/// Determines the variables in a sort.
/// This is useful to determine if a constructor may be ambiguous.
///
/// # Arguments:
///
/// * variables: the variables in the scope
/// * result: accumulator of the variables found
///
fn variables_of(
    sort: &Sort,
    variables: &IndexSet<Symbol>,
    result: &mut IndexSet<Symbol>
) -> () {
    match sort {
        Sort::Sort(L(Identifier::Simple(id), _))
        | Sort::Sort(L(Identifier::Indexed(id, _), _)) => {
            if variables.contains(id) {
                result.insert(id.clone());
            }
        },
        Sort::Parametric(L(Identifier::Simple(_), _), sorts)
        | Sort::Parametric(L(Identifier::Indexed(_, _), _), sorts) => {
            for sort in sorts {
                variables_of(sort, variables, result)
            }
        },
    }
}


pub(crate) fn get_sort_object<'a>(sort: &'a Sort, solver: &'a Solver) -> Option<&'a SortObject> {
    match solver.canonical_sorts.get(sort) {
        Some(canonical) => solver.sort_objects.get(canonical),
        None => None
    }
}


fn set_function_object(
    identifier: &L<Identifier>,
    domain: &Vec<CanonicalSort>,
    co_domain: &CanonicalSort,
    function_object: FunctionObject,
    solver: &mut Solver
) -> Result<(), SolverError> {

    let key = (identifier.clone(), domain.clone());
    match solver.function_objects.get_mut(&key) {
        Some(map) => {
            if ! map.contains_key(co_domain) {
                map.insert(co_domain.clone(), function_object);
            } else {
                return Err(SolverError::IdentifierError("Duplicate function declaration", identifier.clone()));
            }
        }
        None => {
            solver.function_objects.insert(key, IndexMap::from([(co_domain.clone(), function_object)]));
        }
    }
    Ok(())
}