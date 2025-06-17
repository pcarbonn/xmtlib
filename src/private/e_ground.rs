// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use rusqlite::Connection;

use crate::ast::{Identifier, QualIdentifier, Sort, Symbol, Term, L};
use crate::error::{Offset, SolverError::{self, *}};
use crate::solver::{CanonicalSort, Solver};

use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, get_function_object, Interpretation};
use crate::private::e1_ground_view::{view_for_aggregate, view_for_join, view_for_constant, view_for_union, view_for_variable, GroundingView, Ids, QueryVariant, ViewType};
use crate::private::e2_ground_query::{TableName, TableAlias};
use crate::private::e3_ground_sql::Predefined;


/////////////////////  Data structure for Grounding  //////////////////////////


#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Grounding {
    NonBoolean(GroundingView),
    Boolean{tu: GroundingView, uf: GroundingView, g: GroundingView}
}
impl std::fmt::Display for Grounding {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Grounding::NonBoolean(query) => write!(f, " {query}"),
            Grounding::Boolean{tu, uf, g, ..} => {
                if tu.get_ids() == Ids::All {
                    writeln!(f, "----- T ------------------------------------------------------------\n{tu}")?;
                } else {
                    writeln!(f, "----- TU -----------------------------------------------------------\n{tu}")?;
                }
                if uf.get_ids() == Ids::All {
                    writeln!(f, "----- F ------------------------------------------------------------\n{uf}")?;
                } else {
                    writeln!(f, "----- UF -----------------------------------------------------------\n{uf}")?;
                }
                writeln!  (f,   "----- G ------------------------------------------------------------\n{g}")
            },
        }
    }
}


/// Determine if a term uses a function that is interpreted in the solver.
///
/// Arguments:
///
/// * grounded: returned list of uninterpreted symbols occurring in the term
///
fn has_interpreted_function(
    term: &L<Term>,
    not_interpreted: &mut Vec<Identifier>,
    solver: &mut Solver
) -> Result<(CanonicalSort, bool), SolverError> {

    /// returns true if the function is interpreted.
    /// Add it to not_interpreted if not interpreted.
    fn analyze_function(
        function: &QualIdentifier,
        function_object: &FunctionObject,
        not_interpreted: &mut Vec<Identifier>
    ) -> Result<bool, SolverError> {
        match function_object {
            FunctionObject::Predefined { .. }
            | FunctionObject::Constructor => Ok(false),

            FunctionObject::NotInterpreted => {
                if let QualIdentifier::Identifier(L(function, _)) = function {
                    not_interpreted.push(function.clone());
                    Ok(false)
                } else {
                    return Err(SolverError::InternalError(6875596))
                }
            },

            FunctionObject::Interpreted(_)
            | FunctionObject::BooleanInterpreted { .. } => {
                Ok(true)
            },
        }
    }

    let L(term_, _) = term;
    match term_ {
        Term::SpecConstant(spec_constant) => Ok( (spec_constant.to_canonical_sort(), false) ),

        Term::Identifier(function) => {
            let (sort, function_object) =  get_function_object(term, function, &vec![], &solver)?;
            let sort = sort.clone();
            let interpreted = analyze_function(function, function_object, not_interpreted)?;
            Ok( (sort, interpreted) )
        },
        Term::Application(function, ls) => {
            let (sorts, interpreteds): (Vec<_>, Vec<_>) = ls.iter()
                            .map( |term| has_interpreted_function(term, not_interpreted, solver))
                            .collect::<Result<Vec<(_,_)>,_>>()?
                            .into_iter().unzip();
            let (sort, function_object) =  get_function_object(term, function, &sorts, &solver)?;
            let sort = sort.clone();
            let interpreted = interpreteds.iter().any(|b| *b)
                || analyze_function(function, function_object, not_interpreted)?;
            Ok( (sort, interpreted) )
        },
        Term::Let(_, l) => has_interpreted_function(l, not_interpreted, solver),
        Term::Forall(_, l) => has_interpreted_function(l, not_interpreted, solver),
        Term::Exists(_, l) => has_interpreted_function(l, not_interpreted, solver),
        Term::Match(l, _) => has_interpreted_function(l, not_interpreted, solver), // TODO
        Term::Annotation(l, _) => has_interpreted_function(l, not_interpreted, solver),
        Term::XSortedVar(_, sort, _) => {
            let canonical = solver.canonical_sorts.get(sort)
                .ok_or(InternalError(1458856))?
                .clone();
            Ok( (canonical, false) )
        },
        Term::XLetVar(_, l) => has_interpreted_function(l, not_interpreted, solver),
    }
}


/////////////////////  Command (x-ground //////////////////////////////////////

/// ground the pending assertions
pub(crate) fn ground(
    no: bool,
    debug: bool,
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        // update statistics in DB
        solver.conn.execute("ANALYZE", []).unwrap();

        let mut terms = vec![];  // for concatenation
        let mut grounded = vec![];
        for term in solver.assertions_to_ground.clone() {
            if no {
                let assert = format!("(assert {term})\n");
                yield_!(solver.exec(&assert));
            } else {
                match has_interpreted_function(&term, &mut grounded, solver) {
                    Ok( (_, has) ) => {
                        if ! has && ! debug {  // no interpretation
                            let assert = format!("(assert {})\n", &term);
                            yield_!(solver.exec(&assert));
                        } else if debug {  // execute immediately
                            for result in execute_term(term, solver) {
                                yield_!(result)
                            }
                        } else {  // conjoin with other terms
                            terms.push(term.clone())
                        }
                    }
                    Err(e) => yield_!(Err(e))
                }
            }
        }
        for identifier in grounded.into_iter() {
            solver.grounded.insert(identifier);
        }

        // faster, because it gives sqlite more scope for optimisation
        if 0 < terms.len() {
            let and_ = QualIdentifier::new(&Symbol("and".to_string()), None);
            let term = L(Term::Application(and_, terms), Offset(0));

            for result in execute_term(term, solver) {
                yield_!(result)
            }
        }

        // reset terms to ground
        solver.assertions_to_ground = vec![];
    })
}


fn execute_term(
    term: L<Term>,
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        match ground_term(&term, true, solver) {
            Ok((g, _)) => {
                match g {
                    Grounding::NonBoolean(_) => yield_!(Err(SolverError::TermError("Expecting a boolean", term.clone()))),
                    Grounding::Boolean{uf, ..} => {
                        // execute the UF query
                        let query = uf.to_string();
                        for res in execute_query(query, &mut solver.conn) {
                            yield_!(res)
                        }
                    }
                }
            },
            Err(e) => yield_!(Err(e))
        }
    })
}

fn execute_query(
    query: String,
    conn: &mut Connection
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {
    gen!({
        let mut stmt = match conn.prepare(&query) {
            Ok(stmt) => stmt,
            Err(e) => {
                yield_!(Err(SolverError::from(e)));
                return;
            }
        };
        if stmt.column_count() == 1 {  //  just G
            match stmt.query_map([], |row| {
                        row.get::<usize, String>(0)
                    }) {
                Ok(row_iter) => {
                    for row in row_iter {
                        match row {
                            Ok(g) => {
                                if g != "true" {
                                    let assert = format!("(assert {g})\n");
                                    yield_!(Ok(assert));
                                    if g == "false" {  // theory is unsatisfiable anyway
                                        break
                                    }
                                }
                            }
                            Err(e) => yield_!(Err(SolverError::from(e)))
                        }
                    }
                }
                Err(e) => yield_!(Err(SolverError::from(e)))
            };
        } else if stmt.column_count() == 2 {  // with an if_ column
            match stmt.query_map([], |row| {
                        row.get::<usize, String>(0).and_then(|col0| {
                            row.get::<usize, String>(1).map(|col1| (col0, col1))
                        })
                    }) {
                Ok(row_iter) => {
                    for row in row_iter {
                        match row {
                            Ok((if_, g)) => {
                                if if_ == "" || if_ == "true" {
                                    if g != "true" {
                                        let assert = format!("(assert {g})\n");
                                        yield_!(Ok(assert));
                                        if g == "false" {  // theory is unsatisfiable anyway
                                            break
                                        }
                                    }
                                } else {
                                    let assert = format!("(assert (=> {if_} {g}))\n");
                                    yield_!(Ok(assert));
                                }
                            }
                            Err(e) => yield_!(Err(SolverError::from(e)))
                        }
                    }
                }
                Err(e) => yield_!(Err(SolverError::from(e)))
            };
        } else {
            unreachable!()
        }
    })
}


/// Adds the grounding of a term to the solver, if necessary.
/// This function is recursive.
///
/// # Arguments
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction
/// if the term is a universal quantification).
///
fn ground_term(
    term: &L<Term>,
    top_level: bool,
    solver: &mut Solver
) -> Result<(Grounding, CanonicalSort), SolverError> {

    if let Some(grounding) = solver.groundings.get(&(term.clone(), top_level)) {
        Ok(grounding.clone())
    } else {
        let grounding = ground_term_(term, top_level, solver)?;
        solver.groundings.insert((term.clone(), top_level), grounding.clone());
        Ok(grounding)
    }
}

/// Helper function to ground a new term.
///
/// # Arguments:
///
/// * top_level: indicates if it is an assertion (to avoid building a conjunction)
///
pub(crate) fn ground_term_(
    term: &L<Term>,
    top_level: bool,
    solver: &mut Solver
) -> Result<(Grounding, CanonicalSort), SolverError> {

    match term {
        L(Term::SpecConstant(spec_constant), _) => {

            // a number or string; cannot be Boolean
            let grounding = view_for_constant(spec_constant)?;
            let canonical = spec_constant.to_canonical_sort();
            Ok((Grounding::NonBoolean(grounding), canonical))
        },
        L(Term::XSortedVar(symbol, sort, sorted_object), _) => {

            // a regular variable
            let base_table =
                match sorted_object {
                    SortObject::Normal{table, ..} => Some(table.clone()),
                    SortObject::Recursive
                    | SortObject::Infinite
                    | SortObject::Unknown => None,
                };

            let index = solver.groundings.len();
            let g = view_for_variable(symbol, base_table, index)?;

            let canonical = solver.canonical_sorts.get(sort)
                .ok_or(InternalError(1458856))?
                .clone();
            if sort.to_string() == "bool" {
                Ok((Grounding::Boolean { tu: g.clone(), uf: g.clone(), g }, canonical))
            } else {
                Ok((Grounding::NonBoolean(g), canonical))
            }
        },
        L(Term::XLetVar(_, _), _) => {
            todo!()
        }
        L(Term::Identifier(qual_identifier), _) => {

            // an identifier
            ground_compound(term, qual_identifier, &mut vec![], false, solver)
        },
        L(Term::Application(qual_identifier, sub_terms), _) => {

            // a compound term
            ground_compound(term, qual_identifier, sub_terms, top_level, solver)
        },
        L(Term::Let(..), _) => todo!(),
        L(Term::Forall(variables, term), _) => {
            match ground_term(term, false, solver)? {
                (Grounding::NonBoolean(_), _) =>
                    Err(InternalError(42578548)),
                (Grounding::Boolean { tu: _, uf: sub_uf, g: _ }, canonical) => {

                    let index = solver.groundings.len();
                    let table_name = TableName(format!("Agg_{index}"));

                    let (free_variables, infinite_variables) = sub_uf.get_free_variables(variables).clone();

                    let tu = view_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &infinite_variables,
                        "and",
                        Some(true),
                        Some(false),
                        true,
                        TableAlias{base_table: TableName(format!("{table_name}_TU")), index: 0})?;

                    let uf = view_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &infinite_variables,
                        if top_level { "" } else { "and" },
                        None,
                        None,
                        false,
                        TableAlias{base_table: TableName(format!("{table_name}_UF")), index: 0})?;

                    let g = view_for_aggregate(
                        &sub_uf,
                        &free_variables,
                        &infinite_variables,
                        "and",
                        Some(true),
                        None,
                        true,
                        TableAlias{base_table: TableName(format!("{table_name}_G")), index: 0})?;

                    Ok((Grounding::Boolean{tu, uf, g}, canonical))
                },
            }
        },
        L(Term::Exists(variables, term), _) => {
            match ground_term(term, false, solver)? {
                (Grounding::NonBoolean(_), _) =>
                    Err(InternalError(42578548)),
                (Grounding::Boolean { tu: sub_tu, uf: _, g: _ }, canonical) => {

                    let index = solver.groundings.len();
                    let table_name = TableName(format!("Agg_{index}"));

                    let (free_variables, infinite_variables) = sub_tu.get_free_variables(variables).clone();

                    let tu = view_for_aggregate(
                        &sub_tu,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        None,
                        None,
                        false,
                        TableAlias{base_table: TableName(format!("{table_name}_TU")), index: 0})?;

                    let uf = view_for_aggregate(
                        &sub_tu,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        Some(false),
                        Some(true),
                        true,
                        TableAlias{base_table: TableName(format!("{table_name}_UF")), index: 0})?;

                    let g = view_for_aggregate(
                        &sub_tu,
                        &free_variables,
                        &infinite_variables,
                        "or",
                        Some(false),
                        None,
                        true,
                        TableAlias{base_table: TableName(format!("{table_name}_G")), index: 0})?;
                    Ok((Grounding::Boolean{tu, uf, g}, canonical))
                },
            }
        },
        L(Term::Match(..), _) => todo!(),
        L(Term::Annotation(..), _) => todo!(),
    }
}

// Grounds a compound term
fn ground_compound(
    term: &L<Term>,
    qual_identifier: &QualIdentifier,
    sub_terms: &Vec<L<Term>>,
    top_level: bool,
    solver: &mut Solver
) -> Result<(Grounding, CanonicalSort), SolverError> {

    let top_level = if qual_identifier.to_string() == "and" {
            top_level
        } else {
            false
        };

    // ground sub_terms, creating an entry in solver.groundings if necessary
    let (groundings, sorts): (Vec<Grounding>, Vec<CanonicalSort>) =
        sub_terms.iter()
            .map( |t| ground_term(t, top_level, solver))
            .collect::<Result<Vec<(Grounding, CanonicalSort)>,_>>()?
            .into_iter()
            .unzip();

    let index = solver.groundings.len();

    // collect the full grounding queries
    let mut gqs = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(gq) => gq.clone(),
                Grounding::Boolean{g: gq, ..} => gq.clone()
            })
        .collect::<Vec<_>>();

    let (out_sort, function_is) = get_function_object(term, qual_identifier, &sorts, solver)?;
    let out_sort = out_sort.clone();

    match function_is {
        FunctionObject::Predefined { boolean: None, .. } => { // ite
            match qual_identifier.to_string().as_str() {
                "ite" => {
                    if sub_terms.len() != 3 {
                        return Err(SolverError::TermError("Incorrect number of arguments", term.clone()))
                    }
                    let variant = QueryVariant::Predefined(Predefined::Ite);
                    if let Grounding::Boolean{g: ifg, ..} = groundings[0].clone() {
                        match (groundings[1].clone(), groundings[2].clone()) {
                            ( Grounding::NonBoolean(lg),
                              Grounding::NonBoolean(rg)) => {
                                let mut sub_queries = vec![ifg, lg, rg];
                                let g = view_for_join(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                Ok((Grounding::NonBoolean( g ), sorts[1].clone()))
                            },
                            ( Grounding::Boolean{tu: ltu, uf: luf, g: lg, ..},
                              Grounding::Boolean{tu: rtu, uf: ruf, g: rg, ..}) => {

                                let mut sub_queries = vec![ifg.clone(), ltu, rtu];
                                let tu = view_for_join(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                let mut sub_queries = vec![ifg.clone(), luf, ruf];
                                let uf = view_for_join(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                let mut sub_queries = vec![ifg, lg, rg];
                                let g = view_for_join(qual_identifier, index, &mut sub_queries, &variant, None, solver)?;

                                Ok((Grounding::Boolean{tu, uf, g}, sorts[1].clone()))
                            },
                            _ => return Err(SolverError::TermError("Incorrect type of arguments", term.clone()))
                        }
                    } else {
                        return Err(SolverError::TermError("Incorrect type of arguments", term.clone()))
                    }
                }
                _ => Err(InternalError(3884562))
            }
        },
        FunctionObject::Predefined {function, boolean: Some(boolean), .. } => {
            let variant = QueryVariant::Predefined(function.clone());
            if *boolean {
                let (tus, mut ufs) = collect_tu_uf(&groundings);

                match function {
                    Predefined::And => {

                        let mut collapsed = tus.iter().enumerate()
                            .map(|(index, tu)| {
                                if ! tu.has_condition() {
                                    Ok(tu.clone())
                                } else {
                                    let table_name = TableName(format!("Agg_{index}"));
                                    let table_alias = TableAlias{base_table: TableName(format!("{table_name}")), index: 0};
                                    let (free_variables, _) = tu.get_free_variables(&vec![]).clone();
                                    view_for_aggregate(tu, &free_variables, &vec![], "or", None, None, false, table_alias)
                                }
                            }).collect::<Result<Vec<_>,_>>()?;

                        let tu = view_for_join(qual_identifier, index, &mut collapsed, &variant, Some(false), solver)?;

                        let agg = if top_level { "" } else { "and" };
                        let uf = view_for_union(ufs, Some(true), agg.to_string(), index)?;

                        let g = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok((Grounding::Boolean{tu, uf, g}, out_sort))
                    }
                    Predefined::Or => {
                        let tu = view_for_union(tus, Some(false), "or".to_string(), index)?;

                        let mut collapsed = ufs.iter().enumerate()
                            .map(|(index, uf)| {
                                if ! uf.has_condition() {
                                    Ok(uf.clone())
                                } else {
                                    let table_name = TableName(format!("Agg_{index}"));
                                    let table_alias = TableAlias{base_table: TableName(format!("{table_name}")), index: 0};
                                    let (free_variables, _) = uf.get_free_variables(&vec![]).clone();
                                    view_for_aggregate(uf, &free_variables, &vec![], "and", None, None, false, table_alias)
                                }
                            }).collect::<Result<Vec<_>,_>>()?;

                        let uf = view_for_join(qual_identifier,  index, &mut collapsed, &variant, Some(true), solver)?;

                        let g = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok((Grounding::Boolean{tu, uf, g}, out_sort))

                    }
                    Predefined::Not => {
                        // return uf, tu, g with grounding G replaced by not(G)
                        match groundings.get(0) {
                            Some(Grounding::Boolean { tu, uf, g }) => {
                                if let GroundingView::View { .. } = g {
                                    // switch uf and tu and negate the groundings
                                    let new_tu = uf.negate(index, ViewType::UF, solver)?;
                                    let new_uf = tu.negate(index, ViewType::TU, solver)?;
                                    let new_g = g.negate(index, ViewType::G, solver)?;

                                    Ok((Grounding::Boolean{tu: new_tu, uf: new_uf, g: new_g}, out_sort))
                                } else {  // empty
                                    Ok((Grounding::Boolean{tu: GroundingView::Empty, uf:  GroundingView::Empty, g:  GroundingView::Empty}, out_sort))
                                }
                            },
                            Some(Grounding::NonBoolean(_))
                            | None => Err(SolverError::TermError("not a boolean term", term.clone()))
                        }
                    }
                    Predefined::Eq
                    | Predefined::BoolEq(_) => {
                        // LINK src/doc.md#_Equality
                        let tu = view_for_join(qual_identifier, index, &mut gqs, &variant, Some(false), solver)?;

                        let uf = match groundings.get(0) {
                            Some(Grounding::Boolean { .. }) => {
                                if 2 < gqs.len() {
                                    return Err(SolverError::TermError("Too many boolean arguments", term.clone()))  //TODO relax constraint
                                }
                                let use_g = ufs.iter()
                                    .all(|g| g.has_g_complexity());

                                if use_g {
                                    view_for_join(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?
                                } else {
                                    let variant = QueryVariant::Equivalence(true);
                                    view_for_join(qual_identifier, index, &mut ufs, &variant, None, solver)?
                                }
                            },
                            Some(Grounding::NonBoolean { .. }) => {
                                view_for_join(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?
                            },
                            None => return Err(SolverError::TermError("missing arguments", term.clone())),
                        };

                        let g = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok((Grounding::Boolean{tu, uf, g}, out_sort))
                    }
                    Predefined::Is(_)
                    | Predefined::Less
                    | Predefined::LE
                    | Predefined::Greater
                    | Predefined::GE
                    | Predefined::Distinct => {
                        let tu = view_for_join(qual_identifier, index, &mut gqs, &variant, Some(false), solver)?;

                        let uf = view_for_join(qual_identifier, index, &mut gqs, &variant, Some(true), solver)?;

                        let g = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;

                        Ok((Grounding::Boolean{tu, uf, g}, out_sort))
                    }
                    _ => Err(InternalError(58994512))
                }
            } else {  // predefined non-boolean function
                match function {
                    Predefined::Plus
                    | Predefined::Minus
                    | Predefined::Times
                    | Predefined::Div
                    | Predefined::Mod
                    | Predefined::Abs => {
                        let g = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                        let sort = if sorts.iter().any(|s| s.to_string() == "Real") {
                            CanonicalSort(Sort::new(&Symbol("Real".to_string())))
                        } else {
                            CanonicalSort(Sort::new(&Symbol("Int".to_string())))
                        };

                        Ok((Grounding::NonBoolean( g ), sort))
                    }
                    _ => Err(InternalError(48519624))
                }
            }
        },
        FunctionObject::Constructor => {
            // LINK src/doc.md#_Constructor
            let variant = QueryVariant::Construct;
            if qual_identifier.to_string() == "true"
            || qual_identifier.to_string() == "false" {  // boolean
                let tu = view_for_join(qual_identifier, index, &mut vec![], &variant, Some(false), solver)?;
                let uf = view_for_join(qual_identifier, index, &mut vec![], &variant, Some(true), solver)?;
                let g = view_for_join(qual_identifier, index, &mut vec![], &variant, None, solver)?;
                Ok((Grounding::Boolean{tu, uf, g}, out_sort))
            } else {
                let grounding_query = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                Ok((Grounding::NonBoolean(grounding_query), out_sort))
            }
        },
        FunctionObject::NotInterpreted => { // custom function
            let variant = QueryVariant::Apply;
            if out_sort.to_string() == "Bool" {

                // custom boolean function
                let (mut tus, mut ufs) = collect_tu_uf(&groundings);
                let  g = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                let tu = view_for_join(qual_identifier, index, &mut tus, &variant, None, solver)?;
                let uf = view_for_join(qual_identifier, index, &mut ufs, &variant, None, solver)?;

                Ok((Grounding::Boolean{tu, uf, g}, out_sort))
            } else {

                // custom non-boolean function
                let grounding_query = view_for_join(qual_identifier, index, &mut gqs, &variant, None, solver)?;
                Ok((Grounding::NonBoolean(grounding_query), out_sort))
            }
        },
        FunctionObject::BooleanInterpreted { table_tu, table_uf, table_g } => {
            let (tus, ufs) = collect_tu_uf(&groundings);

            let mut new_queries = vec![];

            for ((table, groundings), view_type)
            in [table_tu.clone(), table_uf.clone(), table_g.clone()].iter()
                .zip([tus, ufs, gqs.to_vec()])
                .zip([ViewType::TU, ViewType::UF, ViewType::G]) {

                let exclude = match view_type {
                    ViewType::TU => Some(false),
                    ViewType::UF => Some(true),
                    ViewType::G  => None
                };
                let variant = match table {
                    Interpretation::Table{name, ids} => {
                        let table_name = TableAlias::new(name.clone(), index);
                        QueryVariant::Interpretation(table_name, ids.clone())
                    },
                    Interpretation::Infinite => QueryVariant::Apply
                };
                let new_view = view_for_join(qual_identifier, index, &groundings, &variant, exclude, solver)?;
                new_queries.push(new_view);
            };

            Ok((Grounding::Boolean{tu: new_queries[0].clone(), uf: new_queries[1].clone(), g: new_queries[2].clone()},
                out_sort))
        },
        FunctionObject::Interpreted(table_g) => {
            let variant = match table_g {
                Interpretation::Table{name, ids} => {
                    let table_name = TableAlias::new(name.clone(), index);
                    QueryVariant::Interpretation(table_name, ids.clone())
                },
                Interpretation::Infinite => QueryVariant::Apply
            };
            let new_view = view_for_join(qual_identifier, index, &gqs, &variant, None, solver)?;
            Ok((Grounding::NonBoolean(new_view), out_sort))
        }
    }
}


/// Collect the TU (resp. UF) grounding queries in the vector of groundings
fn collect_tu_uf(
    groundings: &Vec<Grounding>
) -> (Vec<GroundingView>, Vec<GroundingView>) {

    // collect the TU grounding queries
    let tus = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(q) => q.clone(),
                Grounding::Boolean{tu: q, ..} => q.clone()
            })
        .collect::<Vec<_>>();

    // collect the UF grounding queries
    let ufs = groundings.iter()
        .map( |g|
            match g {
                Grounding::NonBoolean(q) => q.clone(),
                Grounding::Boolean{uf: q, ..} => q.clone()
            })
        .collect::<Vec<_>>();

    (tus, ufs)
}

