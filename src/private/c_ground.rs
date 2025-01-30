// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;

use crate::api::{Identifier, QualIdentifier, SortedVar, Symbol, Term};
use crate::private::a_sort::SortObject;
use crate::private::b_fun::{FunctionObject, InterpretationType};
use crate::solver::Solver;
use crate::error::SolverError::{self, *};


/// Contains what is needed to construct the grounding view of a term, in a composable way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct View {
    // for variable x in Color --> select color.G as x, color.G as G from Color
    //      variables:  `x -> Color.G`, i.e., variable name to column name
    //      condition:  ""
    //      grounding:  "Color.G"
    //      joins:      Color
    //      where:      ""
    //      group_by:   ""
    //      _ids:    true

    // For a calculated term p
    // e.g., p(x, f(a)) --> select color.G as x, apply("p", Color.G, apply("f", "a")) as G from Color
    //      variables:  `x -> Color.G`, i.e., variable name to column name
    //      condition:  ""
    //      grounding:  apply("p", Color.G, apply("f", "a"))
    //      joins:      Color
    //      where:      ""
    //      group_by:   ""
    //      _ids:    false

    // for a tabled term: 2 options (create a view or not)
    // e.g., p(x, a) -->
    //      create view term_2 as
    //          select p.a1 as x,
    //                 .. as cond,
    //                 p.G as G
    //            from p
    //           where p.a2 = "a"
    //
    //      variables: `x -> p.a1`, i.e., variable name to column name
    //      condition: ""
    //      grounding: "p.G"
    //      joins: "p"
    //      where: "p.a2 = "a""
    //      view:

    variables: IndexMap<Symbol, String>,
    condition: String,
    grounding: String,
    joins: IndexMap<String, String>,
    where_: String,
    group_by: String,

    _ids: Ids,
}


#[derive(Debug, Clone, PartialEq, Eq)]
enum Ids { All, _Some, None }

impl std::fmt::Display for View {

    // select {variables.0} as {variables.1},
    //        {condition} as cond,  -- if condition
    //        {grounding} as G,
    //   from {joins[0].key}
    //   join {joins[i].key} on {joins[i].value}
    //  where {condition}
    // group by {variables.0}, {grounding}  -- if condition

    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let variables = self.variables.iter()
            .map(|(k, v)| format!("{v} AS {k}"))
            .collect::<Vec<_>>()
            .join(", ");
        let condition = if &self.condition == "" { "".to_string()
            } else if variables != "" {
                format!(", {0} as cond", &self.condition)
            } else {
                format!("{0} as cond", &self.condition)
            };
        let grounding = if variables != "" || condition != "" {
                format!(", {}", &self.grounding)
            } else {
                self.grounding.to_string()
            };
        let tables = self.joins.iter()
            .map(|(table, on)| if on == "" { table.to_string() } else {
                format!("{table} ON {on}")
            })
            .collect::<Vec<_>>()
            .join(" JOIN ");
        let tables = if tables != "" {
                format!(" FROM {tables}")
            } else { "".to_string() };
        let where_ = if self.where_ == "" { "".to_string() } else {
            format!(" WHERE {0}", self.where_)
        };
        let group_by = if self.group_by == "" { "".to_string() } else {
            format!(" GROUP BY {0}", self.group_by)
        };
        write!(f, "SELECT {variables}{condition}{grounding} AS G{tables}{where_}{group_by}")
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Grounding {
    Function(View),
    Boolean{tu: View, uf: View, g: View}
}
impl std::fmt::Display for Grounding {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Grounding::Function(view) => write!(f, " {view}"),
            Grounding::Boolean{tu, uf, g, ..} => {
                writeln!(f, "")?;
                writeln!(f, "    TU: {tu}")?;
                writeln!(f, "    UF: {uf}")?;
                write!  (f, "    G : {g}")
            },
        }
    }
}


/////////////////////  Command ///////////////////////////////////////////////


/// execute the x-ground command
pub(crate) fn ground(
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    gen!({
        // validate the commands
        let commands = solver.terms_to_ground.iter()
            .map(|(_,command)| command.clone())
            .collect::<Vec<_>>();
        for command in commands {
            // todo: push and pop, to avoid polluting the SMT state
            yield_!(solver.exec(&command))
        }

        // ground the terms
        let terms = solver.terms_to_ground.iter()
            .map(|(term, _)| term.clone())
            .collect::<Vec<_>>();

        let mut variables = IndexMap::new();
        let mut assertions = vec![];
        for term in terms {
            if let Ok(i) = ground_term(&term, &mut variables, true, solver) {
                assertions.push(i)
            } else {
                yield_!(Err(InternalError(8423458569)))
            }
        }
        // todo: run the query for all assertions, and solver.exec the resulting grounding

        // reset terms to ground
        solver.terms_to_ground = vec![];
    })
}


/// Adds the grounding of a term to the solver, if necessary.
/// This function is recursive.
///
/// # Arguments
///
/// * variables: the variables in the current scope
/// * top_level: indicates if it is an assertion (to avoid building a conjunction)
///
fn ground_term(
    term: &Term,
    variables: &mut IndexMap<Symbol, SortedVar>,
    top_level: bool,
    solver: &mut Solver
) -> Result<usize, SolverError> {

    if let Some(i) = solver.groundings.get_index_of(term) {
        return Ok(i)
    } else {
        let (new_term, grounding) = ground_term_(term, variables, top_level, solver)?;
        let (i, _) = solver.groundings.insert_full(new_term, grounding);
        Ok(i)
    }
}

/// Helper function to ground a new term.
/// An identifier term representing a variable is replaced by a XSortedVar term.
///
/// # Arguments:
///
/// * variables: the variables in the current scope
/// * top_level: indicates if it is an assertion (to avoid building a conjunction)
///
fn ground_term_(
    term: &Term,
    variables: &mut IndexMap<Symbol, SortedVar>,
    _top_level: bool,
    solver: &mut Solver
) -> Result<(Term, Grounding), SolverError> {

    match term {
        Term::SpecConstant(spec_constant) => {

            // a number or string
            let grounding = View {
                variables: IndexMap::new(),
                condition: "".to_string(),
                grounding: format!("\"{spec_constant}\""),
                joins: IndexMap::new(),
                where_: "".to_string(),
                group_by: "".to_string(),
                _ids: Ids::All,
            };
            Ok((term.clone(), Grounding::Function(grounding)))
        },
        Term::XSortedVar(..) => Err(InternalError(85126645)),  // sorted var should be handled by the quantification
        Term::Identifier(qual_identifier) => {
            match qual_identifier {
                QualIdentifier::Identifier(identifier) => {
                    match identifier {
                        Identifier::Simple(symbol) => {
                            match variables.get(symbol) {
                                None => {

                                    // a predicate or constant
                                    ground_application(term, qual_identifier, &vec![], variables, solver)

                                },
                                Some(SortedVar(_, sort)) => {

                                    // a variable
                                    match solver.sorts.get(sort) {
                                        Some(SortObject::Normal {table_name, ..}) => {
                                            // variable `symbol`` in `table_name`
                                            let view = View {
                                                variables: IndexMap::from([(symbol.clone(), table_name.clone())]),
                                                condition: "".to_string(),
                                                grounding: format!("{table_name}.G"),
                                                joins: IndexMap::from([(table_name.clone(), "".to_string())]),
                                                where_: "".to_string(),
                                                group_by: "".to_string(),
                                                _ids: Ids::All,
                                            };
                                            Ok((term.clone(), Grounding::Function(view)))
                                        },
                                        Some(SortObject::Infinite)
                                        | Some(SortObject::Recursive)
                                        | Some(SortObject::Unknown) => {
                                            // `symbol` as computed
                                            todo!()
                                        },
                                        None => { todo!() }
                                    }
                                },
                            }
                        },
                        Identifier::Indexed(..) => todo!()
                    }
                },
                QualIdentifier::Sorted(..) => todo!(),
            }
        },
        Term::Application(..) => todo!(),
        Term::Let(..) => todo!(),
        Term::Forall(..) => todo!(),
        Term::Exists(..) => todo!(),
        Term::Match(..) => todo!(),
        Term::Annotation(..) => todo!(),
    }
}

/// # Arguments
///
/// * term: the full term
/// * qual_identifier: the applied function
/// * variables: the variables in the current scope
///
fn ground_application(
    term: &Term,
    qual_identifier: &QualIdentifier,
    arguments: &Vec<Term>,
    _variables: &mut IndexMap<Symbol, SortedVar>,
    solver: &mut Solver
) -> Result<(Term, Grounding), SolverError> {

    let function_object = match qual_identifier {
        QualIdentifier::Identifier(identifier) => {
            // todo detect operators, true, false
            solver.functions.get(identifier)
        },
        QualIdentifier::Sorted(..) =>
        // lookup solver.qualified_functions
            todo!()
    };

    match function_object {
        Some(FunctionObject{typ, boolean, ..}) => {
            match typ {
                InterpretationType::Calculated => {
                    if arguments.len() == 0 {

                        // a constant
                        let g = View {
                            variables: IndexMap::new(),
                            condition: "".to_string(),
                            grounding: format!("\"{qual_identifier}\""),
                            joins: IndexMap::new(),
                            where_: "".to_string(),
                            group_by: "".to_string(),
                            _ids: Ids::None,
                        };
                        let grounding =
                            match boolean {
                                Some(true) => Grounding::Boolean{tu: g.clone(), uf: g.clone(), g:g},
                                Some(false) => Grounding::Function(g),
                                None => todo!(),
                            };
                        Ok((term.clone(), grounding))

                    } else {

                        // a true function application
                        todo!()
                    }
                }
            }
        },
        None => todo!(),
    }
}