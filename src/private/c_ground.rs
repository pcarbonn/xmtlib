// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;

use crate::api::Identifier;
use crate::api::QualIdentifier;
use crate::api::SortedVar;
use crate::api::Symbol;

/// Contains what is needed to construct the grounding view of a term, in a composable way.
pub(crate) struct Grounding {
    // for variable x in Color --> select color.G as x, color.G as G from Color
    //      variables:  `x -> Color.G`, i.e., variable name to column name
    //      condition:  ""
    //      grounding:  "Color.G"
    //      joins:      Color
    //      where:      ""
    //      group_by:   ""
    //      all_ids:    true

    // For a calculated term p
    // e.g., p(x, f(a)) --> select color.G as x, apply("p", Color.G, apply("f", "a")) as G from Color
    //      variables:  `x -> Color.G`, i.e., variable name to column name
    //      condition:  ""
    //      grounding:  apply("p", Color.G, apply("f", "a"))
    //      joins:      Color
    //      where:      ""
    //      group_by:   ""
    //      all_ids:    false

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

    _all_ids: bool,
}


impl std::fmt::Display for Grounding {

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
                format!("FROM {tables}")
            } else { "".to_string() };
        let where_ = if self.where_ == "" { "".to_string() } else {
            format!(" WHERE {0}", self.where_)
        };
        let group_by = if self.group_by == "" { "".to_string() } else {
            format!(" GROUP BY {0}", self.group_by)
        };
        write!(f, "SELECT {variables}{condition}{grounding} AS G {tables}{where_}{group_by}")
    }
}


/////////////////////  Command ///////////////////////////////////////////////

use crate::api::Term;
use crate::solver::Solver;
use crate::error::SolverError::{self, *};


/// execute the x-ground command
pub(crate) fn ground(
    solver: &mut Solver
) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {

    let commands = solver.terms_to_ground.iter()
        .map(|(_,command)| command.clone()).collect::<Vec<_>>();
    let terms = solver.terms_to_ground.iter()
        .map(|(term, _)| term.clone()).collect::<Vec<_>>();

    gen!({
        // validate the commands
        for command in commands {
            // todo: push and pop, to avoid polluting the SMT state
            yield_!(solver.exec(&command))
        }

        // ground the terms
        let mut variables = IndexMap::new();
        for term in terms {
            if let Ok(i) = ground_term(&term, &mut variables, true, solver) {
                // todo: run the query and execute the grounding
            } else {
                yield_!(Err(InternalError(8423458569)))
            }
        }

        // reset terms to ground
        solver.terms_to_ground = vec![];
    })
}


/// Adds the grounding of a term to the solver.
/// This function is recursive.
fn ground_term(
    term: &Term,
    // the variables in the current scope
    variables: &mut IndexMap<Symbol, SortedVar>,
    // indicates if it is an assertion (to avoid building a conjunction)
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

/// Helper function to ground a term.
/// An identifier term representing a variable is replaced by a XSortedVar term.
fn ground_term_(
    term: &Term,
    // the variables in the current scope
    variables: &mut IndexMap<Symbol, SortedVar>,
    // indicates if it is an assertion (to avoid building a conjunction)
    top_level: bool,
    _solver: &mut Solver
) -> Result<(Term, Grounding), SolverError> {

    match term {
        Term::SpecConstant(spec_constant) => {
            let grounding = Grounding {
                variables: IndexMap::new(),
                condition: "".to_string(),
                grounding: format!("\"{spec_constant}\""),
                joins: IndexMap::new(),
                where_: "".to_string(),
                group_by: "".to_string(),
                _all_ids: true,
            };
            Ok((term.clone(), grounding))
        },
        Term::XSortedVar(..) => Err(InternalError(85126645)),  // sorted var should be handled by the quantification
        Term::Identifier(qual_identifier) => {
            match qual_identifier {
                QualIdentifier::Identifier(Identifier::Simple(symbol)) => {
                    match variables.get(symbol) {
                        Some(_) => {
                            // let grounding = Grounding {
                            //     variables: IndexMap::from([(symbol.clone(), format!("{sort}.G as {symbol}"))]),
                            //     condition: "".to_string(),
                            //     grounding: format!("{sort}.G"),
                            //     joins: IndexMap::from([(format!("{sort}"), "".to_string())]),
                            //     where_: "".to_string(),
                            //     group_by: "".to_string(),
                            //     all_ids: true,
                            // };
                            // Ok(format!("{grounding}"))
                            todo!()
                        },
                        None => {
                            // todo
                            todo!()
                        }
                    }
                },
                QualIdentifier::Sorted(..) => todo!(),
                _ => todo!()
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