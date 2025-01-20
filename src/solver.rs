// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;

use crate::api::*;
use crate::error::{format_error, SolverError, check_condition};
use crate::grammar::parse;
use crate::private::sort::annotate_sort_decl;

pub enum Backend {
    NoDriver
}

pub struct Solver {
    pub(crate) backend: Backend,

    // contains only parametric data type declarations
    pub(crate) parametric_datatypes: IndexMap<Symbol, DatatypeDec>,

    // contains nullary data types and the used instantiations of parametric data types
    pub(crate) sorts: IndexMap<Sort, Option<DatatypeDec>>,  // None for pre-defined infinite sorts
}

impl Default for Solver {
    fn default() -> Solver {
        let sort = |s: &str| Sort::Sort(Identifier::Simple(Symbol(s.to_string())));
        let bool_sort = sort("Bool");
        let bool_decl = DatatypeDec::DatatypeDec(
            vec![
                ConstructorDec (Symbol("true" .to_string()),vec![]),
                ConstructorDec (Symbol("false".to_string()),vec![]),
            ],
        );

        Solver {
            backend: Backend::NoDriver,
            parametric_datatypes: IndexMap::new(),
            sorts: IndexMap::from([
                (bool_sort, Some(bool_decl)),
                (sort("Int" ), None),
                (sort("Real"), None),
                ]),
        }
    }
}

impl Solver {

    /// Execute the XMT-Lib commands in a string, and returns a generator of strings containing the results.
    pub fn parse_and_execute<'a> (
        &'a mut self,
        source: &'a str
    ) -> Gen<String, (), impl Future<Output = ()> + 'a> {
        gen!({
            match parse(&source) {
                Ok(commands) => {
                    for result in self.execute(commands) {
                        match result {
                            Ok(s) => yield_!(s),
                            Err(e) => yield_!(format_error(&source, e))
                        }
                    }
                },
                Err(err) => {
                    // Pretty-print the error
                    yield_!(format_error(&source, SolverError::ParseError(err)))
                }
            }
        })
    }

    /// Execute the SMT-Lib commands and returns a generator of strings containing the results.
    pub fn execute (
        &mut self,
        commands: Vec<Command>
    ) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {
        gen!({
            for command in commands {
                for result in self.execute1(command) {
                    yield_!(result)
                }
            }
        })
    }

    /// Execute one command and returns a generator of strings containing the results.
    pub fn execute1 (
        &mut self,
        c: Command
    ) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {
        gen!({
            let command = format!("{}", c);
            match c {

                Command::CheckSat => {
                    yield_!(Ok("sat".to_string()));  // TODO
                },

                Command::DeclareDatatype(symb, decl) => {
                    if let Err(err) = annotate_sort_decl(&symb, &decl, self) {
                        yield_!(Err(err))
                    };

                    match self.exec(&command) {
                        Ok(res) => yield_!(Ok(res)),
                        Err(err) => {
                            yield_!(Err(err));
                        }
                    };
                }

                Command::XDebug(s) => {
                    match s.as_str() {
                        "sorts" => {
                            yield_!(Ok("Sorts:".to_string()));
                            for (sort, decl) in &self.sorts {
                                if let Some(decl) = decl {
                                    yield_!(Ok(format!(" - {}: {}", sort, decl)));
                                } else {
                                    yield_!(Ok(format!(" - {}: infinite", sort)));
                                }
                            }
                        },
                        "parametric_datatypes" => {
                            yield_!(Ok("Parametric datatypes:".to_string()));
                            for (sort, decl) in &self.parametric_datatypes {
                                yield_!(Ok(format!(" - {}: {}", sort, decl)));
                            }
                        },
                        _ => {
                            if let Err(e) = check_condition(false,
                                       "Unknown x-debug parameter", None) {
                                yield_!(Err(e))
                            }
                        }
                    }
                },

                _ => {
                    match self.exec(&command) {
                        Ok(res) => yield_!(Ok(res)),
                        Err(err) => {
                            yield_!(Err(err));
                        }
                    };
                },
            }
        })
    }

    // execute a command string
    fn exec(&mut self, cmd: &str) -> Result<String, SolverError> {
        match self.backend {
            Backend::NoDriver => {
                return Ok(cmd.to_string())
            }
        }
    }

}
