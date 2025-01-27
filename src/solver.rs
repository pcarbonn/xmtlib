// Copyright Pierre Carbonnelle, 2025.

use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::IndexMap;
use rusqlite::{Connection, Result};

use crate::api::*;
use crate::error::{format_error, SolverError};
use crate::grammar::parse;
use crate::private::a_sort::*;
use crate::private::y_db::init_db;


pub enum Backend {
    NoDriver
}


pub struct Solver {
    pub(crate) backend: Backend,
    pub(crate) conn: Connection,

    // contains only parametric data type declarations
    pub(crate) parametric_sorts: IndexMap<Symbol, ParametricObject>,

    // contains nullary data types and the used instantiations of parametric data types
    pub(crate) sorts: IndexMap<Sort, SortObject>,
}


impl Default for Solver {
    fn default() -> Solver {
        let sort = |s: &str| Sort::Sort(Identifier::Simple(Symbol(s.to_string())));
        let bool_sort = sort("Bool");
        let bool_decl = SortObject::Normal(DatatypeDec::DatatypeDec(
            vec![
                ConstructorDec (Symbol("true" .to_string()),vec![]),
                ConstructorDec (Symbol("false".to_string()),vec![]),
            ],
        ), "Bool".to_string());

        // create Bool table
        let mut conn = Connection::open_in_memory().unwrap();
        conn.execute(
            "CREATE TABLE Bool (
                    G    TEXT
            )",
            (), // empty list of parameters.
        ).unwrap();
        conn.execute("INSERT INTO Bool (G) VALUES (\"true\")" , ()).unwrap();
        conn.execute("INSERT INTO Bool (G) VALUES (\"false\")", ()).unwrap();

        init_db(&mut conn).unwrap();

        Solver {
            backend: Backend::NoDriver,
            conn: conn,
            parametric_sorts: IndexMap::new(),
            sorts: IndexMap::from([
                (bool_sort, bool_decl),
                (sort("Int" ), SortObject::Infinite),
                (sort("Real"), SortObject::Infinite),
                ])
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
                    yield_!(declare_datatype(symb, decl, command, self))
                }

                Command::DeclareDatatypes(sort_decls, decls) => {
                    yield_!(declare_datatypes(sort_decls, decls, command, self))
                }

                Command::DeclareSort(symb, numeral) => {
                    yield_!(declare_sort(symb, numeral, command, self))
                }

                Command::DefineSort(symb, variables, sort) => {
                    yield_!(define_sort(symb, variables, sort, command, self))
                }

                Command::XDebug(typ, obj) => {
                    match typ.as_str() {
                        "solver" => {
                            match obj.as_str() {
                                "sorts" => {
                                    yield_!(Ok("Sorts:".to_string()));
                                    for (sort, decl) in &self.sorts {
                                        match decl {
                                            SortObject::Normal(decl, table) =>
                                                yield_!(Ok(format!(" - ({}) {}: {}", table, sort, decl))),
                                            SortObject::Recursive =>
                                                yield_!(Ok(format!(" - (recursive) {}", sort))),
                                            SortObject::Infinite =>
                                                yield_!(Ok(format!(" - (infinite) {}", sort))),
                                            SortObject::Unknown =>
                                                yield_!(Ok(format!(" - (unknown) {}", sort))),
                                        }
                                    }
                                },
                                "parametric_sorts" => {
                                    yield_!(Ok("Parametric datatypes:".to_string()));
                                    for (sort, decl) in &self.parametric_sorts {
                                        match decl {
                                            ParametricObject::Datatype(decl) =>
                                                yield_!(Ok(format!(" - {}: {}", sort, decl))),
                                            ParametricObject::Definition(vars, parent_sort) => {
                                                let vars = vars.iter().map(|v| v.0.clone()).collect::<Vec<String>>().join(",");
                                                yield_!(Ok(format!(" - {}: ({}) -> {}", sort, vars, parent_sort)))
                                            },
                                            ParametricObject::Recursive =>
                                                yield_!(Ok(format!(" - (recursive): {}", sort))),
                                            ParametricObject::Unknown =>
                                                yield_!(Ok(format!(" - (unknown): {}", sort))),
                                        }
                                    }
                                },
                                _ => {
                                    yield_!(Err(SolverError::ExprError("Unknown 'x-debug solver' parameter".to_string(), None)))
                                }
                            }
                        },
                        "db" => {
                            if let Ok(content) = pretty_sqlite::pretty_table(&self.conn, obj.as_str()) {
                                yield_!(Ok(content))
                            } else {
                                yield_!(Err(SolverError::ExprError("Unknown table".to_string(), None)))
                            }
                        },
                        _ => yield_!(Err(SolverError::ExprError("Unknown 'x-debug' parameter".to_string(), None)))
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
    pub(crate) fn exec(&mut self, cmd: &str) -> Result<String, SolverError> {
        match self.backend {
            Backend::NoDriver => {
                return Ok(cmd.to_string())
            }
        }
    }

}
