// Copyright Pierre Carbonnelle, 2025.

use regex::Regex;
use std::future::Future;

use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::{IndexMap, IndexSet};
use rusqlite::{Connection, Result};
use z3_sys::*;

use crate::api::*;
use crate::error::{format_error, SolverError, Offset};
use crate::grammar::parse;
use crate::private::a_sort::{declare_datatype, declare_datatypes, declare_sort, define_sort, ParametricObject, SortObject};
use crate::private::b_fun::{declare_fun, FunctionObject};
use crate::private::c_assert::assert_;
use crate::private::d_interpret::{interpret_pred, interpret_fun};
use crate::private::e_ground::{ground, Grounding};
use crate::private::e2_ground_query::DbName;
use crate::private::y_db::init_db;
use crate::api::L;


#[derive(PartialEq)]
pub(crate) enum Backend {
    NoDriver,
    Z3(Z3_context)
}

pub(crate) type TermId = usize;


pub struct Solver {
    pub(crate) backend: Backend,
    /// help ensure the backend is not changed after a command has been executed
    pub (crate) started: bool,
    pub conn: Connection,

    /// contains only parametric data type declarations
    pub(crate) parametric_sorts: IndexMap<Symbol, ParametricObject>,

    /// contains nullary data types and the used instantiations of parametric data types
    pub(crate) sorts: IndexMap<Sort, SortObject>,

    /// predicate and function symbols
    pub(crate) functions: IndexMap<QualIdentifier, FunctionObject>,
    // pub(crate) qualified_functions: IndexMap<QualIdentifier, FunctionObject>,

    /// To support differed grounding of terms.
    /// The string is the original assertion command.
    /// The first element is the annotated term
    pub(crate) assertions_to_ground: Vec<(String, L<Term>)>,
    /// a mapping from a term to a composable representation of its grounding
    pub(crate) groundings: IndexMap<L<Term>, Grounding>,

    /// to convert interpretations to definitions when given late
    /// (i.e., make an assertion with p, x-ground, interpret p
    /// --> need to add a definition of p to avoid losing information about p)
    pub(crate) grounded: IndexSet<Identifier>,

    /// to handle the fact that db names are case insensitive in sqlite
    pub(crate) db_names: IndexSet<String>,
}


impl Default for Solver {
    fn default() -> Solver {

        // create Bool table
        let mut conn = Connection::open_in_memory().unwrap();
        conn.execute(
            "CREATE TABLE Bool (
                    G    TEXT PRIMARY KEY
            )",
            (), // empty list of parameters.
        ).unwrap();
        conn.execute("INSERT INTO Bool (G) VALUES (\"true\")" , ()).unwrap();
        conn.execute("INSERT INTO Bool (G) VALUES (\"false\")", ()).unwrap();

        init_db(&mut conn).unwrap();

        // Note: indexed sorts are created as Unknown when occurring: (_ BitVec n), (_ FloatingPoint eb sb)

        // create pre-defined parametric sorts: (Array ..), (Seq ..), (Tuple..)
        let mut parametric_sorts = IndexMap::new();
        parametric_sorts.insert(Symbol("Array".to_string()), ParametricObject::Unknown);

        // not in the SMT-Lib standard:
        // parametric_sorts.insert(Symbol("Seq".to_string()), ParametricObject::Unknown);
        // parametric_sorts.insert(Symbol("Tuple".to_string()), ParametricObject::Unknown);

        // create pre-defined sorts: Bool, Int, Real
        let mut sorts = IndexMap::new();
        let sort = |s: &str| Sort::Sort(L(Identifier::Simple(Symbol(s.to_string())), Offset(0)));

        let bool_decl = SortObject::Normal{
            datatype_dec: DatatypeDec::DatatypeDec(
                vec![
                    ConstructorDec (Symbol("true" .to_string()),vec![]),
                    ConstructorDec (Symbol("false".to_string()),vec![]),
                ],
                ),
            table: DbName("Bool".to_string()),
            row_count: 2};
        sorts.insert(sort("Bool"), bool_decl);
        // LINK src/doc.md#_Infinite
        sorts.insert(sort("Int" ), SortObject::Infinite);
        sorts.insert(sort("Real" ), SortObject::Infinite);
        sorts.insert(sort("RoundingMode" ), SortObject::Infinite);  // in FloatingPoint theory
        sorts.insert(sort("String" ), SortObject::Infinite);  // in String theory
        sorts.insert(sort("RegLan" ), SortObject::Infinite);  // in String theory

        // create pre-defined functions
        let mut functions = IndexMap::new();
        let function = |s: &str|
            QualIdentifier::Identifier(L(Identifier::Simple(Symbol(s.to_string())), Offset(0)));

        // boolean pre-defined functions
        // LINK src/doc.md#_Constructor
        for s in ["true", "false"] {
            functions.insert(function(s),
                FunctionObject::Constructor);
        }

        // boolean pre-defined functions
        for s in ["not",
                        "=>", "and", "or", "xor",
                        "=", "distinct",
                        "<=", "<", ">=", ">"
                        ] {
            functions.insert(function(s),
                FunctionObject::Predefined{ boolean: Some(true) });
        }

        // ite
        functions.insert(function("ite"),
            FunctionObject::Predefined { boolean: None });

        // non-boolean pre-defined functions
        for s in ["+", "-", "*", "div",
                        "mod", "abs",
                        ] {
            functions.insert(function(s),
                FunctionObject::Predefined{ boolean: Some(false) });
        };

        unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            let backend = Backend::Z3(ctx);

            Solver {
                backend: backend,
                started: false,
                conn: conn,
                parametric_sorts: parametric_sorts,
                sorts: sorts,
                functions: functions,
                // qualified_functions: IndexMap::new(),
                assertions_to_ground: vec![],
                groundings: IndexMap::new(),
                grounded: IndexSet::new(),
                db_names: IndexSet::new(),
            }
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
                            Err(e) => {
                                yield_!(format_error(&source, e));
                                break
                            }
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
                    if result.is_err() {
                        yield_!(result);
                        break
                    } else {
                        yield_!(result);
                    }
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
            let command = c.to_string();
            match c {

                Command::Assert(term) =>
                    yield_!(assert_(&term, command, self)),

                Command::CheckSat => {
                    for res in ground(self) {
                        yield_!(res)
                    }
                    match self.exec(&command) {
                        Ok(res) => yield_!(Ok(res)),
                        Err(err) => {
                            yield_!(Err(err));
                        }
                    };
                }

                Command::DeclareConst(symb, sort) =>
                    yield_!(declare_fun(symb, vec![], sort, command, self)),

                Command::DeclareDatatype(symb, decl) =>
                    yield_!(declare_datatype(symb, decl, command, self)),

                Command::DeclareDatatypes(sort_decls, decls) =>
                    yield_!(declare_datatypes(sort_decls, decls, command, self)),

                Command::DeclareFun(symb, domain, co_domain) =>
                    yield_!(declare_fun(symb, domain, co_domain, command, self)),

                Command::DeclareSort(symb, numeral) =>
                    yield_!(declare_sort(symb, numeral, command, self)),

                Command::DefineSort(symb, variables, sort) =>
                    yield_!(define_sort(symb, variables, sort, command, self)),

                Command::XInterpretPred(identifier, tuples) =>
                    yield_!(interpret_pred(identifier, tuples, self)),

                Command::XInterpretFun(identifier, tuples, else_) =>
                    yield_!(interpret_fun(identifier, tuples, else_, command, self)),

                Command::SetOption(option) =>
                    yield_!(self.set_option(option, command)),

                Command::XDebug(typ, obj) => {
                    match typ.to_string().as_str() {
                        "solver" => {
                            match obj.to_string().as_str() {
                                "sorts" => {
                                    yield_!(Ok("Sorts:\n".to_string()));
                                    for (sort, decl) in &self.sorts {
                                        match decl {
                                            SortObject::Normal{datatype_dec, table, row_count} =>
                                                yield_!(Ok(format!(" - ({table}: {row_count}) {sort}: {datatype_dec}\n"))),
                                            SortObject::Recursive =>
                                                yield_!(Ok(format!(" - (recursive) {sort}\n"))),
                                            SortObject::Infinite =>
                                                yield_!(Ok(format!(" - (infinite) {sort}\n"))),
                                            SortObject::Unknown =>
                                                yield_!(Ok(format!(" - (unknown) {sort}\n"))),
                                        }
                                    }
                                },
                                "parametric_sorts" => {
                                    yield_!(Ok("Parametric datatypes:\n".to_string()));
                                    for (sort, decl) in &self.parametric_sorts {
                                        match decl {
                                            ParametricObject::Datatype(decl) =>
                                                yield_!(Ok(format!(" - {sort}: {decl}\n"))),
                                            ParametricObject::DTDefinition{variables, definiendum} => {
                                                let vars = variables.iter()
                                                    .map(|v| v.0.clone())
                                                    .collect::<Vec<String>>().join(",");
                                                yield_!(Ok(format!(" - {sort}: ({vars}) -> {definiendum}\n")))
                                            },
                                            ParametricObject::Recursive =>
                                                yield_!(Ok(format!(" - (recursive): {sort}\n"))),
                                            ParametricObject::Unknown =>
                                                yield_!(Ok(format!(" - (unknown): {sort}\n"))),
                                        }
                                    }
                                },
                                "functions" => {
                                    yield_!(Ok("Functions:\n".to_string()));
                                    for (symbol, func) in &self.functions {
                                        yield_!(Ok(format!(" - {symbol}: {func}\n")))
                                    }
                                },
                                "groundings" => {
                                    yield_!(Ok("Groundings:\n".to_string()));
                                    for (term, grounding) in &self.groundings {
                                        yield_!(Ok(format!(" - {term}:{grounding}\n")))
                                    }
                                },
                                _ => yield_!(Err(SolverError::IdentifierError("Unknown 'x-debug solver' parameter\n", obj)))
                            }
                        },
                        "db" => {
                            if obj.to_string() == "tables" {
                                // Query to list all tables and views in the database
                                let query = "SELECT name, type FROM sqlite_master WHERE type IN ('table', 'view')";
                                let mut stmt = self.conn.prepare(query).unwrap();
                                let rows = stmt.query_map([], |row| {
                                    let name: String = row.get(0)?;
                                    let typ: String = row.get(1)?;
                                    Ok((name, typ))
                                }).unwrap();

                                yield_!(Ok("Tables and Views:\n".to_string()));
                                for row in rows {
                                    if let Ok((name, typ)) = row {
                                        yield_!(Ok(format!(" - {name} ({typ})\n")));
                                    }
                                }
                            } else if let Ok(content) = pretty_sqlite::pretty_table(&self.conn, obj.to_string().to_lowercase().as_str()) {
                                yield_!(Ok(format!("{content}\n")))
                            } else {
                                yield_!(Err(SolverError::IdentifierError("Unknown table\n", typ)))
                            }
                        },
                        "db-view" => {
                            // helper function
                            let query = || {
                                let mut stmt = self.conn.prepare("SELECT sql FROM sqlite_master WHERE type='view' AND name=?1")?;
                                let res = stmt.query_row([obj.to_string()], |row| row.get::<_, String>(0))?;
                                Ok(res)
                            };
                            yield_!(query());
                            yield_!(Ok(format!("\n")))
                        },
                        _ => yield_!(Err(SolverError::IdentifierError("Unknown 'x-debug' parameter\n", typ)))
                    }
                },

                Command::XGround => {
                    for res in ground(self) {
                        yield_!(res)
                    }
                }

                Command::Verbatim(_) => {
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

    /// execute a command string
    pub(crate) fn exec(&mut self, cmd: &str) -> Result<String, SolverError> {
        if cmd.to_string().len() != 0 {
            self.started = true;
        }
        match self.backend {
            Backend::NoDriver => {
                return Ok(cmd.to_string())
            },
            Backend::Z3(ctx) => {
                unsafe {
                    let c_cmd = std::ffi::CString::new(cmd).unwrap();
                    let response = Z3_eval_smtlib2_string(ctx, c_cmd.as_ptr());
                    let c_str: &std::ffi::CStr = std::ffi::CStr::from_ptr(response);
                    let str_slice: &str = c_str.to_str().unwrap();
                    let result: String = str_slice.to_owned();
                    return Ok(result)
                }
            }
        }
    }

    pub(crate) fn set_option(&mut self, option: Option_, cmd: String) -> Result<String, SolverError> {
        match option {
            Option_::Attribute(Attribute::Keyword(_)) => {
                self.exec(&cmd)
            },
            Option_::Attribute(Attribute::WithValue(keyword, value)) => {
                match (keyword.0.as_str(), value) {
                    (":backend", AttributeValue::Symbol(Symbol(value))) => {
                        let new =
                            match value.as_str() {
                                "none" => Backend::NoDriver,
                                "Z3" => {
                                    unsafe {
                                        let cfg = Z3_mk_config();
                                        let ctx = Z3_mk_context(cfg);
                                        Backend::Z3(ctx)
                                    }
                                },
                                _ => return Err(SolverError::ExprError(format!("Unknown backend: {value}")))
                            };
                        if self.backend != new {
                            if self.started {
                                return Err(SolverError::ExprError("Can't change backend anymore".to_string()))
                            };
                            self.backend = new;
                        }
                        Ok("".to_string())
                    },
                    _ => self.exec(&cmd)
                }

            },
        }
    }


    /// Sanitize a name.  Removes non-alphanumeric characters, and adds a number if empty or ambiguous.
    pub(crate) fn create_db_name(self: &mut Solver, name: String) -> DbName {
        let re = Regex::new(r"[\+\-/\*=\%\?\!\.\$\&\^<>@]").unwrap();
        let db_name = re.replace_all(&name, "").to_string().to_lowercase();
        let index = self.db_names.len();
        let db_name =
            if db_name.len() == 0 {
                format!("_xmt_{index}")
            } else {
                let temp = format!("_xmt_{db_name}");
                if self.db_names.contains(&temp) {
                    format!("_xmt_{db_name}_{index}")
                } else {
                    temp
                }
            };
        self.db_names.insert(db_name.clone());
        DbName(db_name)
    }
}
