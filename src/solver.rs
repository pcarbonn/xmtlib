// Copyright Pierre Carbonnelle, 2025.

use regex::Regex;
use std::future::Future;

use derive_more::Display;
use genawaiter::{sync::Gen, sync::gen, yield_};
use indexmap::{IndexMap, IndexSet};
use rusqlite::{Connection, Result};
use z3_sys::*;

use crate::ast::*;
use crate::error::{format_error, SolverError, Offset};
use crate::grammar::parse;
use crate::private::a_sort::{declare_datatype, declare_datatypes, declare_sort, define_sort, ParametricObject, SortObject};
use crate::private::b_fun::{declare_fun, FunctionObject};
use crate::private::c_assert::assert_;
use crate::private::d_interpret::{interpret_pred, interpret_fun};
use crate::private::e_ground::{ground, Grounding};
use crate::private::e2_ground_query::TableName;
use crate::private::y_db::init_db;
use crate::ast::L;


#[derive(PartialEq)]
pub(crate) enum Backend {
    NoDriver,
    Z3(Z3_context)
}

pub(crate) type TermId = usize;

// A non-parametric sort without use of aliases (defined sort)
#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CanonicalSort(pub(crate) Sort);


/// A solver is used to solve SMT problems.
pub struct Solver {
    /// A connection to the sqlite database used for grounding assertions
    /// (via the [rusqlite](https://docs.rs/rusqlite/latest/rusqlite/index.html) crate).
    pub(crate) conn: Connection,
    pub(crate) backend: Backend,
    /// help ensure the backend is not changed after a command has been executed
    pub (crate) started: bool,

    /// contains only parametric data type declarations
    pub(crate) parametric_sorts: IndexMap<Symbol, ParametricObject>,

    /// contains nullary data types and the used instantiations of parametric data types
    pub(crate) canonical_sorts: IndexMap<Sort, CanonicalSort>,
    pub(crate) sort_objects: IndexMap<CanonicalSort, SortObject>,

    /// predicate and function symbols
    pub(crate) functions: IndexMap<L<Identifier>, FunctionObject>,

    /// To support differed grounding of terms.
    /// The string is the original assertion command.
    /// The first element is the annotated term
    pub(crate) assertions_to_ground: Vec<L<Term>>,
    /// a mapping from a term (top-level?) to a composable representation of its grounding
    pub(crate) groundings: IndexMap<(L<Term>, bool), Grounding>,

    /// to convert interpretations to definitions when given late
    /// (i.e., make an assertion with p, x-ground, interpret p
    /// --> need to add a definition of p to avoid losing information about p)
    pub(crate) grounded: IndexSet<Identifier>,

    /// to handle the fact that db names are case insensitive in sqlite
    pub(crate) db_names: IndexSet<String>,
}


impl Solver {
    /// Creates a solver.
    /// Optionally gives access to a sqlite database with pre-loaded data
    /// (via the [rusqlite](https://docs.rs/rusqlite/latest/rusqlite/index.html) crate).
    pub fn new(conn: Option<Connection>) -> Solver {

        let mut conn =
            if let Some(conn) = conn {
                conn
            } else {
                Connection::open_in_memory().unwrap()
            };

        // create Bool table
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
        let mut sort_objects = IndexMap::new();
        let sort = |s: &str|
            Sort::Sort(L(Identifier::Simple(Symbol(s.to_string())), Offset(0)));
        let canonical_sort = |s: &str|
            CanonicalSort(Sort::Sort(L(Identifier::Simple(Symbol(s.to_string())), Offset(0))));

        let bool_decl = SortObject::Normal{
            datatype_dec: DatatypeDec::DatatypeDec(
                vec![
                    ConstructorDec (Symbol("true" .to_string()),vec![]),
                    ConstructorDec (Symbol("false".to_string()),vec![]),
                ],
                ),
            table: TableName("Bool".to_string()),
            row_count: 2};
            sort_objects.insert(CanonicalSort(sort("Bool")), bool_decl);
        // LINK src/doc.md#_Infinite
        sort_objects.insert(canonical_sort("Int"), SortObject::Infinite);
        sort_objects.insert(canonical_sort("Real"), SortObject::Infinite);
        sort_objects.insert(canonical_sort("RoundingMode"), SortObject::Infinite);  // in FloatingPoint theory
        sort_objects.insert(canonical_sort("String"), SortObject::Infinite);  // in String theory
        sort_objects.insert(canonical_sort("RegLan"), SortObject::Infinite);  // in String theory


        let mut canonical_sorts = IndexMap::new();
        canonical_sorts.insert(sort("Bool"), canonical_sort("Bool"));
        canonical_sorts.insert(sort("Int"), canonical_sort("Int"));
        canonical_sorts.insert(sort("Real"), canonical_sort("Real"));
        canonical_sorts.insert(sort("RoundingMode"), canonical_sort("RoundingMode"));  // in FloatingPoint theory
        canonical_sorts.insert(sort("String"), canonical_sort("String"));  // in String theory
        canonical_sorts.insert(sort("RegLan"), canonical_sort("RegLan"));  // in String theory

        // create pre-defined functions
        let mut functions = IndexMap::new();
        let function = |s: &str|
            L(Identifier::Simple(Symbol(s.to_string())), Offset(0));

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

        // ite, lte
        functions.insert(function("ite"),
            FunctionObject::Predefined { boolean: None });
        functions.insert(function("let"),
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
                backend,
                started: false,
                conn,
                parametric_sorts,
                sort_objects,
                canonical_sorts,
                functions,
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
    pub(crate) fn execute (
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
    pub(crate) fn execute1 (
        &mut self,
        c: Command
    ) -> Gen<Result<String, SolverError>, (), impl Future<Output = ()> + '_> {
        gen!({
            let command = c.to_string();
            match c {

                Command::Assert(term) => {
                    if self.backend != Backend::NoDriver {
                        // submit to solver to detect syntax error
                        // push and pop, to avoid polluting the SMT state
                        yield_!(self.exec("(push)"));
                        yield_!(self.exec(&command));
                        yield_!(self.exec("(pop)"));
                    }

                    yield_!(assert_(&term, self))
                }
                Command::CheckSat => {
                    for res in ground(false, self) {
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
                                    for (sort, canonical) in &self.canonical_sorts {
                                        let decl = self.sort_objects.get(canonical).unwrap();
                                        let canonical = if canonical.0 == sort.clone() { "".to_string() }
                                            else { format!(" (= {canonical})") };
                                        match decl {
                                            SortObject::Normal{datatype_dec, table, row_count} =>
                                                yield_!(Ok(format!(" - ({table}: {row_count}) {sort}{canonical}: {datatype_dec}\n"))),
                                            SortObject::Recursive =>
                                                yield_!(Ok(format!(" - (recursive) {sort}{canonical}\n"))),
                                            SortObject::Infinite =>
                                                yield_!(Ok(format!(" - (infinite) {sort}{canonical}\n"))),
                                            SortObject::Unknown =>
                                                yield_!(Ok(format!(" - (unknown) {sort}{canonical}\n"))),
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
                                            ParametricObject::Recursive(decl) =>
                                                yield_!(Ok(format!(" - (recursive) {sort}: {decl}\n"))),
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
                                    for ((term, top), grounding) in &self.groundings {
                                        let top = if *top { "(top)" } else { "" };
                                        yield_!(Ok(format!("=== {top} {term} ======================================\n{grounding}\n")))
                                    }
                                    yield_!(Ok("===========================================\n".to_string()))
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
                        _ => yield_!(Err(SolverError::IdentifierError("Unknown 'x-debug' parameter\n", typ)))
                    }
                },

                Command::XGround(debug) => {
                    for res in ground(debug, self) {
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
    pub(crate) fn create_table_name(self: &mut Solver, name: String) -> TableName {
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
        TableName(db_name)
    }
}
