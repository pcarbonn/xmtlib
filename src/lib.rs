// cargo watch -x "doc --no-deps"

//! xmt-lib denotes:
//! * an expressive language for interacting with [SMT](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers;
//! * a program that executes commands in that language.
//!
//! The program can be used to find (optimal) solutions of combinatorial/configuration problems
//! and perform various reasoning tasks with knowledge represented in logical forms.
//! Of note, the xmt-lib program has a fast "grounder"
//! based on the [sqlite](https://sqlite.org) relational database engine.
//! The program can be called by another program (API interface) and can run standalone (CLI interface).
//!
//! xmt-lib extends the [SMT-Lib 2.6](https://smt-lib.org/language.shtml) language with the following commands:
//!
//! * `set-option :backend` to specify the SMT solver (if any) used to execute the xmt-lib commands;
//! * `x-interpret-const`, to specify the interpretation of a constant;
//! * `x-interpret-pred`, to specify the interpretation of a boolean function symbol;
//! * `x-interpret-fun`, to specify the interpretation of a function symbol;
//! * `x-ground`, to ground assertions, i.e., to expand the finite quantifications,
//! taking into account the known interpretations.
//!
//! It supports the Core, Int and Real [theories of SMT-Lib](https://smt-lib.org/theories.shtml).
//!
//!
//! # Usage
//!
//! This example shows how to use the xmt-lib crate to flag triangles in a graph, i.e. to assert:
//!
//! `∀ x,y,z: Edge(x,y) and Edge(y,z) and Edge(z, x) => RedTriangle(x, y, z).`
//!
//! * Install [z3](https://github.com/Z3Prover/z3) so that `z3` is in your `PATH`
//! * add `xmt-lib = "<version>"` to your `cargo.toml` file.
//! * add the following code, e.g., to `fn main()`:
//! ```
//! use xmt_lib::solver::Solver;
//!
//! fn main() -> () {
//!     let mut solver = Solver::default();
//!     let commands = r#"
//!         (set-option :backend Z3)
//!         (declare-fun Edge (Int Int) Bool)
//!         (declare-fun RedTriangle (Int Int Int) Bool)
//!         (x-interpret-pred Edge
//!             (x-set
//!                 (1 2)
//!                 (2 3)
//!                 (1 3)
//!             )
//!         )
//!         (assert (forall ((x Int) (y Int) (z Int))
//!                     (=> (and (Edge x y) (Edge y z) (Edge x z))
//!                         (RedTriangle x y z)
//!                     )))
//!         (check-sat)
//!     "#;
//!     let results = solver.parse_and_execute(&commands);
//!     for result in results {
//!         print!("{}", result);
//!     }
//! }
//! ```
//!
//! Executing the code will yield this output:
//! ```text
//! sat
//! ```
//!
//! If the Rust toolchain [cannot find `z3.h`](https://github.com/prove-rs/z3.rs/tree/master/z3-sys#finding-z3-libraries),
//! change the xmt-lib line in your Cargo.toml file to:
//!
//! ```text
//! xmt-lib = [version = "<version>", features = ["static-link-z3"]]
//! ```
//!
//! # Rust API interface
//!
//! The programmable interface of xmt-lib is text based: commands are sent as strings,
//! not as objects constructed in memory.
//! This is similar to the approach used in interfaces for the web (HTML) and relational databases (SQL).
//! An alternative is to construct commands in memory and submit the data structure via a call.
//! We believe the string approach makes an acceptable compromise between performance and simplicity.
//! Should we be wrong, we can easily make the memory-based API public.
//!
//! The Solver API is described [here](solver/struct.Solver.html).
//! Note that, unlike SMT-Lib 2.6, but like the Z3 solver,
//! xmt-lib accepts negative numbers in terms (e.g., `-1` is accepted for `(- 1)`).
//!
//! A solver instance has a connection to the sqlite database used for grounding assertions.
//! This connection can be used to efficiently load data in the database,
//! as examplified in the [triangle crate](../triangle/index.html).
//! The interpretation of a symbol can be specified using an sql statement, as described further below.
//!
//! The new commands introduced by xmt-lib are listed below.
//!
//!
//! ## (set-option :backend ...)
//!
//! This command has the following variants:
//!
//! * `set-option :backend none` to obtain the translation of xmt-lib commands to SMT-Lib 2.6;
//! * `set-option :backend Z3` for immediate execution of commands by a Z3 solver.
//!
//! By default, the backend is Z3.
//! It can only be changed at the start of a session.
//!
//!
//! ## (x-interpret-const ...)
//!
//! An `x-interpret-const` command specifies the interpretation of constant.
//! Such an intepretation can be given only once.
//!
//! Example: `(x-interpret-const c 1 )`.
//! The value of constant `c` is `1`.
//!
//! For a proposition `p` (aka a boolean constant), the interpretation can be given as :
//!
//! * `(x-interpret-const p true )` if `p` is true;
//! * `(x-interpret-const p false )` if `p` is false;
//!
//! Unlike an assertion about the value of a constant,
//! the interpretation of a constant is used to simplify the grounding.
//!
//! Note that interpreted constants may take any value in a model obtained by `(get-model)`.
//! So, in our example, `c` and `p` may have any value in a model.
//!
//!
//! ## (x-interpret-pred ...)
//!
//! An `x-interpret-pred` command specifies the total interpretation of a boolean function symbol (aka a predicate),
//! by listing all the tuples of arguments that make it true.
//! Such an intepretation can be given only once.
//!
//! Example: `(x-interpret-pred Edge (x-set (a b) (b c) (c a)) )`.
//! The only pairs of nodes that satisfy the `Edge` predicate are `(a b)`, `(b c)`, and `(c a)`.
//!
//! For a unary predicate over integers, the set can be given as a (union of) interval with inclusive boundaries:
//!
//! Example: `(x-interpret-pred Row (x-range 1 8) )`.
//! The values making Row true are 1, 2, 3, 4, 5, 6, 7, 8.
//!
//! Note that interpreted predicates may take any value in a model obtained by `(get-model)`.
//! So, in our example, `(Edge a b)` may have any value in a model.
//!
//!
//!
//! ## (x-interpret-pred p (x-sql "SELECT .. FROM .."))
//!
//! This variation of the `(x-interpret-pred` command
//! allows specifying the interpretation of a symbol, e.g.,  `p`,
//! using an sql SELECT that returns the tuples that make `p` true.
//!
//! The SELECT must return `n` columns named `a_0, .. a_n`
//! where `n` is the arity of the symbol being interpreted.
//! These columns must be of type INTEGER for integers, REAL for reals, and TEXT otherwise.
//!
//! The table may not have duplicate rows,
//! and the values in the columns must be nullary constructors of the appropriate type.
//! (note: these rules are not enforced by the xmtlib crate)
//!
//!
//! ## (x-interpret-fun ...)
//!
//! An `x-interpret-fun` command specifies the interpretation of a function symbol, possibly partially,
//! by associating a value to tuples of arguments, and by giving a default value.
//! (The interpretation of a function with an infinite domain cannot be given)
//!
//! Example: `(x-interpret-fun Length (x-mapping ((a b) 2) ((b c) ?) ((c a) 4) ) 999)`.
//! The length of pair `(a b)` is 2, of `(b c)` is unknown, of `(c a)` is 4,
//! and is 999 for every other pairs in the domain of Length.
//!
//! The grammar of this command is :
//!
//! ```text
//!     '(' 'x-interpret-fun' <symbol> '(' 'x-mapping' <mapping>* ')' <value>? ')'
//!```
//!
//! with 0 or more mapping of the form:
//!
//! ```text
//!    '(' <tuple> <value> ')'
//!```
//!
//! where a tuple is a list of identifiers between parenthesis (e.g., `(a b)`),
//! and a value is an identifier or  `?` (for unknown value).
//! The list of identifiers must match the arity of the function symbol.
//! The default value must be given if the set of tuples in the interpretation
//! does not cover the domain of the function;
//! it may not be given otherwise.
//!
//! Note that pre-interpreted terms may take any value in a model obtained by `(get-model)`.
//! (In our triangle example above,
//! `(Length a b)` can have any interpretation in a model,
//! but `(Length b c)` will have an interpretation that satisfies the assertions)
//!
//!
//! ## (x-interpret-fun f (x-sql "SELECT .. FROM ..") ..)
//!
//! This variation of the `(x-interpret-fun` command
//! allows specifying the interpretation of a function symbol, e.g.,  `f`,
//! using an sql SELECT that maps a tuple of ids to their image by `f`.
//!
//! The SELECT must return `n+1` columns named `a_0, .. a_n, G`
//! where `n` is the arity of the symbol being interpreted,
//! `a_0, .. a_n` contain the tuples of arguments, and `G` the corresponding values.
//! These columns must be of type INTEGER for integers, REAL for reals, and TEXT otherwise.
//!
//! The table may not have duplicate rows,
//! and the values in the columns must be nullary constructors of the appropriate type
//! (thus excluding any unknown value).
//! (note: these rules are not enforced by the xmt-lib crate)
//!
//! The default value must be given if the set of tuples in the interpretation
//! does not cover the domain of the function;
//! it may not be given otherwise.
//!
//!
//! ## (x-ground)
//!
//! Use `(x-ground)` to ground the pending assertions,
//! i.e., to expand the finite quantifications in them,
//! taking into account the known interpretations.
//! Quantifications over infinite domains remain unchanged.
//!
//! The grounding of assertions is delayed until requested.
//! It is thus possible to make assertions,
//! then to give the interpretations of symbols,
//! and then to ground the assertions using those interpretations.
//!
//! Note that `(check-sat)` grounds any pending assertions,
//! making a prior call to `x-ground` unnecessary.
//!
//!
//!
//! # Command-line interface
//!
//!
//! The following examples show how to use xmt-lib to flag triangles in a graph, i.e. to assert:
//!
//! `∀ x,y,z: Edge(x,y) and Edge(y,z) and Edge(z, x) => RedTriangle(x, y, z).`
//!
//! * Install the Rust toolchain using [rustup](https://rustup.rs/).
//! * Install [z3](https://github.com/Z3Prover/z3) so that `z3` is in your `PATH`
//! * Download the xmtlib repository.
//! * Create a `Triangle.xmt` file with the following xmt-lib content:
//!
//! ```text
//!     (set-option :backend none)
//!     (declare-fun Edge (Int Int) Bool)
//!     (declare-fun RedTriangle (Int Int Int) Bool)
//!     (x-interpret-pred Edge
//!         (x-set
//!             (1 2)
//!             (2 3)
//!             (1 3)
//!         )
//!     )
//!     (assert (forall ((x Int) (y Int) (z Int))
//!                 (=> (and (Edge x y) (Edge y z) (Edge x z))
//!                     (RedTriangle x y z)
//!                 )))
//!     (check-sat)  ; implicitly runs (x-ground)
//! ```
//!
//! * In the xmtlib directory, run `cargo run --release -- path/to/Triangle.xmt`
//!
//! Note: If the Rust toolchain [cannot find `z3.h`](https://github.com/prove-rs/z3.rs/tree/master/z3-sys#finding-z3-libraries),
//! modify the last line in the `Cargo.toml` file in the xmtlib directory to:
//!
//! ```text
//! z3 = { version = "0.8.1", features = ["static-link-z3"] }
//! ```
//! and re-run the `cargo` command (it will take a few minutes).
//!
//! The program will output the translation to SMT-Lib 2.6:
//! ```text
//! (declare-fun Edge (Int Int) Bool)
//! (declare-fun RedTriangle (Int Int Int) Bool)
//! (assert (RedTriangle 1 2 3))
//! (check-sat)
//! ```
//!
//! The grounding of the assertion is simply `(assert (RedTriangle 1 2 3))`,
//! once the interpretation of Edge is taken into account.
//!
//! To check satisfiability, submit the output to a SMT solver,
//! or replace the first line of Triangle.xmt with:
//!
//! ```text
//!    (set-option :backend Z3)
//! ```
//!

mod ast;
pub mod error;
mod grammar;
pub mod solver;
mod private;
