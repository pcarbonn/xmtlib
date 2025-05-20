// cargo watch -x "doc --no-deps"

//!
//! xmt-lib denotes:
//! * an extension of the [SMT-Lib 2.6](https://smt-lib.org/language.shtml) language
//!   to communicate with [SMT](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers;
//! * a program that executes commands in that language.
//!
//! The program can be used to find (optimal) solutions of combinatorial/configuration problems.
// and perform various reasoning tasks with knowledge represented in logical forms.
//! It is faster than standard SMT solvers for the model expansion task,
//! i.e., the task of finding a model of a logic formula
//! when the interpretation of some symbols of the vocabulary is already known.
//! This performance gain comes from using a fast "grounder"
//! based on the [sqlite](https://sqlite.org) relational database engine.
//! This grounder also allows xmt-lib to access data stored in a sqlite database.
// The program can be called by another program (API interface) and can run standalone (CLI interface).
//!
//! xmt-lib extends the [SMT-Lib 2.6](https://smt-lib.org/language.shtml) language with the following commands:
//!
//! * `set-option :backend` to specify the SMT solver (if any) used to execute the xmt-lib commands;
//! * `x-interpret-const`, to specify the interpretation of a constant;
//! * `x-interpret-pred`, to specify the interpretation of a boolean function symbol;
//! * `x-interpret-fun`, to specify the interpretation of a function symbol;
//! * `x-ground`, to ground assertions, i.e., to expand the quantifications in the submitted assertions,
//! taking into account the known interpretations.
//!
//! xmt-lib supports the Core, Int and Real [theories of SMT-Lib](https://smt-lib.org/theories.shtml).
//! Future extensions of the language are expected to provide more expressivity and reasoning capabilities:
//! - [ ] partial functions
//! - [ ] aggregates
//! - [ ] inductive definitions
//! - [ ] intensional logic
//! - [ ] more reasoning tasks
//!
//!
//! xmt-lib is inspired by the [FO(.)](https://fo-dot.readthedocs.io/en/latest/FO-dot.html) language
//! and [IDP-Z3](https://www.idp-z3.be/) reasoning engine developed by KU Leuven.

//!
//! # Usage
//!
//! We consider the following statement in a graph problem:
//!
//! `∀ x,y,z: Edge(x,y) and Edge(y,z) and Edge(z, x) => Triangle(x, y, z).`
//!
//! * Install [z3](https://github.com/Z3Prover/z3) so that `z3` is in your `PATH`;
//! * create a Rust project in a directory, [using cargo](https://doc.rust-lang.org/book/ch01-03-hello-cargo.html);
//! * add `xmt-lib = "<insert the current version>"` to its `cargo.toml` file, e.g. `xmt-lib = "0.1.0"`;
//! * create `main.rs` with the source code listed below;
//! * run `cargo run --release`
//!
//! ```
//! // main.rs
//! use xmt_lib::solver::Solver;
//!
//! fn main() -> () {
//!     let connection = None;  // i.e., do not use a pre-existing sqlite database
//!     let mut solver = Solver::new(connection);
//!     let commands = r#"
//!         (set-option :backend none)
//!         (declare-fun Edge (Int Int) Bool)
//!         (declare-fun Triangle (Int Int Int) Bool)
//!         (x-interpret-pred Edge
//!             (x-set
//!                 (1 2)
//!                 (2 3)
//!                 (1 3)
//!             )
//!         )
//!         (assert (forall ((x Int) (y Int) (z Int))
//!                     (=> (and (Edge x y) (Edge y z) (Edge x z))
//!                         (Triangle x y z)
//!                     )))
//!         (x-ground)
//!     "#;
//!     let results = solver.parse_and_execute(&commands);
//!     for result in results {
//!         print!("{}", result);
//!     }
//! }
//! ```
//!
//! If the Rust toolchain [cannot find `z3.h`](https://github.com/prove-rs/z3.rs/tree/master/z3-sys#finding-z3-libraries),
//! change the xmt-lib line in your Cargo.toml file to:
//!
//! ```text
//! xmt-lib = [version = "<insert the current version>", features = ["static-link-z3"]]
//! ```
//!
//! Executing the code will yield the output below:
//!
//! ```text
//! (declare-fun Edge (Int Int) Bool)
//! (declare-fun Triangle (Int Int Int) Bool)
//! (assert (Triangle 1 2 3))
//! ```
//!
//!
//! To check satisfiability of the formula, replace the first line of the xmt-lib code by:
//!
//! ```text
//!         (set-option :backend Z3)
//! ```
//!
//! and `(x-ground)` by `(check-sat)` in the last line.
//! Running the program will now yield `sat`, meaning that the formula is satisfiable.
//! You can obtain an interpretation of `Triangle` satisfying the formula
//! using the `get-model` and `get_value` commands of [SMT-Lib 2.6](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf).
//! Every command of SMT-Lib 2.6 are supported.
//!
//!
//!
//! # Benefits
//!
//! To represent the `x-interpret-pred` command above in pure SMT-Lib,
//! one would have to use a function definition (or an equivalent assertion):
//!
//! ```text
//! (define-fun Edge ((x Int) (y Int)) Bool
//!     (or (and (= x 1) (= y 2))
//!         (and (= x 2) (= y 3))
//!         (and (= x 1) (= y 3))
//!     ))
//! ```
//!
//! However, this approach does not scale well.
//! It takes more than 1 minute to verify satisfiability for a graph with 200 nodes and 200 triangles with SMT-Lib,
//! but only 30 ms with xmt-lib (and 300 ms for 10,000 nodes and triangles).
//!
//! Another approach is to use a finite domain for Node (instead of Int),
//! to expand the quantification over that domain using a procedural programming language,
//! and to simplify the resulting expression using the known interpretation of `Edge`.
//! This also does not scale well, unless sophisticated grounding algorithms are used.
//!
//! Another benefit is that it is possible for xmt-lib to directly read data in a sqlite database, using `(x-sq`.
//!
//!
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
//!
//! A solver instance has a connection to a sqlite database used for grounding assertions.
//! This database can be pre-loaded with data describing the interpretation of symbols,
//! as examplified in the [triangle crate](../triangle/index.html).
//! The interpretation of a symbol can then be specified using the `(x-sql` construct, as described further below.
//!
//! The new commands introduced by xmt-lib are listed below.
//! Note that, unlike SMT-Lib 2.6, but like the Z3 solver,
//! xmt-lib accepts negative numbers in terms (e.g., `-1` is accepted for `(- 1)`).
//!
//!
//! ## (set-option :backend ...)
//!
//! This command has the following variants:
//!
//! * `set-option :backend none` to obtain the translation of xmt-lib commands to SMT-Lib 2.6;
//! * `set-option :backend Z3` for immediate execution of translated commands by a Z3 solver.
//!
//! By default, the backend is Z3.
//! It can only be changed at the start of a session.
//!
//!
//! ## (x-interpret-const ...)
//!
//! An `x-interpret-const` command specifies the interpretation of a constant.
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
//! This list of tuples can be supplied using:
//!
//! * `(x-set`, e.g., `(x-interpret-pred Edge (x-set (a b) (b c) (c a)) )`.
//! The only pairs of nodes that satisfy the `Edge` predicate are `(a b)`, `(b c)`, and `(c a)`.
//!
//! * `(x-sql "SELECT .. FROM ..")`.
//! The SELECT is run using the sqlite connection of the solver.
//! The SELECT must return `n` columns named `a_0, .. a_n`
//! where `n` is the arity of the symbol being interpreted.
//! These columns must be of type INTEGER for integers, REAL for reals, and TEXT otherwise,
//! and contain nullary constructors.
//!
//! * `(x-range`, e.g., `(x-interpret-pred Row (x-range 1 8) )`.
//! The values making Row true are 1, 2, 3, 4, 5, 6, 7, 8.
//! The set is the (union of) interval with inclusive boundaries.
//! This can only be used for unary predicates over Int.
//!
//! The list of tuples may not have duplicate tuples,
//! and the values in the tuples must be of the appropriate type for the predicate.
//!
//! Note that the data integrity rules are not enforced for the `(x-sql` variant.
//!
//! Note that interpreted predicates may take any value in a model obtained by `(get-model)`.
//! So, in our first example, `(Edge 1 1)` may have any value in a model.
//!
//!
//! ## (x-interpret-fun ...)
//!
//! An `x-interpret-fun` command specifies the interpretation of a function symbol, possibly partially,
//! by mapping a value to tuples of arguments, and by giving a default value.
//! (The interpretation of a function with an infinite domain cannot be given)
//!
//! The grammar for this command is:
//! ```text
//!     '(' 'x-interpret-fun' <symbol> <mappings> <default>? ')'
//! ```
//!
//! The mappings can be supplied using:
//!
//! * ``` `(` `x-mapping` ['(' <tuple> <value> ')']* `)` ```
//! where a tuple is a list of identifiers between parenthesis (e.g., `(a b)`),
//! and a value is an identifier or  `?` (for unknown value).
//! The list of identifiers must match the arity of the function symbol.
//! For example, `(x-mapping ((a b) 2) ((b c) ?) ((c a) 4) )`
//! maps `(a b)` to 2, `(b c)` to unknown, and `(c a)` to 4
//!
//! * `(x-sql "SELECT .. FROM ..")`
//! The SELECT is run using the sqlite connection of the solver.
//! The SELECT must return `n+1` columns named `a_0, .. a_n, G`
//! where `n` is the arity of the symbol being interpreted,
//! `a_0, .. a_n` contain the tuples of arguments, and `G` the corresponding known values.
//! These columns must be of type INTEGER for integers, REAL for reals, and TEXT otherwise.
//! The values in the mappings must be nullary constructors (thus excluding "?")
//! (note: this rule is not enforced by the xmtlib crate)
//!
//! The mappings may not have duplicate tuples,
//! and the values in the mapping must be of the appropriate type.
//!
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
//! Usage: xmt-lib <FILE_PATH>
//!
//! Arguments:
//! <FILE_PATH>  Path to the script file containing XMT-Lib commands.
//!
//! Options:
//! -h, --help     Print help
//! -V, --version  Print version
//!

mod ast;
pub mod error;
mod grammar;
pub mod solver;
mod private;
