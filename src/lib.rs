// cargo watch -x "doc --no-deps"

//! xmt-lib denotes:
//! * a powerful language for interacting with [SMT](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers;
//! * a program that executes commands in that language;
//! * a program that translates from that language to
//! [SMT-Lib 2.6](https://smt-lib.org/language.shtml)
//! for use with SMT solvers;
// !todo * a rust library that executes or translates xmt-lib commands.
//!
//! The program can be used to find (optimal) solutions of configuration problems
//! and perform various reasoning tasks with knowledge represented in logical forms.
//! Of note, the xmt-lib program has a fast "grounder"
//! based on the [sqlite](https://sqlite.org) relational database engine.
//!
//! xmt-lib extends the SMT-Lib 2.6 language with the following commands:
//!
//! * `set-option :backend` to specify the SMT solver (if any) used to execute the SMT-Lib 2.6 commands.
//! * `x-interpret-pred`, to specify the interpretation of a boolean function symbol.
//! * `x-interpret-fun`, to specify the interpretation of a function symbol.
//! * `x-ground`, to ground assertions, i.e., to expand the finite quantifications,
//! taking into account the known interpretations.
//!
//! It supports the Core, Int and Real [theories of SMT-Lib](https://smt-lib.org/theories.shtml).
//!
//!
//! # Usage
//!
//! The following examples show how to use xmt-lib to flag triangles in a graph, i.e. to assert:
//!
//! `∀ x,y,z: Edge(x,y) and Edge(y,z) and Edge(z, x) => RedTriangle(x, y, z).`
//!
//! * Install the Rust toolchain using [rustup](https://rustup.rs/).
//! * Install [z3](https://github.com/Z3Prover/z3) so that `z3` is in your `PATH`
//! * Download the xmt-lib repository.
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
//! * In the xmt-lib directory, run `cargo run --release -- path/to/Triangle.xmt`
//!
//! Note: If the Rust toolchain cannot find Z3,
//! modify the last line in the `Cargo.toml` file in the xmt-lib directory to:
//!
//! ```text
//! z3 = { version = "0.24", features = ["static-link-z3"] }
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

// todo: use as a rust library

//!
// ! # Example
// !
// ! This example shows how to use xmt-lib to flag triangles in a graph, i.e. to assert:
// !
// ! `∀ x,y,z: Edge(x,y) and Edge(y,z) and Edge(z, x) => RedTriangle(x, y, z).`
// !
// ! ```
// ! use xmtlib::solver::Solver;
// ! let mut solver = Solver::default();
// ! let commands = r#"
// !     (set-option :backend none)
// !     (declare-fun Edge (Int Int) Bool)
// !     (declare-fun RedTriangle (Int Int Int) Bool)
// !     (x-interpret-pred Edge
// !         (x-set
// !             (1 2)
// !             (2 3)
// !             (1 3)
// !         )
// !     )
// !     (assert (forall ((x Int) (y Int) (z Int))
// !                 (=> (and (Edge x y) (Edge y z) (Edge x z))
// !                     (RedTriangle x y z)
// !                 )))
// !     (check-sat)  ; implicitly runs (x-ground)
// ! "#;
// ! let results = solver.parse_and_execute(&commands);
// ! for result in results {
// !     print!("{}", result);
// ! }
// ! ```
// ! Output:
// ! ```text
// ! (declare-fun Edge (Int Int) Bool)
// ! (declare-fun RedTriangle (Int Int Int) Bool)
// ! (assert (RedTriangle 1 2 3))
// ! (check-sat)
// ! ```
// !

//!
//!
//! # New commands
//!
//! Note that, unlike SMT-Lib 2.6, but like the Z3 solver,
//! xmt-lib accepts negative numbers in terms (e.g., `-1` is accepted for `(- 1)`).
//!
//! ## (set-option :backend
//!
//! This command has the following variants:
//!
//! * `set-option :backend none` to obtain the translation of xmt-lib commands to SMT-Lib 2.6;
//! * `set-option :backend Z3` for immediate execution of commands by a Z3 solver.
//!
//!
//! ## (x-interpret-pred
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
//! For a proposition `p` (aka a boolean function of arity 0), the interpretation can be given as :
//!
//! * `(x-interpret-pred p (x-set ()) )` if `p` is true;
//! * `(x-interpret-pred p (x-set   ) )` if `p` is false;
//!
//! Unlike an assertion about the value of a proposition,
//! the interpretation of a proposition is used to simplify the grounding.
//!
//! Note that a model of the assertions (obtained by `(get-model)`)
//! will not have any information about interpreted predicate symbols.
//! So, in our example, `(Edge a b)` may have any value in a model.
//!
//!
//! ## (x-interpret-fun
//!
//! An `x-interpret-fun` command specifies the interpretation of a function symbol, possibly partially,
//! by associating a value to tuples of arguments, and by giving a default value.
//! (The interpretation of a function with an infinite domain cannot be given)
//!
//! Example: `(x-interpret-fun Length (x-mapping ((a b) 2) ((b c) 3) ((c a) 4) ) 999)`.
//! The length of pair `(a b)` is 2, of `(b c)` is 3, of `(c a)` is 4,
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
//! The interpretation of a constant `c` (i.e., a function of arity 0) is given in the default value,
//! e.g., `(x-interpret-fun Length c (x-mapping ) 1)`.
//!
//! Note that a model (obtained by `(get-model)`)
//! will not have any information about function symbols
//! that have been given in the interpretation.
//! (In our triangle example above,
//! the `Edge` function is not constrained by any assertions,
//! and can thus have any interpretation in a model)
//!
//!
//! ## (x-ground
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
//! Note that `(check-sat)` grounds any pending assertions.
//!
//!
//! # API
//!
//! The programmable interface of xmt-lib is text based: commands are sent as strings,
//! not as objects constructed in memory.
//! This is similar to the approach used in interfaces for the web (HTML) and relational databases (SQL).
//! We believe this is an acceptable compromise between performance and simplicity.
//! Should we be wrong, we can easily make the memory-based API public.
//!

mod api;
pub mod error;
mod grammar;
pub mod solver;
mod private;
