// cargo watch -x "doc --no-deps"

#![doc = include_str!("../README.md")]


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
//! The `x-interpret-pred` command is used to specify the total interpretation of a boolean function symbol (aka a predicate),
//! by listing all the tuples of arguments that make it true.
//! Such an interpretation can be given only once.
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
//! The `x-interpret-fun` command is used to specify the interpretation of a function symbol.
//! If the domain of the function is finite, its interpretation is specified
//! by mapping a value to some tuples of arguments in its domain,
//! and by giving a default value for the remaining tuples in its domain.
//! If the domain of the function is infinite, but its "domain of definition" is finite
//! (i.e., the domain where its value is meaningful and relevant for the problem at hand),
//! its interpretation is given by mapping a value to all tuples of arguments in its domain of definition.
//! If the domain of definition of the function is infinite,
//! one cannot specify its interpretation with this command:
//! the SMT-Lib `(define-fun` command must be used instead.
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
//! The default value may be `? `(for unknown).
//! It may only be given for functions with finite domain
//! when the set of tuples in the interpretation does not cover the domain;
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
