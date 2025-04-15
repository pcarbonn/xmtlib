# xmtlib

`xmt-lib` denotes:

* a powerful language for interacting with [SMT](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers;
* a program that executes commands in that language;
* a program that translates from that language to [SMT-Lib 2.6](https://smt-lib.org/language.shtml) for use with SMT solvers.

The program can be used to solve configuration problems and perform various reasoning tasks with knowledge represented in logical forms.  Of note, the `xmt-lib` program has a fast "grounder" based on the [sqlite](https://sqlite.org) relational database engine.

xmt-lib extends the SMT-Lib 2.6 language with the following commands:

* `set-option :backend none` for translation to SMT-Lib-2, or `set-option :backend Z3` for execution with Z3 solver.
* `x-interpret-pred`, to specify the interpretation of a boolean function.  E.g., `(x-interpret-pred edge (x-set (a b) (b c) (c a)) )`
* `x-interpret-fun`, to specify the intepretation of a function symbol.  E.g., `(x-interpret-fun length ( ((a b) 2) ((b c) 3) ((c a) 4) ) 999)`
* `x-ground`, to ground the previous assertions, i.e., to expand the finite quantifications, taking into account the known interpretations.

It supports the Core, Int and Real [theories of SMT-Lib](https://smt-lib.org/theories.shtml).
