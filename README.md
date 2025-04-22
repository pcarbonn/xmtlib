
THIS IS NOT READY FOR RELEASE YET !

xmt-lib denotes:
* an expressive language for interacting with [SMT](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers;
* a program that executes commands in that language.

They are inspired by the [FO(.)](https://fo-dot.readthedocs.io/en/latest/FO-dot.html) language
and [IDP-Z3](https://www.idp-z3.be/) reasoning engine developed by KU Leuven.

The program can be used to find (optimal) solutions of combinatorial/configuration problems
and perform various reasoning tasks with knowledge represented in logical forms.
Of note, the xmt-lib program has a fast "grounder"
based on the [sqlite](https://sqlite.org) relational database engine.
The program can be called by another program (API interface) and can run standalone (CLI interface).

xmt-lib extends the [SMT-Lib 2.6](https://smt-lib.org/language.shtml) language with the following commands:

* `set-option :backend` to specify the SMT solver (if any) used to execute the xmt-lib commands;
* `x-interpret-const`, to specify the interpretation of a constant;
* `x-interpret-pred`, to specify the interpretation of a boolean function symbol;
* `x-interpret-fun`, to specify the interpretation of a function symbol;
* `x-ground`, to ground assertions, i.e., to expand the finite quantifications,
taking into account the known interpretations.

It supports the Core, Int and Real [theories of SMT-Lib](https://smt-lib.org/theories.shtml).

Future developments include support for more expressivity:
- [ ] partial functions
- [ ] aggregates
- [ ] inductive definitions
- [ ] intensional logic
- [ ] more reasoning tasks