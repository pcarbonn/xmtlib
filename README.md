# xmtlib

A high-level language for interacting with SMT solvers.

Based on SMT-Lib 2.6, it adds the following extensions:

* `set-option :backend None` for translation to SMT-Lib-2, or `set-option :backend Z3` for execution with Z3 solver.
* `x-interpret-pred`, to specify the interpretation of a boolean function.  E.g., `(x-interpret-pred edge (a b) (b c) (c a) )`
* `x-interpret-fun`, to specify the intepretation of a function symbol.  E.g., `(x-interpret-fun length ( ((a b) 2) ((b c) 3) ((c a) 4) ) 999)`
* `x-ground`, to ground the previous assertions, i.e., to expand the finite quantifications, taking into account the known interpretations.


Note that, unlike SMT-Lib 2.6, but like the Z3 solver, we accept negative numbers in terms (e.g., `-1` is `(- 1)`).
