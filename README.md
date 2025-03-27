# xmtlib

A high-level language for interacting with SMT solvers.

Based on SMT-Lib, it adds the followinge extensions:

* `x-interpret-pred`, to specify the interpretation of a boolean function.  E.g., `(x-interpret-pred edge (a b) (b c) (c a) )`
* `x-interpret-fun`, to specify the intepretation of a function symbol.  E.g., `(x-interpret-fun length ( ((a b) 2) ((b c) 3) ((c a) 4) ) 999)`
