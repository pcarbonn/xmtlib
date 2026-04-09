

**xmt-lib** is a high-performance tool designed to solve configuration and combinatorial problems through a fast, declarative approach.

It serves as a powerful alternative to standard [SMT solvers](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories) like [Z3](https://github.com). While the standard **SMT-LIB** language is declarative but often slow, and the **Z3 API** is fast but requires complex custom code, **xmt-lib** bridges this gap by offering both speed and ease of use.

### Key Features

*   **Universal Front-End:** xmt-lib can be used as a front-end to **any SMT-LIB compliant solver**, bringing its benefits to your preferred engine.
*   **Superior Performance:** xmt-lib outperforms standard SMT solvers when the interpretation of specific vocabulary symbols is already defined, as in configuration problems.
*   **SQLite-Powered Grounding:** This speed is driven by a specialized "grounder" built on the [SQLite](https://sqlite.org) relational database engine. This architecture also allows xmt-lib to directly access and process data stored in SQLite databases.
*   **Mathematical Foundation:** The grounding mechanism is detailed in this [arXiv research paper](https://arxiv.org/pdf/2602.19102).
*   **Extended Standard:** The program executes commands in **XMT-Lib**, an extension of the [SMT-LIB 2.6](https://smt-lib.org) standard designed for efficient communication with SMT solvers.


> [!WARNING]
> This public repository is old and not maintained.
> The new repository can be accessed after [purchasing a subscription](https://buy.polar.sh/polar_cl_ub1HJhijqGxblzSfpoTqHwZcakbDdrp8JRnf81enMRT) on polar.sh.
> Alternatively, you can use [xmt-lib online](https://pcarbonn.github.io/XMT-IDE) and access [its documentation](https://pcarbonn.github.io/XMT-doc).

XMT-lib extends the [SMT-Lib 2.6](https://smt-lib.org/language.shtml) language with the following commands:

* `set-option :backend` to specify the SMT solver (if any) used to execute the xmt-lib commands;
* `x-interpret-const`, to specify the interpretation of a constant;
* `x-interpret-pred`, to specify the interpretation of a boolean function symbol;
* `x-interpret-fun`, to specify the interpretation of a function symbol;
* `x-ground`, to ground assertions, i.e., to expand the quantifications in the submitted assertions,
  taking into account the known interpretations.

xmt-lib supports the Core, Int and Real [theories of SMT-Lib](https://smt-lib.org/theories.shtml).
Future extensions of the language are expected to provide more expressivity and reasoning capabilities:

- [ ] partial functions
- [ ] aggregates
- [ ] inductive definitions
- [ ] intensional logic
- [ ] more reasoning tasks

XMT-lib is inspired by the [FO(.)](https://fo-dot.readthedocs.io/en/latest/FO-dot.html) language
and [IDP-Z3](https://www.idp-z3.be/) reasoning engine developed by KU Leuven.

# Usage

We consider the following statement in a graph problem:

`∀ x,y,z: Edge(x,y) and Edge(y,z) and Edge(z, x) => Triangle(x, y, z).`

* Install [z3](https://github.com/Z3Prover/z3) so that `z3` is in your `PATH`;
* create a Rust project in a directory, [using cargo](https://doc.rust-lang.org/book/ch01-03-hello-cargo.html);
* add `xmt-lib = "<insert the current version>"` to its `cargo.toml` file, e.g. `xmt-lib = "0.1.0"`;
* create `main.rs` with the source code listed below;
* run `cargo run --release`

```
// main.rs
use xmt_lib::solver::Solver;

fn main() -> () {
    let connection = None;  // i.e., do not use a pre-existing sqlite database
    let mut solver = Solver::new(connection);
    let commands = r#"
        (set-option :backend none)
        (declare-fun Edge (Int Int) Bool)
        (declare-fun Triangle (Int Int Int) Bool)
        (x-interpret-pred Edge
            (x-set
                (1 2)
                (2 3)
                (1 3)
            )
        )
        (assert (forall ((x Int) (y Int) (z Int))
                    (=> (and (Edge x y) (Edge y z) (Edge x z))
                        (Triangle x y z)
                    )))
        (x-ground)
    "#;
    let results = solver.parse_and_execute(&commands);
    for result in results {
        print!("{}", result);
    }
}
```

If the Rust toolchain [cannot find `z3.h`](https://github.com/prove-rs/z3.rs/tree/master/z3-sys#finding-z3-libraries),
change the xmt-lib line in your Cargo.toml file to:

```text
xmt-lib = [version = "<insert the current version>", features = ["static-link-z3"]]
```

Executing the code will yield the output below:

```text
(declare-fun Edge (Int Int) Bool)
(declare-fun Triangle (Int Int Int) Bool)
(assert (Triangle 1 2 3))
```

To check satisfiability of the formula, replace the first line of the xmt-lib code by:

```text
        (set-option :backend Z3)
```

and `(x-ground)` by `(check-sat)` in the last line.
Running the program will now yield `sat`, meaning that the formula is satisfiable.
You can obtain an interpretation of `Triangle` satisfying the formula
using the `get-model` and `get_value` commands of [SMT-Lib 2.6](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf).
Every command of SMT-Lib 2.6 are supported.

# Benefits

To represent the `x-interpret-pred` command above in pure SMT-Lib,
one would have to use a function definition (or an equivalent assertion):

```text
(define-fun Edge ((x Int) (y Int)) Bool
    (or (and (= x 1) (= y 2))
        (and (= x 2) (= y 3))
        (and (= x 1) (= y 3))
    ))
```

However, this approach does not scale well.
It takes more than 1 minute to verify satisfiability for a graph with 200 nodes and 200 triangles with SMT-Lib,
but only 30 ms with xmt-lib (and 300 ms for 10,000 nodes and triangles).

Another approach is to use a finite domain for Node (instead of Int),
to expand the quantification over that domain using a procedural programming language,
and to simplify the resulting expression using the known interpretation of `Edge`.
This also does not scale well, unless sophisticated grounding algorithms are used.

Another benefit is that it is possible for xmt-lib to directly read data in a sqlite database, using `(x-sql`.

