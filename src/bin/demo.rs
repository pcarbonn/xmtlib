// Copyright Pierre Carbonnelle, 2025.

// cargo run --release --bin demo

//! This file examplifies the use of `xmt-lib` as a crate.
//! (Click Source to view the source code)


use std::time::Instant;

use xmt_lib::solver::Solver;

fn main() -> () {

    let start = Instant::now();

    let connection = None;
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

    let solving = Instant::now();
    println!("Duration: {:?}", solving.duration_since(start));

}