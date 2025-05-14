// Copyright Pierre Carbonnelle, 2025.

// cargo run --release --bin triangle

//! This file examplifies the use of `xmt-lib` as a crate.
//! (Click Source to view the source code)


use std::time::Instant;

use rusqlite::{Connection, params};

use xmt_lib::solver::Solver;

fn main() -> Result<(), Box<dyn std::error::Error>> {

    let n = 200+1;

    let start = Instant::now();



    // Data load
    let conn = Connection::open_in_memory().unwrap();
    conn.execute("CREATE TABLE Edges (a_1 INTEGER, a_2 INTEGER, PRIMARY KEY (a_1, a_2))", ())?;

    {
        let mut stmt = conn.prepare("INSERT INTO Edges (a_1, a_2) VALUES (?, ?)")?;
        for i in 1..n {
            for j in 1..4 {
                if i+j < n {
                    stmt.execute(params![format!("{i}"), format!("{}", i+j)])?;
                }
            }
        }
    }
    let data_load = Instant::now();
    println!("Data load: {:?}", data_load.duration_since(start));


    // Declarations
    let mut solver = Solver::new(Some(conn));
    let execute = |solver: &mut Solver, commands: &str| {
        let results = solver.parse_and_execute(&commands);
        for _result in results {
            //print!("{}", _result);
        }
    };

    execute(&mut solver, r#"
        (set-option :backend Z3)
        (declare-fun Edge (Int Int) Bool)
        (declare-fun phi (Int Int Int) Bool)
        (x-interpret-pred Edge (x-sql "SELECT * FROM Edges"))
    "#);

    let declaration = Instant::now();
    println!("Declarations: {:?}", declaration.duration_since(data_load));


    // Grounding
    execute(&mut solver, r#"
        (assert (forall ((x Int) (y Int) (z Int))
                    (=> (and (Edge x y) (Edge y z) (Edge x z))
                            (phi x y z)
                    )))
        (x-ground debug:)
    "#);
    let grounding = Instant::now();
    println!("Grounding: {:?}", grounding.duration_since(declaration));


    // Solving
    execute(&mut solver, "(check-sat)");
    let solving = Instant::now();
    println!("Solving: {:?}", solving.duration_since(grounding));

    println!("Total: {:?}", solving.duration_since(start));

    Ok(())
}