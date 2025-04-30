// Copyright Pierre Carbonnelle, 2025.

// cargo run --release --bin triangle

//! This files examplifies the use of `xmt-lib` as a crate.


use std::time::Instant;

use rusqlite::{Connection, params};

use xmt_lib::solver::Solver;

#[test]
fn main() -> Result<(), Box<dyn std::error::Error>> {

    let n = 5+1;

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

    let mut solver = Solver::new(Some(conn));

    // Declarations
    let execute = |solver: &mut Solver, commands: &str| {
        let results = solver.parse_and_execute(&commands);
        for _result in results {
            print!("{}", _result);
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
        (x-ground)
    "#);
    let grounding = Instant::now();
    println!("Grounding: {:?}", grounding.duration_since(declaration));


    // Solving
    execute(&mut solver, "(check-sat)");
    let solving = Instant::now();
    println!("Solving: {:?}", solving.duration_since(grounding));

    println!("Total: {:?}", solving.duration_since(start));

    // test of x-sql for functions
    execute(&mut solver, r#"
        (declare-datatype Color ( (red) (green) ))
        (declare-fun Strength (Color) Int)
        (x-interpret-fun Strength (x-sql "SELECT G as a_1, 1 as G from _xmt_color"))
        (assert (= (Strength red) 1))
        (x-ground)
        (check-sat)
    "#);

    Ok(())
}