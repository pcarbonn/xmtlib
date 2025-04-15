// Copyright Pierre Carbonnelle, 2025.

// cargo run --release --bin triangle

use std::time::Instant;

use rusqlite::params;

use xmtlib::solver::Solver;

fn execute(solver: &mut Solver, commands: &str) -> () {
    let results = solver.parse_and_execute(&commands);
    for _result in results {
        //print!("{}", _result);
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let n = 8000+1;

    let start = Instant::now();
    let mut solver = Solver::default();

    execute(&mut solver, format!(r#"
        (set-option :backend none)
        (declare-fun Edge (Int Int) Bool)
        (declare-fun phi (Int Int Int) Bool)
        (x-interpret-pred Edge (x-set ))
    "#).as_str());

    let declaration = Instant::now();
    println!("Declarations: {:?}", declaration.duration_since(start));

    {
        let mut stmt = solver.conn.prepare("INSERT INTO _xmt_edge_T (a_0, a_1) VALUES (?, ?)")?;
        for i in 1..n {
            for j in 1..4 {
                if i+j < n {
                    stmt.execute(params![format!("{i}"), format!("{}", i+j)])?;
                }
            }
        }
    }
    let data_entry = Instant::now();
    println!("Data entry: {:?}", data_entry.duration_since(declaration));

    let source = r#"
        (assert (forall ((x Int) (y Int) (z Int))
                    (=> (and (Edge x y) (Edge y z) (Edge x z))
                            (phi x y z)
                    )))
        (x-ground)
    "#;
    execute(&mut solver, source);
    let grounding = Instant::now();
    println!("Grounding: {:?}", grounding.duration_since(data_entry));

    execute(&mut solver, "(check-sat)");
    let solving = Instant::now();
    println!("Solving: {:?}", solving.duration_since(grounding));

    println!("Total: {:?}", solving.duration_since(start));

    Ok(())
}