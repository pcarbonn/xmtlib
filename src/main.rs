// Copyright Pierre Carbonnelle, 2025.

pub mod ast;
pub mod error;
pub mod grammar;
pub mod solver;
mod private;

use std::fs;
use std::path::PathBuf;

use clap::Parser;

use crate::solver::Solver;

/// A high-level language for interacting with SMT solvers
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the problem file in XMT-Lib format.
    file_path: PathBuf,
}

fn main() {
    let args = Cli::parse();

    if args.file_path.exists() {
        let source = fs::read_to_string(args.file_path).unwrap();
        let mut solver = Solver::new(None);
        let results = solver.parse_and_execute(&source);
        for result in results {
            print!("{}", result);
        }
    } else {
        eprintln!("Error: File '{:?}' does not exist.", args.file_path);
        std::process::exit(1);
    }
}


#[cfg(test)]
mod tests {
    use std::fs::File;

    use simplelog::*;
    use crate::solver::Solver;

    fn tester(source: &str, output: &str) {
        let mut solver = Solver::new(None);
        let results = solver.parse_and_execute(source);
        assert_eq!(results.into_iter().collect::<Vec<_>>().join(""), output);
    }

    #[test]
    fn sandbox() {
        let config = ConfigBuilder::new()
            .set_time_level(LevelFilter::Off)
            .build();
        let _ = WriteLogger::init(LevelFilter::Trace, config, File::create("xmtlib.log").unwrap());

        tester( "(assert false)
            (check-sat)",

        "unsat\n"
        );
    }
}