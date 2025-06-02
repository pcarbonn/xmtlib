// Copyright Pierre Carbonnelle, 2025.

// to open overview of code coverage;
//    > cargo llvm-cov --open
// to view coverage in one file in VS Code
//    > cargo llvm-cov --lcov --output-path ./target/lcov.info
//    then, open file, ctrl-Shift-P, Coverage, Display (a bit slow !)


use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

use xmt_lib::solver::Solver;


#[test] fn test_sandbox()      {
    assert!(test_file(Path::new("tests/sandbox.xmt")));
}


#[test]
fn test_all_xmt_files() {
    let test_dir = Path::new("tests");
    let mut failures: Vec<String> = vec![];
    all_xmt(test_dir, &mut failures);
    let empty: Vec<String> = vec![];
    assert_eq!(failures, empty);
}

// recursively test all .xmt files in the test directory and its subdirectories
fn all_xmt(test_dir: &Path, failures: &mut Vec<String>) {
    for entry in fs::read_dir(test_dir).expect("read_dir call failed") {
        if let Ok(entry) = entry {
            let path = entry.path();
            if path.is_file() {
                if let Some(extension) = path.extension() {
                    if extension == "xmt" {
                        if ! test_file(&path) {
                            failures.push(path.file_name().unwrap().to_str().unwrap().to_string())
                        }
                    }
                }
            } else if path.is_dir() {
                all_xmt(&path, failures)
            }
        }
    }
}


fn test_file(path: &Path) -> bool {

    // read file
    let expected = fs::read_to_string(path)
        .expect("Should have been able to read the input file");
    let input = expected.split("\n------- RESULTS ------------------\n").collect::<Vec<&str>>()[0];

    // execute file
    let panic = std::panic::catch_unwind(|| {
        let mut solver = Solver::new(None);
        let results = solver.parse_and_execute(&input);
        let result = results.into_iter().collect::<Vec<_>>().join("");
        result
    });
    if let Ok(result) = panic {
        // compare to expected
        let actual = input.to_owned() + "\n------- RESULTS ------------------\n"+ &result;
        if actual != expected {  // write to file
            let mut expected_file = File::create(path).expect("creation failed");
            expected_file.write(actual.as_bytes(),).expect("write failed");
        }
        actual == expected
    } else {
        false
    }
}