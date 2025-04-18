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


#[test] fn test_a_sorts_1()     { test_file(Path::new("tests/private/a_sorts_1.xmt")) }
#[test] fn test_a_sorts_2()     { test_file(Path::new("tests/private/a_sorts_2.xmt")) }
#[test] fn test_b_fun()         { test_file(Path::new("tests/private/b_fun.xmt")) }
#[test] fn test_c_term_const()  { test_file(Path::new("tests/private/c_term_const.xmt")) }
#[test] fn test_c_term_quant()  { test_file(Path::new("tests/private/c_term_quant.xmt")) }
#[test] fn test_d_interpret_1() { test_file(Path::new("tests/private/d_interpret_1.xmt")) }
#[test] fn test_d_interpret_fun_2() { test_file(Path::new("tests/private/d_interpret_fun_2.xmt")) }
#[test] fn test_d_interpret_partial() { test_file(Path::new("tests/private/d_interpret_partial.xmt")) }
#[test] fn test_e_ground()      { test_file(Path::new("tests/private/e_ground.xmt")) }
#[test] fn test_e_ground_comparison()   { test_file(Path::new("tests/private/e_ground_comparison.xmt")) }
#[test] fn test_e_ground_compound_1()      { test_file(Path::new("tests/private/e_ground_compound_1.xmt")) }
#[test] fn test_e_ground_compound_2()      { test_file(Path::new("tests/private/e_ground_compound_2.xmt")) }
#[test] fn test_e_ground_equality()     { test_file(Path::new("tests/private/e_ground_equality.xmt")) }
#[test] fn test_e_ground_arithmetic()     { test_file(Path::new("tests/private/e_ground_arithmetic.xmt")) }
#[test] fn test_e_ground_predef()     { test_file(Path::new("tests/private/e_ground_predef.xmt")) }

#[test] fn test_empty()         { test_file(Path::new("tests/empty.xmt")) }
#[test] fn test_sandbox()       { test_file(Path::new("tests/sandbox.xmt")) }
#[test] fn test_triangle_int()  { test_file(Path::new("tests/triangle Int.xmt")) }
#[test] fn test_triangle()      { test_file(Path::new("tests/triangle.xmt")) }


// #[test]
// fn test_all_xmt_files() {
//     let test_dir = Path::new("tests/benchmark");
//     all_xmt(test_dir)
// }

// // recursively test all .xmt files in the test directory and its subdirectories
// fn all_xmt(test_dir: &Path) {
//     for entry in fs::read_dir(test_dir).expect("read_dir call failed") {
//         if let Ok(entry) = entry {
//             let path = entry.path();
//             if path.is_file() {
//                 if let Some(extension) = path.extension() {
//                     if extension == "xmt" {
//                         test_file(&path)
//                     }
//                 }
//             } else if path.is_dir() {
//                 all_xmt(&path)
//             }
//         }
//     }
// }


fn test_file(path: &Path) {

    // read file
    let expected = fs::read_to_string(path)
        .expect("Should have been able to read the input file");
    let input = expected.split("\n-------------------------\n").collect::<Vec<&str>>()[0];

    // execute file
    let mut solver = Solver::default();
    let results = solver.parse_and_execute(&input);
    let result = results.into_iter().collect::<Vec<_>>().join("");

    // compare to expected
    let actual = input.to_owned() + "\n-------------------------\n"+ &result;
    if actual != expected {  // write to file
        let mut expected_file = File::create(path).expect("creation failed");
        expected_file.write(actual.as_bytes(),).expect("write failed");
    }
    assert_eq!(actual, expected);

}