// Copyright Pierre Carbonnelle, 2025.

use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

use xmtlib::solver::Solver;


#[test] fn test_a_sorts_1()     { test_file(Path::new("tests/private/a_sorts_1.smt2")) }
#[test] fn test_a_sorts_2()     { test_file(Path::new("tests/private/a_sorts_1.smt2")) }
#[test] fn test_b_fun()         { test_file(Path::new("tests/private/b_fun.smt2")) }
#[test] fn test_c_term_const()  { test_file(Path::new("tests/private/c_term_const.smt2")) }
#[test] fn test_c_term_quant()  { test_file(Path::new("tests/private/c_term_quant.smt2")) }
#[test] fn test_d_interpret_1() { test_file(Path::new("tests/private/d_interpret_1.smt2")) }
#[test] fn test_e_ground()      { test_file(Path::new("tests/private/e_ground.smt2")) }

#[test] fn test_empty()         { test_file(Path::new("tests/empty.smt2")) }
#[test] fn test_sandbox()       { test_file(Path::new("tests/sandbox.smt2")) }
#[test] fn test_triangle_int()  { test_file(Path::new("tests/triangle Int.smt2")) }
#[test] fn test_triangle()      { test_file(Path::new("tests/triangle.smt2")) }

// #[test]
// fn test_all_smt2_files() {
//     let test_dir = Path::new("tests");
//     all_smt2(test_dir)
// }

// recursively test all .smt2 files in the test directory and its subdirectories
// fn all_smt2(test_dir: &Path) {
//     for entry in fs::read_dir(test_dir).expect("read_dir call failed") {
//         if let Ok(entry) = entry {
//             let path = entry.path();
//             if path.is_file() {
//                 if let Some(extension) = path.extension() {
//                     if extension == "smt2" {
//                         test_file(&path)
//                     }
//                 }
//             } else if path.is_dir() {
//                 all_smt2(&path)
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
    let result = results.into_iter().collect::<Vec<_>>().join("\n");

    // compare to expected
    let actual = input.to_owned() + "\n-------------------------\n"+ &result;
    if actual != expected {  // write to file
        let mut expected_file = File::create(path).expect("creation failed");
        expected_file.write(actual.as_bytes(),).expect("write failed");
    }
    assert_eq!(actual, expected);

}