// Copyright Pierre Carbonnelle, 2025.

use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

use xmtlib::solver::Solver;


#[test]
fn test_all_smt2_files() {
    let test_dir = Path::new("tests");
    for entry in fs::read_dir(test_dir).expect("read_dir call failed") {
        if let Ok(entry) = entry {
            let path = entry.path();
            if path.is_file() {
                if let Some(extension) = path.extension() {
                    if extension == "smt2" {
                        if let Some(file_name) = path.file_name().and_then(|n| n.to_str()) {
                            test_file(file_name);
                        }
                    }
                }
            }
        }
    }
}


fn test_file(file_name: &str) {

    // read file
    let input_path = Path::new("tests").join(file_name);
    let expected = fs::read_to_string(input_path.clone())
        .expect("Should have been able to read the input file");
    let input = expected.split("\n-------------------------\n").collect::<Vec<&str>>()[0];

    // execute file
    let mut solver = Solver::default();
    let results = solver.parse_and_execute(&input);
    let result = results.into_iter().collect::<Vec<_>>().join("\n");

    // compare to expected
    let actual = input.to_owned() + "\n-------------------------\n"+ &result;
    if actual != expected {  // write to file
        let mut expected_file = File::create(input_path).expect("creation failed");
        expected_file.write(actual.as_bytes(),).expect("write failed");
    }
    assert_eq!(actual, expected);

}