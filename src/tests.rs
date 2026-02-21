use std::process::Command;
use std::str;

#[test]
fn test_variables_example() {
    let input_file = "examples/1_variables.fcy";
    let output_bin = "testbins/1_variables";

    let compile_status = Command::new("cargo")
        .args(&["run", "--", "input", input_file, "-o", output_bin])
        .status()
        .expect("Failed to run compiler command");

    assert!(
        compile_status.success(),
        "Compilation failed for {}",
        input_file
    );

    let run_output = Command::new(output_bin)
        .output()
        .expect("Failed to run compiled binary");

    assert!(
        run_output.status.success(),
        "Compiled program crashed"
    );

    let stdout = str::from_utf8(&run_output.stdout)
        .expect("Output is not valid UTF-8")
        .trim(); // remove trailing newline

    let expected = "\
9.859600
5
3
10.000000
27.500000";

    assert_eq!(stdout, expected, "Program output did not match expected");
}

#[test]
fn test_loops_example() {
    let input_file = "examples/2_loops.fcy";
    let output_bin = "testbins/2_loops";

    let compile_status = Command::new("cargo")
        .args(&["run", "--", "input", input_file, "-o", output_bin])
        .status()
        .expect("Failed to run compiler command");

    assert!(
        compile_status.success(),
        "Compilation failed for {}",
        input_file
    );

    let run_output = Command::new(output_bin)
        .output()
        .expect("Failed to run compiled binary");

    assert!(
        run_output.status.success(),
        "Compiled program crashed"
    );

    let stdout = str::from_utf8(&run_output.stdout)
        .expect("Output is not valid UTF-8")
        .trim(); // remove trailing newline

    let expected = "\
0
1
2
3
4
5
6
7
8
9
1
2
3
4
5
6
7
8
9";

    assert_eq!(stdout, expected, "Program output did not match expected");
}
