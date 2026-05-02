use std::process::Command;

/// Some tests on examples 
/// Doing nostd for easier CI/CD
/// Set ENV `FCY_BACKEND=llvm` to test with llvm
/// E.g. `FCY_BACKEND=llvm cargo test` in sh

fn backend_flag() -> &'static str {
    std::env::var("FCY_BACKEND")
        .unwrap_or_else(|_| "qbe".to_string())
        .leak()
}

fn compile(input_files: &[&str], output_bin: &str) {
    let backend = backend_flag();

    let mut args = vec![
        "run",
        "--",
        "input",
    ];

    args.extend(input_files);
    args.push("-o");
    args.push(output_bin);
    args.push("--nostd");
    args.push("--verbose");

    args.push("--backend");
    args.push(backend);

    let status = std::process::Command::new("cargo")
        .args(&args)
        .status()
        .expect("failed to run compiler");

    assert!(status.success(), "Compilation failed");
}

fn run_bin(bin: &str) -> String {
    let out = std::process::Command::new(bin)
        .output()
        .expect("failed to run binary");

    assert!(out.status.success(), "program crashed");

    std::str::from_utf8(&out.stdout)
        .unwrap()
        .trim()
        .to_string()
}

#[test]
fn test_variables_example() {
    let input_file = "examples/1_variables.fcy";
    let output_bin = "testbins/1_variables";

    compile(&[input_file], output_bin);

    let stdout = run_bin(output_bin);

    let expected = "\
9.859600
5
3
10.000000
27.500000";

    assert_eq!(stdout, expected);
}

#[test]
fn test_loops_example() {
    compile(&["examples/2_loops.fcy"], "testbins/2_loops");

    let stdout = run_bin("testbins/2_loops");

    let expected = "\
0
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
0
1
2
3
4
5
6
7
8
9";

    assert_eq!(stdout, expected);
}

#[test]
fn test_functions_example() {
    compile(&["examples/3_functions.fcy"], "testbins/3_functions");

    let stdout = run_bin("testbins/3_functions");

    let expected = "\
1
7
120
19.250000";

    assert_eq!(stdout, expected);
}

#[test]
fn test_arrays_example() {
    compile(&["examples/4_arrays.fcy"], "testbins/4_arrays");

    let stdout = run_bin("testbins/4_arrays");

    let expected = "\
3
1
2
7
Hello, world!
13
3
1
8";

    assert_eq!(stdout, expected);
}

#[test]
fn test_modules_example() {
    compile(
        &[
            "examples/5_modules/main.fcy",
            "examples/5_modules/other.fcy",
        ],
        "testbins/5_modules",
    );

    let stdout = run_bin("testbins/5_modules");

    let expected = "\
Hello, modules!
Goodbye!
Goodbye!
6";

    assert_eq!(stdout, expected);
}

#[test]
fn test_structs_example() {
    compile(&["examples/6_structs.fcy"], "testbins/6_structs");

    let stdout = run_bin("testbins/6_structs");

    let expected = "\
5
289
12
5
289
12
16
124";

    assert_eq!(stdout, expected);
}
