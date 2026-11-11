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
    compile_extra(input_files, output_bin, &[]);
}

fn compile_extra(input_files: &[&str], output_bin: &str, extra: &[&str]) {
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
    args.extend_from_slice(extra);

    let output = std::process::Command::new("cargo")
        .args(&args)
        .output()
        .expect("failed to run compiler");

    assert!(output.status.success(), "Compilation failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
}

#[test]
fn native_callback_and_varargs_interop() {
    compile_extra(&["examples/15_native_interop.fcy"], "testbins/15_native_interop", &["--extfiles", "tests/fixtures/native_calls.c"]);
    assert_eq!(run_bin("testbins/15_native_interop"), "121\n1");
}

#[test]
fn callbacks_and_typed_tails_across_modules() {
    compile(&["examples/16_callbacks/main.fcy", "examples/16_callbacks/helpers.fcy"], "testbins/16_callbacks");
    assert_eq!(run_bin("testbins/16_callbacks"), "15\n10\n0");
}

#[test]
fn qbe_lowering_avoids_copy_chains() {
    use crate::codegen::mirtoqbe::QBEBackend;
    use crate::mir::mir::*;
    use crate::seman::seman::FType;
    let mut function = FFunction::new("sum".into(), true, vec![], FType::int, FFunctionKind::Local);
    function.add_blk(FBlock::new("entry".into()));
    let result = FValue::new(FVal::VarTmp("result".into()), FType::int);
    function.assign_instr(result.clone(), FType::int, FInstr::BinaryOp(IRBinOp::Add,
        FValue::new(FVal::IConst(2), FType::int), FValue::new(FVal::IConst(3), FType::int)));
    function.add_term(FTerm::Return(Some(result)));
    let mut module = FModule::new();
    module.add_func(function);
    let output = QBEBackend::new().translate_module(&module).to_string();
    assert!(output.contains("%result =l add 2, 3"), "{output}");
    assert!(!output.contains("copy"), "unnecessary copy in arithmetic lowering: {output}");
}

#[test]
fn enum_payloads_share_storage() {
    use crate::fcparse::fcparse::FcParser;
    use crate::lexer::lexer::tokenize_source;
    let mut parser = FcParser::new(tokenize_source("enum E { A(int), B(double), C(ubyte) }"));
    parser.parse_everything();
    parser.structs.recalc_layouts().unwrap();
    let info = &parser.structs.tab["main::E"];
    assert_eq!(info.size, 16);
    assert_eq!(info.max_alignment, 8);
    assert!(info.fields.values().all(|f| f.offset == 8));
}

fn reject(name: &str, source: &str, diagnostic: &str) {
    let path = format!("testbins/reject_{name}.fcy");
    std::fs::write(&path, source).unwrap();
    let output = Command::new("cargo").args(["run", "--quiet", "--", "input", &path, "--nostd", "--check"])
        .output().expect("compiler failed to start");
    let text = format!("{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
    assert!(!output.status.success(), "invalid source compiled: {name}");
    assert!(!text.contains("panicked"), "compiler crashed: {text}");
    assert!(text.contains(diagnostic), "missing diagnostic {diagnostic}: {text}");
}

#[test]
fn function_pointers() {
    compile(&["examples/11_function_pointers.fcy"], "testbins/11_function_pointers");
    assert_eq!(run_bin("testbins/11_function_pointers"), "5\n10\n14\n21\n12\n41\n31\n12\n99");
}

#[test]
fn variadic_functions() {
    compile(&["examples/12_variadic.fcy"], "testbins/12_variadic");
    assert_eq!(run_bin("testbins/12_variadic"), "16\n10\n15\n5\n258\npromoted -7 1.5\n1 65535\nempty tail\n42");
}

#[test]
fn scalar_and_control_flow_regressions() {
    compile(&["examples/13_regressions.fcy"], "testbins/13_regressions");
    assert_eq!(run_bin("testbins/13_regressions"),
        "9\n-4\n1\n6148914691236517205\n0\n255\n-1\n4\n-1\n-2.000000\n3\n6.000000\n65000\n-9\n1\n0\nline one\nline two\n1\n1\n0");
}

#[test]
fn build_command_uses_default_backend() {
    let root = std::env::current_dir().unwrap();
    let dir = root.join("testbins/build_smoke");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("build.fcy"), "extern func printf(format: str, ...) -> i32; func main() { printf(\"builder ran\"); return; }").unwrap();
    let output = Command::new("cargo").args(["run", "--quiet", "--manifest-path"])
        .arg(root.join("Cargo.toml")).args(["--", "build"]).current_dir(dir)
        .output().expect("compiler failed to start");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(String::from_utf8_lossy(&output.stdout).contains("builder ran"));
}

#[test]
fn reject_invalid_function_signatures_and_calls() {
    reject("fn_arg", "func f(x: int) -> int { return x; } func main() { let p = f; p(true); return; }", "Incompatible argument");
    reject("fn_count", "func f(x: int) -> int { return x; } func main() { let p = f; p(); return; }", "Incorrect argument count");
    reject("fn_type", "func f(x: int) -> int { return x; } func main() { let p: func(uint) -> int = f; return; }", "Mismatched types");
    reject("call_scalar", "func main() { let p = 1; p(); return; }", "not a function pointer");
    reject("untyped_local", "func f(n: int, ...) { return; } func main() { return; }", "Use `...`");
    reject("typed_extern", "extern func f(n: ...int); func main() { return; }", "Use `...`");
    reject("empty_extern", "extern func f(...); func main() { return; }", "at least one fixed");
    reject("variadic_main", "func main(values: ...int) { return; }", "entry point cannot be variadic");
    reject("tail_type", "func f(n: ...int) { return; } func main() { f(true); return; }", "compatible with given arguments");
    reject("tail_owned", "struct S { value: int } func f(n: ...s_S) { return; } func main() { return; }", "copyable scalar");
    reject("c_owned", "struct S { value: int } extern func f(n: int, ...); func main() { f(0, S { value: 1; }); return; }", "compatible with given arguments");
}

#[test]
fn distinct_types_are_not_interchangeable() {
    reject("struct_cast", "struct A { x: int } struct B { x: int } func main() { let a = A { x: 1; }; let b = a$s_B; return; }", "Illegal cast");
    reject("array_arg", "func f(xs: [int]) { return; } func main() { f([true]bool); return; }", "compatible with given arguments");
}

#[test]
fn reject_invalid_matches() {
    reject("match_missing", "func main() { let n = match 1 { 1 => {2;} }; return; }", "Non-exhaustive match");
    reject("match_enum", "enum E { A, B } func main() { let e = E::A; let n = match e { E::C => {1;} _ => {0;} }; return; }", "variant of the matched enum");
    reject("match_unit", "enum E { A } func main() { let n = match E::A { E::A(v) => {1;} }; return; }", "unit variant payload");
    reject("match_wrong_type", "func main() { let n = match 1 { true => {2;} _ => {0;} }; return; }", "requires a bool");
    reject("match_void_arm", "func nothing() { return; } func main() { let n = match true { true => {1;} false => { nothing(); } }; return; }", "Mismatched types");
    reject("tail_not_last", "func f(xs: ...int, n: int) { return; } func main() { return; }", "must be last");
}

#[test]
fn match_and_branch_returns() {
    compile(&["examples/14_match_control_flow.fcy"], "testbins/14_match_control_flow");
    assert_eq!(run_bin("testbins/14_match_control_flow"), "7\n0\n9\n-1\n1\n2\n11");
}

#[test]
fn lexer_handles_eof_comments_and_string_escapes() {
    use crate::lexer::lexer::{tokenize_source, Tok};
    let tokens = tokenize_source("1 // no final newline");
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].tok, Tok::Int(1));
    let tokens = tokenize_source(r#""a\n\t\"\\\0" ... .."#);
    assert_eq!(tokens[0].tok, Tok::strlit("a\n\t\"\\\0".into()));
    assert_eq!(tokens[1].tok, Tok::Ellipsis);
    assert_eq!(tokens[2].tok, Tok::DoubleDot);
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
5
289
12
12
16
124";

    assert_eq!(stdout, expected);
}

#[test]
fn test_generic_structs_example() {
    compile(&["examples/7_generic_structs.fcy"], "testbins/7_generic_structs");

    let stdout = run_bin("testbins/7_generic_structs");

    let expected = "7\n42";
    assert_eq!(stdout, expected);
}

#[test]
fn test_unions_enums_example() {
    compile(&["examples/8_unions_enums.fcy"], "testbins/8_unions_enums");
    assert_eq!(run_bin("testbins/8_unions_enums"), "3");
}

#[test]
fn test_match_example() {
    compile(&["examples/9_match.fcy"], "testbins/9_match");
    assert_eq!(run_bin("testbins/9_match"), "20\n0\n3");
}

#[test]
fn test_comparison_loop_before_enum_match() {
    let binary = "testbins/10_tribool";
    compile(&["examples/10_tribool.fcy"], binary);
    let out = Command::new(binary).args(["hello", "world"])
        .output().expect("failed to run TriBool example");
    assert!(out.status.success(), "TriBool program crashed");
    assert_eq!(String::from_utf8(out.stdout).unwrap().trim(),
        "testbins/10_tribool\nhello\nworld\n4");
}

#[test]
fn test_parser_failure_does_not_report_success() {
    let out = Command::new("cargo").args([
        "run", "--", "input", "tests/fixtures/invalid_parse.fcy", "--nostd",
    ]).output().expect("failed to run compiler");
    assert!(!out.status.success(), "malformed input must fail compilation");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(!stdout.contains("Compilation succeed"), "{stdout}");
}

#[test]
fn test_ranges_and_slices_example() {
    compile(&["examples/10_ranges_slices.fcy"], "testbins/10_ranges_slices");
    assert_eq!(run_bin("testbins/10_ranges_slices"), "3\n30\n99\n2\n2\n50");
}

#[test]
fn test_generic_unions_and_enums_example() {
    compile(&["examples/17_generic_aggregates.fcy"], "testbins/17_generic_aggregates");
    assert_eq!(run_bin("testbins/17_generic_aggregates"), "4 8");
}
