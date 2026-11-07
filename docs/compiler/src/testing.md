# Testing and debugging

Run the full suite with `FCY_BACKEND=qbe cargo test` and `FCY_BACKEND=llvm cargo test`. The tests compile example programs with `--nostd`, link them, and compare stdout.

For a single source file, use `cargo run -- input file.fcy -o /tmp/program --nostd --backend qbe`. Set `--check` to stop before linking. Debug builds print the generated MIR module, which is useful for checking layouts, calls, ownership cleanup, and generated generic functions.
