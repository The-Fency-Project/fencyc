# Testing and debugging

Run the full suite with `FCY_BACKEND=qbe cargo test` and `FCY_BACKEND=llvm cargo test`. The tests compile example programs with `--nostd`, link them, and compare stdout.

The suite also checks rejected signatures and matches, compiler failure status, EOF comments and string escapes, enum payload layout, and QBE copy elimination. `tests/fixtures/native_calls.c` exercises the native callback ABI and C varargs promotions with register and stack arguments. Tests for `examples/16_callbacks` cover declarations and calls across compilation units. The build-command smoke test compiles and runs a temporary `build.fcy` under `testbins/`.

For a single source file, use `cargo run -- input file.fcy -o /tmp/program --nostd --backend qbe`. Set `--check` to stop before linking. Debug builds print the generated MIR module, which is useful for checking layouts, calls, ownership cleanup, and generated generic functions.
