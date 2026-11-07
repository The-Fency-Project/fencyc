# Repository map

- `src/lexer/lexer.rs` tokenizes source and defines keywords and operators.
- `src/fcparse/fcparse.rs` contains the Pratt parser, AST, function tables, and parser-side generic metadata.
- `src/seman/seman.rs` performs name resolution, type checking, move checks, trait checks, and struct layout calculation.
- `src/codegen/codegen.rs` lowers AST expressions and functions to MIR and handles deferred generic generation.
- `src/mir/mir.rs` defines MIR values, instructions, functions, data, and type definitions.
- `src/codegen/mirtoqbe.rs` and `src/codegen/mirtollvm.rs` implement the QBE and LLVM backends.
- `src/main.rs` coordinates parsing, semantic analysis, code generation, backend lowering, assembly, and linking.
- `src/tests.rs` runs end-to-end compiler tests against example programs.
