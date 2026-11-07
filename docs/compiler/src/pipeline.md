# Compilation pipeline

`main::compile` parses all input files in parallel, combines function, struct, trait, and generic tables, and calculates concrete struct layouts. Semantic analysis then runs independently per source file and records matched overloads for call sites.

Code generation runs per file. Each `CodeGen` receives the shared tables and the semantic call map. It emits a MIR module, writes a temporary SSA file or LLVM module, and the driver invokes the selected assembler and linker.

When debugging a change, start at the source construct in `fcparse.rs`, follow its semantic arm in `SemAn::analyze_expr`, then follow the matching `CodeGen::gen_expr` arm and the backend instruction lowering.
