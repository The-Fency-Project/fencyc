# Compilation pipeline

`main::compile` delegates dependency resolution and cache validation to `artifact`. A cache hit reuses compiled objects. On a miss, `main::compile_unit` parses the unit's input files in parallel, merges local tables with imported binary interfaces, and calculates concrete struct layouts. Semantic analysis then runs independently per source file and records matched overloads for call sites.

Code generation runs per file. Each `CodeGen` receives the shared tables and the semantic call map. It emits a MIR module, writes a staged SSA file or LLVM module, and the driver assembles reusable objects. The cache publishes those objects and binary metadata; executable builds then link the unit and its dependencies.

When debugging a change, start at the source construct in `fcparse.rs`, follow its semantic arm in `SemAn::analyze_expr`, then follow the matching `CodeGen::gen_expr` arm and the backend instruction lowering.
