# Standard library integration proposal

This chapter proposes the next ecosystem steps. It does not implement the standard library or a package manager.

## Starting point

The compiler currently compiles an explicit list of source files together. `use` changes name lookup; it does not discover or load source files. Generic definitions and aggregate layouts are available only for the files in that invocation. `--nostd` disables automatic runtime linking. The default driver otherwise searches `~/.fency/runtime` and `~/.fency/libs` and links `libfcyrt`. `build.fcy` is compiled as a host executable and then run.

Consequently, linking `libstd.a` alone would not make generic types, traits, or source signatures visible to semantic analysis. Start by making stdlib source available to the existing frontend, and defer serialized compiler metadata until there is a stable format worth caching.

## Library boundaries

Keep a Rust-like public `std` namespace while dividing implementation responsibilities:

| Layer | Responsibility | Dependencies |
| --- | --- | --- |
| Core | Fundamental traits, `Option`/`Result`, arithmetic and pointer helpers | Compiler intrinsics; no allocator or OS |
| Allocation | Allocator interface, collections, owned strings | Core plus an allocator |
| Hosted library | Files, streams, processes, threads, platform APIs | Core, allocation, platform runtime |
| Runtime | Startup, allocation hooks, panic/abort hooks, small C/assembly shims | Target ABI and OS |

Use separate source trees or packages even if the first public imports remain `std::core::...`. Agree on canonical names such as `std::core::op::Eq` before introducing compiler-recognized hooks. Prefer explicit, versioned language items for required hooks over recognizing whichever user declaration happens to have the right spelling. Primitive operators should keep working without std.

## A reproducible toolchain installation

Introduce an explicit `--sysroot` and a documented discovery order (flag, environment override, compiler installation). A proposed layout is:

```text
<sysroot>/
  manifest.toml
  lib/fency/src/core/
  lib/fency/src/alloc/
  lib/fency/src/std/
  lib/fency/<target>/libfcyrt.a
  lib/fency/<target>/libstd.a
```

The manifest should record compiler version, runtime ABI version, supported targets, and source revision. Compile std sources with the same compiler and target as the application. Initially, a small deterministic source manifest can add the required files to one compilation. Generic code is instantiated in the consuming compilation; avoid putting concrete std function bodies into every application object. Later, split compiled implementation objects from signatures and generic bodies using versioned metadata.

Keep library selection independent of linking: core-only code should not need an OS runtime, and `--nostd` should remain a reliable bootstrap path. Add a separate allocator/hosted-library selection when those layers exist. Report missing installations and version mismatches directly instead of failing deep inside the linker.

## Build and package workflow

Start with local path dependencies and explicit entry points. A future project manifest should describe package name/version, dependencies, source roots, target kind, and required native libraries. Record resolved revisions in a lockfile. Keep the frontend's module names independent of filesystem paths, and reject duplicate module or symbol definitions rather than letting merged maps overwrite them.

Use `build.fcy` for native integration and code generation. Build scripts run for the host; their generated code and native libraries may target a different machine. Pass host, target, sysroot, and output directory explicitly. Cache keys should include compiler/ABI versions, source and dependency hashes, target, backend, and optimization flags.

## Suggested implementation order

1. Write small core modules against explicit file lists with `--nostd`: traits, `Option`, `Result`, and integer helpers.
2. Add deterministic std source discovery and sysroot diagnostics, then test a program importing core in multiple files.
3. Define allocator and panic hooks; compile the runtime per target and test failure paths.
4. Implement collections and owned strings only after control-flow ownership, aggregate destruction, and pointer lifetimes have regression coverage. Those areas are still shallow in the current compiler.
5. Add hosted facilities one platform at a time, keeping platform calls behind a narrow internal interface.
6. Add package resolution and compiled-library metadata when explicit-source builds become a measurable bottleneck.

For each layer, run the same behavior suite through QBE and LLVM and add C interoperability tests for exported callbacks and native calls. This keeps ABI and runtime changes visible while the language is still evolving.
