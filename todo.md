## Short term

### Compiler
- Add MIR atomic operations and lower them through LLVM.
- Finish generic method specialization across metadata-only libraries.
- Improve diagnostics for ownership, traits, and generic type inference.
- Keep the MIR backend-independent while LLVM is the only active backend.

### Standard library
- Finish `std::rc::Arc<T>` and `std::rc::Weak<T>` on top of fcyrt.
- Add allocation, string, collection, and I/O essentials.
- Make `fency build` the standard stdlib build path.

## Later

- Add `ref T` and `weak T` syntax with compiler cycle checks.
- Revisit FCBE or another lightweight backend after the language and MIR stabilize.
- Add package and sysroot tooling.
- Macros and self-hosting experiments.
