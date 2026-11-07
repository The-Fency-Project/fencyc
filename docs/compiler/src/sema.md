# Semantic analysis and ownership

`FType::Struct` is an owning by-value aggregate. `FType::StructHeapPtr` is an owning heap pointer. Both are destructive move types. `FType::StructPtr` and `FType::Ptr` are non-owning raw pointers and are trivially copyable.

Each symbol carries `moved: Option<usize>`. Semantic analysis marks a symbol when it is consumed by a binding, reassignment, by-value call, return, array construction, or struct field construction. A later read reports a use-after-move error. Code generation mirrors the same state so scope cleanup skips values whose ownership moved elsewhere.

This is deliberately smaller than Rust's borrow checker: raw pointers are allowed, there are no lifetimes, and pointer validity is not proven by the compiler.
