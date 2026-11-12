# Fencyc compiler internals

`fencyc` is a small Rust compiler for the Fency language. The frontend parses source into an AST, semantic analysis resolves names and types, code generation lowers the AST into a small MIR, and LLVM turns MIR into native code.

The compiler is intentionally direct. There is no borrow checker and no general intermediate type-inference engine. Ownership is represented by a moved marker on symbols and is enforced at the points where values are consumed.
