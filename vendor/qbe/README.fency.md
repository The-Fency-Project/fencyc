# Local QBE adapter

Vendored from `https://github.com/Freemorger/qbe-rs` at commit
`b8f59573d539b0306c62d752e9f359ef8d786bf8` (crate version 2.5.1). Upstream MIT and Apache 2.0 licenses
are preserved alongside this file.

Fency adds `Instr::CallIndirect(Value, args, variadic_boundary)` to render
typed function-pointer calls while preserving aggregate return types.
It also renders floating-point ordered comparisons without integer sign prefixes.
Keep this small extension when updating the vendored adapter.
