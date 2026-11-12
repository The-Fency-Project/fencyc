# Changelog

## 0.15.0

- LLVM is now the only supported backend; QBE is retained only as dormant MIR infrastructure.
- Added backend-independent MIR atomic RMW operations and LLVM lowering.
- Added typed `std::core::atomic` builtins with explicit memory ordering.
- Added initial `std::rc` Arc/Weak support and strong/weak fcyrt counters.
- Added split stdlib module layout and LLVM stdlib packaging.
- Added Rust-like ranges, array slices, generic unions/enums, trait-backed comparisons, and improved separate compilation.
- Added generic `sizeof @T` handling for concrete specializations.

## 0.14.2

- Previous stable baseline before the stdlib, backend, atomic, and generic aggregate work.
