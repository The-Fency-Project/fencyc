# Changelog

## Unreleased

- LLVM is now the only supported backend. QBE remains in the source tree as a dormant MIR translator while the backend boundary is preserved for future FCBE work.
- The default backend is LLVM for all optimization levels.
- Standard library installation now targets LLVM metadata and object bundles.
- Added the initial `std::rc` module with generic `Arc<T>` and `Weak<T>` handles backed by fcyrt reference counters.
- Split stdlib sources into module directories.
- Added fcyrt strong/weak counter APIs for future Arc and Weak support.
- Planned next: backend-independent MIR atomic operations and LLVM lowering.
