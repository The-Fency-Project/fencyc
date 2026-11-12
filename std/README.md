# Fency standard library skeleton

This directory is the source tree for the first in-repository standard library
layers. It is intentionally small and declaration-focused: the modules define
the names that future collections, allocators, and hosted APIs can build on,
without pretending that those facilities are implemented yet.

The compiler currently builds libraries from an explicit source list. LLVM is the
active backend, so install its metadata/object bundle:

```sh
fencyc input \
  std/core/mod.fcy std/libc/mod.fcy std/alloc/mod.fcy std/io/mod.fcy std/prelude/mod.fcy std/rc/mod.fcy \
  --library -o build/std-llvm.fmeta --nostd --backend llvm -O3
```

The same build can be bootstrapped inside this directory with `fencyc build`.
The build script shells out through `std::libc::system` for now.
An application can consume the metadata with `--dep build/std-llvm.fmeta` and
refer to declarations under `std::core`,
`std::alloc`, `std::io`, `std::prelude`, and `std::libc`. Installed toolchains
discover the backend-matching bundle automatically.

The source files are split by layer so the tree can grow without forcing the
compiler runtime, allocator, and hosted APIs into one monolithic module.

The dependency-free core currently includes small numeric and comparison
helpers under `std::core::num` and `std::core::cmp`.

All C ABI declarations live in `std::libc`. Other modules should depend on
that namespace instead of redeclaring `printf`, allocation, or memory-copy
symbols, which keeps the platform boundary in one place.

`Option<T>` and `Result<T, E>` are usable with explicit type arguments, for
example `std::core::Option<int>::Some(7)`. Type inference for an unparameterized
generic enum constructor such as `Option::Some(7)` remains future work.
