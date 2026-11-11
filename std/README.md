# Fency standard library skeleton

This directory is the source tree for the first in-repository standard library
layers. It is intentionally small and declaration-focused: the modules define
the names that future collections, allocators, and hosted APIs can build on,
without pretending that those facilities are implemented yet.

The compiler currently builds libraries from an explicit source list. From the
repository root, build the skeleton with:

```sh
fencyc input \
  std/core.fcy std/libc.fcy std/alloc.fcy std/io.fcy std/prelude.fcy \
  --library -o build/std.fmeta --nostd
```

The same build can be bootstrapped from inside this directory with
`fencyc build`; `build.fcy` currently shells out through `std::libc::system`.

An application can consume the resulting metadata with `--dep build/std.fmeta`
and refer to declarations under `std::core`, `std::alloc`, `std::io`, and
`std::prelude` and `std::libc`. Automatic sysroot discovery and implicit std imports remain
future work, so applications should opt in explicitly for now.

The source files are split by layer so the tree can grow without forcing the
compiler runtime, allocator, and hosted APIs into one monolithic module.

All C ABI declarations live in `std::libc`. Other modules should depend on
that namespace instead of redeclaring `printf`, allocation, or memory-copy
symbols, which keeps the platform boundary in one place.

`Option<T>` and `Result<T, E>` are usable with explicit type arguments, for
example `std::core::Option<int>::Some(7)`. Type inference for an unparameterized
generic enum constructor such as `Option::Some(7)` remains future work.
