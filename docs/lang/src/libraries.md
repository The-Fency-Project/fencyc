# Compiled libraries

Library files use ordinary module declarations and `pub` exports:

```fcy
module math {
    pub func add(a: int, b: int) -> int { return a + b; }
}
```

Build the library once, then import its compiled metadata when building an application:

```sh
fencyc input math.fcy --library -o build/math.fmeta --nostd
fencyc input main.fcy --dep build/math.fmeta -o program --nostd
```

The application can call `math::add(1, 2)`. `--dep` supplies declarations to the compiler and objects to the linker. It can be repeated, and transitive dependencies load automatically. A `use math;` statement affects name lookup after the library has been supplied; it does not locate files on disk.

Libraries can export structs, enums, unions, traits, generic functions, and generic struct definitions. Consumers can request new generic instantiations. Separate libraries should use distinct module namespaces; conflicting definitions are diagnosed.

By default, project builds cache objects and metadata in `.fency/incr/`. Add this directory to your project's `.gitignore`. Use `--verbose` to see cache hits and rebuilds, `--cache-dir` to choose another directory, and `--no-incremental` to force the current unit to rebuild. Changes to a dependency cause it and its consumers to rebuild on the next application build.

An exported library consists of its `.fmeta` and adjacent `.fmeta.objects/` directory. Keep them together. For installed precompiled libraries whose sources are unavailable, pass `--frozen-deps`. This validates the installed artifacts without trying to rebuild them. Installed artifacts must match the compiler build, backend, target, and PIC configuration. Sysroot discovery and automatic stdlib imports are future work.
