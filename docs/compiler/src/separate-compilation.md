# Separate compilation and the build cache

This first implementation caches whole compilation units and imports explicitly built libraries. It does not implement a package resolver or automatic stdlib installation/discovery.

## Building and consuming a library

Put library declarations in a module namespace, export its public API, and build a metadata artifact:

```sh
fencyc input math.fcy --library -o build/math.fmeta --nostd
fencyc input main.fcy --dep build/math.fmeta -o program --nostd
```

Repeat `--dep` for multiple libraries. Metadata records direct dependencies, so consumers automatically load transitive interfaces and link each dependency once, including diamond graphs. Ordinary `use` statements still only affect name lookup.

An unchanged compilation reuses objects without parsing, semantic analysis, code generation, or assembly. Executables are linked on every invocation; deleting the output executable does not force source recompilation. Verbose output reports `Cache hit:` and `Rebuilding:` per unit. `--no-incremental` forces the requested unit to rebuild. `--check` runs semantic analysis and does not publish a compiled cache entry for that unit.

## On-disk layout

The project working directory is the default cache root. `--cache-dir` overrides it.

```text
project/.fency/incr/
  {target}/{backend}/O{optimization}/{unit-id}/
    build.lock
    latest.fmeta
    {generation}/
      object_0.o
      ...
```

The unit ID derives from the output path, keeping separate outputs independent. Metadata records the exact input file list, compilation recipe, dependency build keys, direct object inventory and checksums, compiler identity, interfaces, and generic specialization names/signatures. Cached object generations are immutable. There is no garbage collector yet; removing `.fency/incr/` safely discards the project cache.

Library exports have a metadata file and an adjacent object directory:

```text
build/math.fmeta
build/math.fmeta.objects/{object-set-id}/object_0.o
```

Exported object references are relative to the metadata directory. Dependency references are also relative when they lie below that directory. This allows an installer to copy an artifact and its object directory together. Dependencies outside that directory retain absolute references; installations must lay out/rebuild their dependency artifacts together before distribution.

## Installed artifacts

By default, dependencies are validated against their recorded source files. If a dependency changed, the driver recursively rebuilds it from its recipe before compiling the consumer. Dependencies are visited before acquiring unit locks, and cycles are diagnosed.

Use `--frozen-deps` for prebuilt installations whose source files are unavailable:

```sh
fencyc input main.fcy --dep /opt/fency/lib/std.fmeta --frozen-deps -o program
```

Frozen dependencies validate compiler identity, target/backend/PIC configuration, object checksums, and the recorded keys of their transitive dependencies. They do not check source files or rebuild dependencies. Missing, corrupt, or incompatible installed artifacts produce errors. The install location is explicit for now; a future `fcyup` sysroot integration can supply these paths.

## Binary format and invalidation

`.fmeta` contains an eight-byte magic header, a format version, a SHA-256 payload checksum, and a size-limited bincode payload. It serializes the existing function, aggregate, and trait tables plus generic AST definitions. This is compiler-internal metadata, not a stable public interchange format. Compiler upgrades may require rebuilding libraries.

`build.rs` embeds a SHA-256 compiler identity derived from compiler sources, the QBE adapter, Cargo manifests/lockfile, Rust version, and build configuration. Each unit's key additionally covers source paths and bytes, native inputs, dependency build keys, and compilation settings. The driver also hashes the resolved assembler/compiler and QBE executables. Timestamps do not decide cache validity.

Invalidating a dependency currently invalidates all of its consumers, even if its public interface did not change. Interface-only hashes and finer-grained function/module invalidation are future optimizations.

Native object/archive inputs are copied and hashed. Units containing C/assembly source inputs are conservatively rebuilt each time, since native header/include dependency tracking has not been implemented. Native libraries selected through linker flags are resolved anew during linking.

## Imported interfaces and generics

Each artifact stores its direct interface; imports are deduplicated by artifact identity before tables merge. Conflicting ordinary function, aggregate, and trait definitions are errors. Repeated compatible external function declarations and identical specialization signatures can merge. Visibility remains a semantic property of declarations. Library machine symbols include private helpers so imported generic bodies can call them; symbol export is not the language privacy boundary.

Generic definitions remain available to consumers, allowing new concrete types without recompiling ordinary library bodies. Existing materialized specializations are recorded and reused. New instantiations are stored with the consumer's objects. Specialization call sites are analyzed in the definition namespace to avoid reusing another source file's call IDs. Native weak definitions coalesce identical instantiations independently emitted by different libraries; this is exercised on the Linux host with LLVM. Other target linkers still need platform execution tests.

The existing limitations of generic substitution, ownership, and symbol mangling still apply. Serialized generic ASTs are an initial representation; typed templates and stable declaration IDs would be a stronger long-term foundation.

## Failure and concurrency behavior

An OS file lock serializes builds of the same unit/configuration. The driver assembles into staging storage, verifies that inputs did not change during compilation, and renames objects into a new generation. It publishes `latest.fmeta` and exported metadata through temporary files and atomic renames. Failed compilations leave previous good metadata intact. Corrupt project cache entries or missing/corrupt cached objects rebuild; malformed explicitly imported metadata is reported instead of silently ignored.

The artifact regression suite covers cache hits, source edits, transitive rebuilds, missing/corrupt objects, failed builds, cyclic/diamond dependencies, imported generics and their private helpers, independent specialization producers, source-free artifact relocation, and configuration checks.
