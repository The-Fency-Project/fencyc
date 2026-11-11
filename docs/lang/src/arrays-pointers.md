# Arrays and pointers

Fixed arrays store their elements inline. Unsized `[T]` values represent pointer-backed arrays. `ptr` is intended for C and runtime interop and has no ownership tracking. Safe raw pointers are written `*T` in type positions and are copied like addresses.

Ranges use Rust-style half-open bounds: `start..end` includes `start` and stops before `end`. Either bound can be omitted (`..end`, `start..`). A range is a first-class `range` value, so it can be stored in a variable and used for indexing.

Indexing an array with a range creates a zero-copy view:

```text
let middle = arr[1..3];
let tail = arr[2..];
```

The resulting `slice[T]` view stores a pointer and a length. `_len` reports the view length, indexing reads the underlying array, and writes through the view update the original array.
