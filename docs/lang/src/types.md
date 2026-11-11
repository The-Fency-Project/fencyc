# Types

Primitive types include `int`, `uint`, `i32`, `u32`, `double`, `single`, `bool`, byte and short variants, `str`, and `ptr`.

Struct types use prefixes: `s_T` is a struct value, `h_T` is an owning heap pointer to a struct, `*T` is a safe raw pointer to a struct, and `ptr` is an untracked FFI pointer.

Arrays use `[T; count]` for fixed arrays and `[T]` for pointer-backed arrays. Struct layout follows C-like alignment and field order.

`range` values describe half-open intervals such as `1..3`, `..3`, and `1..`. `slice[T]` is a pointer-backed array view produced by applying a range to an array.
