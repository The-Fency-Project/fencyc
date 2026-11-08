# Ownership and moves

Fency uses a small ownership model rather than a borrow checker.

| Type | Meaning | Passing by value |
|---|---|---|
| `s_T` | owning struct payload | destructive move |
| `h_T` | owning heap pointer | destructive move |
| `*T` | non-owning raw pointer | trivial copy |
| `ptr` | raw FFI pointer | trivial copy |

After moving an owning value, the original variable cannot be read again. Destructors and heap frees follow the value that received ownership. Taking a raw pointer does not consume the original value.

`ref T` and `weak T` are planned and are not part of the current language.
