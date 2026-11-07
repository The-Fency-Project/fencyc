# Unions and enums

Unions and Rust-like enums currently support declarations, concrete layout, construction, and ownership-aware aggregate storage.

The intended direction is:

- unions provide overlapping storage with an explicitly chosen active member;
- enums provide a discriminant and zero or one payload field per variant;
- payloads follow the normal `s_T`/`h_T` move and destruction rules;
- pattern matching will be added after declaration, layout, construction, and discriminant checking are stable.

Current syntax is:

```fcy
union Value { integer: int }
enum Result { Ok(int), Err(str), None }
```
