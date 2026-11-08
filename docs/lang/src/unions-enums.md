# Unions and enums

Unions and Rust-like enums currently support declarations, concrete layout, construction, and ownership-aware aggregate storage.

The intended direction is:

- unions provide overlapping storage with an explicitly chosen active member;
- enums provide a discriminant and zero or one payload field per variant;
- payloads follow the normal `s_T`/`h_T` move and destruction rules;
- simple literal, wildcard, and enum-variant matching is supported;
- payload bindings and exhaustive-match diagnostics are not implemented yet.

Current syntax is:

```fcy
union Value { integer: int }
enum Result { Ok(int), Err(str), None }
```

```fcy
match result {
    Result::Ok => { printintrin 1; }
    Result::None => { printintrin 2; }
    _ => { printintrin 3; }
}
```
