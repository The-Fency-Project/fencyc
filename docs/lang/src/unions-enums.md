# Unions and enums

Unions provide overlapping storage with an explicitly chosen member. Enums provide an eight-byte discriminant and shared storage for the largest payload, with zero or one payload per variant. Both can be named directly in type annotations.

Aggregate ownership checks are currently shallow. Nested payload destruction and moves across control flow still need work before these types can underpin owning stdlib containers.

Current syntax is:

```fcy
union Value { integer: int }
enum Result { Ok(int), Err(str), None }
```

```fcy
let result: Result = Result::Ok(7);
let value = match result {
    Result::Ok(v) => { v + 1; }
    Result::Err => { 0; }
    Result::None => { -1; }
};
```

`Result::None` constructs a unit variant. A payload binding such as `Ok(v)` is scoped to its arm; a variant pattern without a binding ignores its payload. All arms that produce a value must agree on its type. Arms may also return from the enclosing function.

Matches must be exhaustive: cover each enum variant, both boolean values, or include `_`. Integer matches require a wildcard. Integer literals, booleans, wildcards, and enum variants are supported. Struct value matching through the future `Eq` trait is not implemented yet.

Casting an enum to `uint`, `u32`, `ushort`, or `ubyte` yields its zero-based declaration index, truncated to the destination width. The first variant has index zero.
