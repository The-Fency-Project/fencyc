# Unions and enums

Unions and Rust-like enums are planned language features. Their design is being implemented around the existing tagged-layout and ownership model.

The intended direction is:

- unions provide overlapping storage with an explicitly chosen active member;
- enums provide a discriminant and zero or more payload fields per variant;
- payloads follow the normal `s_T`/`h_T` move and destruction rules;
- pattern matching will be added after declaration, layout, construction, and discriminant checking are stable.

No union or enum syntax is accepted by the current compiler yet.
