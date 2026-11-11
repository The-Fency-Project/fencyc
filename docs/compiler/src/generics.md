# Generics and monomorphization

Generic structs, unions, and enums are parsed as templates. Concrete uses such as `Box<int>` or `Maybe<int>::Some(8)` are recorded during parsing. Before semantic analysis, `StructTable::instantiate_many` clones each template, substitutes generic field types, recursively instantiates nested generic fields, and calculates a concrete layout.

Generic struct methods are deferred. Code generation clones each method for every concrete instance and substitutes receiver, argument, and return types. Generic functions use the same deferred-generation idea and receive their concrete argument and return types at a call site.

Concrete names are path-like strings, for example `main::Box::int` and `main::Maybe::int`, so existing symbol and backend naming code can continue to use path segments. Generic enum constructor and match paths currently require explicit type arguments; inference from `Maybe::Some(...)` is future work.
