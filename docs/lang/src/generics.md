# Generics

Generic structs, unions, and enums are instantiated at concrete use sites and receive independent layouts.

```fcy
struct Box<T> {
    pub value: T
}

let n = Box<int> { value: 42; };

union Slot<T> { pub value: T }
enum Maybe<T> { Some(T), None }

let slot = Slot<int> { value: 7; };
let value = Maybe<int>::Some(8);
```

Methods on generic structs are specialized for each concrete instance. Generic functions are also monomorphized from their call arguments.
