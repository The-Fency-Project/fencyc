# Generics

Generic structs are instantiated at concrete use sites and receive independent layouts.

```fcy
struct Box<T> {
    pub value: T
}

let n = Box<int> { value: 42; };
```

Methods on generic structs are specialized for each concrete instance. Generic functions are also monomorphized from their call arguments.
