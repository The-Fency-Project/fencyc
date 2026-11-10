# Functions and methods

Functions use `func name(args) -> return_type`. A function returning no value may omit the return type. Methods are declared inside `impl Type` and receive an explicit `self` argument, commonly `self: *Type` for a non-consuming pointer receiver.

Passing an owning struct or heap pointer by value moves it. Passing `*Type` lets a method inspect or modify the original without transferring ownership.

## Function pointers

`func(int) -> int` is the type of a function pointer taking one `int` and returning an `int`. Omit the arrow for functions returning no value. A bare function name produces a pointer:

```fcy
func increment(x: int) -> int { return x + 1; }
func apply(f: func(int) -> int, x: int) -> int { return f(x); }

extern func printf(format: str, ...) -> i32;

func main() {
    let callback: func(int) -> int = increment;
    printf("%ld\n", apply(callback, 4));
    return;
}
```

Pointers are copyable. They can be stored in arrays and struct fields, returned, reassigned, and called through expressions such as `handlers[0u](5)` or `choose()(5)`. Parameter types, return types, and variadic tails are part of the pointer type. Capturing closures and taking an overloaded or unspecialized generic function as a value are not supported yet.

## Typed variadic functions

A final `name: ...T` parameter collects zero or more arguments of type `T`:

```fcy
func sum(initial: int, values: ...int) -> int {
    let total = initial;
    for let i = 0u in i < _len values; i += 1u {
        total += values[i];
    }
    return total;
}
```

Call it as `sum(10)` or `sum(10, 1, 2, 3)`. Its pointer type is `func(int, ...int) -> int`. Tail elements currently support numeric types, `bool`, `str`, raw pointers, and function pointers. Owning aggregates and generic tail element types are rejected.

The tail is a temporary view into caller-provided storage. Use indexing and `_len` directly on the named parameter. Do not retain it after the call or return it: the compiler does not yet check the lifetime of pointer-backed arrays. Passing an existing array as a spread tail is not supported.

## External C varargs

External declarations use a final unnamed `...`, with at least one fixed parameter:

```fcy
extern func printf(format: str, ...) -> i32;

func main() {
    printf("%d %.1f\n", -7ib, 1.5f);
    let output: func(str, ...) -> i32 = printf;
    output("hello\n");
    return;
}
```

Extra arguments follow C default promotions: `float` becomes `double`, and `bool` and 8/16-bit integers become `i32`. Owning aggregates are rejected in the untyped tail. The compiler checks the fixed parameters and representability of tail arguments; it does not validate a C format string against the supplied arguments. Fency typed tails use a different calling convention from C varargs.
