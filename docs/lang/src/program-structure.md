# Program structure

A program is made from declarations and a `main` function. Modules can nest declarations. `use` makes names from another module available for lookup.

```fcy
module math {
    pub func add(a: int, b: int) -> int {
        return a + b;
    }
}

func main() -> int {
    return math::add(2, 3);
}
```

Visibility is explicit with `pub`. Struct fields and functions are private unless declared public.
