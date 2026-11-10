# Structs

```fcy
extern func printf(format: str, ...) -> i32;

struct Point {
    pub x: int
    pub y: int
}

func main() -> int {
    let p = Point { x: 3; y: 4; };
    printf("%ld\n", p.x);
    return 0;
}
```

Struct values are copied at the machine level when moved, but the source ownership state is invalidated. Heap-only structs use `#[heap]` and are constructed through a heap pointer.
