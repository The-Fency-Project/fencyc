# Functions and methods

Functions use `func name(args) -> return_type`. A function returning no value may omit the return type. Methods are declared inside `impl Type` and receive an explicit `self` argument, commonly `self: *Type` for a non-consuming pointer receiver.

Passing an owning struct or heap pointer by value moves it. Passing `*Type` lets a method inspect or modify the original without transferring ownership.
