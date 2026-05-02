# Small silly contributing guide 
Current tasks and bigger roadmap could be found in TODO.md
`// TODO:` comments in code are for smaller but still important ones.
# Compiler architecture
Lexer -> parser -> sema -> MIR codegen -> mir translator -> backend -> 
ldas (assembler+linker) -> done.
Parsers generate global tables (structs, traits, funcs, etc) and then they're shared 
in sema and codegen.
## Repo structure
`src/main.rs`: entry point with some cli
`src/cli.rs`: main cli definitions (commands, Target, etc)
`src/tests.rs`: ci/cd tests
`src/lexer/lexer.rs`: lexer definitions
`src/fcparse/fcparse.rs`: parser with a weird name + some tables definitions 
`src/seman/seman.rs`: semantic analyzer and some structs/enums like `FType`
`src/mir/mir.rs` - fencyc's MIR (Middle Intermediate Representation) definitions 
`src/codegen/codegen.rs`: MIR generator
`src/codegen/mirtoqbe.rs`: MIR -> QBE IR translation layer 
`src/codegen/mirtollvm.rs`: MIR -> LLVM IR translation layer 
# Formatting rules
Just don't do mess. Use rustfmt if possible.
Meaningful variable names, no unrelated stuff in comments...
# Opening issue
Make sure other one with the same problem isn't yet open.
Provide all useful context.
# Opening pull request
Describe your improvements, why they're important. Check formatting. 
> [!IMPORTANT]
Run tests for both backends before pushing and make sure all of them passed: 
```sh
FCY_BACKEND=qbe cargo test 
FCY_BACKEND=llvm cargo test 
```

