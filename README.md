# fencyc
> [!WARNING]
> Toolchain is still on very early stages.

The Fency programming language compiler.
Targets [VoxVM](https://github.com/Freemorger/voxvm) bytecode.

# Building it
You would need latest rustc and cargo which could be installed with rustup.
Then just:
`cargo build --release`
You also may get binary from releases.

# Usage
Compile some program:
- `fencyc input.fcy -o program.vve`
Run it with [VoxVM](https://github.com/Freemorger/voxvm):
`voxvm --vve=program.vve`
Flags:
`-fpermissive`: enables permissive mode, which leads to less type system errors, but still warns.

# Docs
Soon.
