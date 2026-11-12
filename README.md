# fencyc
![GitHub Release](https://img.shields.io/github/v/release/The-Fency-Project/fencyc)
![GitHub License](https://img.shields.io/github/license/The-Fency-Project/fencyc)
![GitHub commit activity](https://img.shields.io/github/commit-activity/m/The-Fency-Project/fencyc)

The Fency programming language compiler - simple and modern language, aimed to be enjoyable.
Think of it like this: Rust, but without borrow checker pain, simpler C interop,
faster compilation, overloads and much more.

> [!WARNING]
> The toolchain is still on very early stages. Best experience would be with 
> Linux (amd64/aarch64/riscv64), though workarounds with other OS'es are possible 
> with some extra tinker steps.


## Fast installation
There is a `fcyup` python script that would download/update fency toolchain for you,
including fencyc and libs from latest binary release.  
On *nix systems (linux/macos/etc):
```sh
curl --proto '=https' --tlsv1.2 -sSL https://raw.githubusercontent.com/The-Fency-Project/fcyup/refs/heads/main/fcyup.py | python3 -
```
For windows, just download the script and run it.  
[Script repository](https://github.com/The-Fency-Project/fcyup)  
If your platform isn't covered by binary releases, consider building the toolchain from source.

## Building fencyc
You will need latest rustc and cargo which could be installed with rustup.
Then just:
`cargo build --release`

## External dependencies
To actually compile something with fencyc, you would also need:
1. `llvm` (version 21!) - the currently supported compiler backend.
   LLVM emits native object files directly for the linker.
> [!NOTE]
> All the external dependencies binaries (except libs) must be in your PATH.

## Usage
Make sure everything working:
- `cargo test`    
Compile some program:  
- `fencyc input input.fcy`     
Run as normal program.     
Flags: see `fencyc help` for general help or `fencyc help subcommand` to see info about 
specific subcommand (e.g. `fencyc help input`)  

## Editor plugins
For now, we have plugins for 2 code editors:
1. [VS Code](https://github.com/The-Fency-Project/fcyvsc)
2. [Vim/Nvim](https://github.com/The-Fency-Project/fcyvim)

## Docs
Soon. For now, consider learning from `examples/` directory in numerical order (1_*, 2_*, ..)
