# fencyc
> [!WARNING]
> The toolchain is still on very early stages. Best experience would be with 
> Linux (amd64/aarch64/riscv64), though workarounds with other OS'es are possible 
> with some extra tinker steps.
> [!WARNING]
> Codegen currently are being rewritten for QBE IR target only

The Fency programming language compiler - simple and modern language, aimed to be enjoyable.
Planned to be lightweight and ~~de-appled~~ swift alternative

## Fast installation
There is a `fcyup` python script that would download/update fency toolchain for you,
including voxvm and fencyc from latest binary release.  
On *nix systems (linux/macos/etc):
```sh
curl --proto '=https' --tlsv1.2 -sSL https://raw.githubusercontent.com/The-Fency-Project/fcyup/refs/heads/main/fcyup.py | python3 -
```
For windows, just download the script and run it.  
[Script repository](https://github.com/The-Fency-Project/fcyup)  
If your platform isn't covered by binary releases, consider building toolchain from source.

## Building fencyc
You will need latest rustc and cargo which could be installed with rustup.
Then just:
`cargo build --release`

## External dependencies
To actually compile something with fencyc, you would also need:
1. `qbe` - QBE (quick backend) binary to generate native assemblies from SSA.
Get those from your package manager (apt/pacman/homebrew/etc) or install 
manually, has to be in PATH. See [QBE website](https://c9x.me/compile/).
2. `gcc` - to assemble and link native assemblies. Preinstalled on most linux 
distributions, but for others/macos/windows you would likely need to 
install this, also has to be in the PATH. 
See [GNU website](https://gcc.gnu.org/install/) or get the binaries.

## Usage
Compile some program:  
- `fencyc input input.fcy`     
Run as normal program.
Flags:  
`--fpermissive`: enables permissive mode, which leads to less type system errors, but still warns.
`-o name`: determines output program name

## Docs
Soon. For now, consider learning from `examples/` directory in order (1_*, 2_*, ..)
