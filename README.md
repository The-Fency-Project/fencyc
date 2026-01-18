# fencyc
> [!WARNING]
> The toolchain is still on very early stages.

The Fency programming language compiler - simple and modern language, aimed to be enjoyable.
This branch targets QBE IR. 

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

## Usage
Compile some program:  
- `fencyc input input.fcy` 
Run as normal program.
Flags:  
`--fpermissive`: enables permissive mode, which leads to less type system errors, but still warns.

## Docs
Soon. For now, consider learning from `examples/` directory in order (1_*, 2_*, ..)
