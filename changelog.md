v0.9.2:
- destructors
- `$HOME/.fency/runtime` and `$HOME/.fency/libs` are now used as libraries import 
dirs for linker
- [fency runtime lib](https://github.com/The-Fency-Project/runtime) is 
imported now if you don't pass arg `--nostd`
- quite a lot of fixes
- added new compilation flags: `--shared` and `--onlyobjs`
- added help messages for `fencyc help subcommand`
