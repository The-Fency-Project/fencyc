v0.13.1:
- LLVM backend somewhat works. It was kinda painful to work with because of 
overengineering probably, but I hope their optimizations was worth it.
- MIR refactor: `FValue` now is a struct containing `FVal` enum (which was previously
`FValue` itself)
- Fixed tests for LLVM support
additional patch 0.13.1-a:
- Fixed tests 
- `mem2reg` returned
- A bit more info into `CONTRIBUTING.md`
