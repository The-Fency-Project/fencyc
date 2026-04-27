# Current
- Optimize QBE code from redundant copies
## Next planned steps (likely)
- maybe llvm backend
- generic structs 
- traits example + update struct example 
# Future
## Small/medium (unsorted)
- unions
- further diagnostics (trait incompl func signature)
- move in loops
- incremential compilation
- maybe move keyword
- glob for input
- unsafe stuff
- imports?
- iterators for `for`
- default args values in funcs (maybe)
- make error if trying to override func that wasnt declared
- function pointers
- block return
- va args
- stack strs
- slices
- ptrs for primitives
## Long-term
- generics
    - generic structs
- smaller features 
    - unions 
    - enums 
    - matches 
- stdlib 
- wiki
- macros 
- other features
- maybe move to LLVM from QBE 
- maybe rewrite fencyc in fency itself, which may achieve cleaning code and better integration
## General vision
1. MIR, QBE and LLVM stuff 
2. Finish generics (structs)
3. Implement unions and limited VA args. They will be crucial, e.g. unions for error type in std.
4. Implement enums (no adt yet) and basic pattern matching
5. Stdlib and fixes in compiler (likely to be)
6. fencyc v1.0.0 release 
