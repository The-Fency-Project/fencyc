## Next planned steps (likely)
### Stdlib
- stdlib
# Future
## Small/medium (unsorted)
- further diagnostics (trait incompl func signature)
- move in loops
- Finer incremental compilation, interface hashes, and cache garbage collection
- maybe move keyword
- glob for input
- unsafe stuff
- iterators for `for`
- default args values in funcs (maybe)
- block return
- stack strs
- slices
- ptrs for primitives
## Long-term
- stdlib 
- wiki
- macros 
- other features
- maybe rewrite fencyc in fency itself, which may achieve cleaning code and better integration
## General vision
1. MIR, QBE and LLVM stuff 
2. Finish generics (structs)
3. Implement unions and limited VA args. They will be crucial, e.g. unions for error type in std.
4. Implement enums (no adt yet) and basic pattern matching
5. Stdlib and fixes in compiler (likely to be)
6. fencyc v1.0.0 release 
