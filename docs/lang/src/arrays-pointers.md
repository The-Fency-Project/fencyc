# Arrays and pointers

Fixed arrays store their elements inline. Unsized `[T]` values represent pointer-backed arrays. `ptr` is intended for C and runtime interop and has no ownership tracking. Safe raw pointers are written `*T` in type positions and are copied like addresses.
