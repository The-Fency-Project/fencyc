# Calls and ABI

Function declarations and function-pointer types share `FType` signatures. `Function(args, ret)` is a copyable pointer with a checked signature. The last argument may be `Variadic(T)`: `none` marks C varargs and any supported scalar `T` marks a Fency typed tail. `Variadic` is declaration metadata, not a first-class runtime type.

`FuncDat::function_type` exposes a declaration's source signature. `FType::abi_signature` calculates the physical signature used for indirect calls. `CodeGen::abi_args` gives the same transformation for definitions and LLVM forward declarations. Keep these transformations in sync:

| Source signature component | ABI representation |
| --- | --- |
| Fixed scalar or function pointer | One argument |
| By-value aggregate return | Leading destination pointer; returned pointer |
| Fency `values: ...T` | Array data pointer followed by `uint` count |
| C `...` | ABI variadic tail after the fixed arguments |

The caller allocates typed-tail storage, evaluates each argument once from left to right, and stores tail elements consecutively using their actual byte sizes. `_len values` reads the hidden count. Typed tails currently support copyable scalar elements only. They inherit the lifetime limitations of existing pointer-backed arrays; this is not a borrow checker.

`AstNode::Call` resolves ordinary names and local function-pointer variables. `CallValue` handles computed callees, including field and array access and functions returning function pointers. Callbacks have no environment or capture payload. Taking overloaded or unspecialized generic functions as values is rejected.

MIR keeps ordinary direct calls as `Call`. `Invoke(target, args, boundary)` carries a typed callee and an optional boundary between fixed and C variadic arguments. Hidden return arguments count toward that boundary. The frontend applies C default promotions before either backend sees the call.

QBE emits `call $symbol(...)` or `call %pointer(...)`, placing `...` at the recorded boundary. The locally vendored `qbe` adapter adds indirect-call rendering; its provenance and licenses are in `vendor/qbe`. LLVM declares C variadic functions with `is_var_args`, constructs indirect call types from the ABI signature, and lowers function addresses as function symbols rather than data globals.

QBE expression lowering accepts an optional destination and writes result-producing instructions straight to that destination. Copy expressions reuse their operand; an explicit copy remains when a named mutable value needs assignment. Narrow integer values still receive sign/zero normalization. This avoids the previous instruction-to-temporary, temporary-to-temporary, temporary-to-destination chain without propagating mutable aliases across blocks.
