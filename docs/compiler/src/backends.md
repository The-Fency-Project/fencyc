# MIR and backends

MIR is defined in `src/mir/mir.rs`. Functions contain blocks with assignments, calls, loads, stores, copies, aggregate operations, and terminators. Struct layouts are represented by `FTypeDef` entries.

The QBE backend maps aggregates to named QBE types and pointers to machine-word values. The LLVM backend declares opaque struct types first, fills their bodies from MIR typedefs, and then emits functions. Backend changes should preserve the same MIR behavior so both backend test runs remain equivalent.
