# Aggregate types: unions and enums

The first implementation slice is in place. A union has a layout consisting of the maximum member size and alignment. An enum has an eight-byte discriminant followed by storage for its largest payload. The parser accepts declarations, semantic analysis calculates layouts and validates construction, and codegen lowers construction to aggregate storage.

The compiler calculates layouts centrally in `StructTable`, lowers aggregates through MIR `FTypeDef`, and tracks ownership on symbols. Every enum payload overlaps after the discriminant, with each field's offset aligned for its type. The current slice supports at most one payload per variant.

Match expressions compare literal values or load the enum discriminant, branch into arms, and assign a shared result when an arm yields a value. Semantic analysis checks pattern types, variant identity, bindings, compatible result types, and exhaustiveness. Returning arms do not contribute a result type. MIR's `Unreachable` terminator marks the impossible unmatched path and continuations after all arms return.

These checks do not constitute complete ownership analysis for aggregates. Recursive payload drops and control-flow ownership merging remain prerequisites for robust owning collections.
