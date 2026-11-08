# Aggregate types: unions and enums

The first implementation slice is in place. A union has a layout consisting of the maximum member size and alignment. An enum has an eight-byte discriminant followed by storage for its largest payload. The parser accepts declarations, semantic analysis calculates layouts and validates construction, and codegen lowers construction to aggregate storage.

The existing compiler calculates layouts centrally in `StructTable`, lowers aggregates through MIR `FTypeDef`, and tracks ownership on symbols. Pattern matching should be added only after discriminant values and payload access are represented in MIR. The current slice supports at most one payload per enum variant; match expressions and variant extraction remain future work.
