# Aggregate type design: unions and enums

This page records the design constraints before implementation. A union needs a declaration table, a layout consisting of the maximum member size and alignment, active-member construction, and member access. An enum needs a discriminant layout, variant payload layouts, construction, and ownership-aware destruction of the active payload.

The existing compiler calculates layouts centrally in `StructTable`, lowers aggregates through MIR `FTypeDef`, and tracks ownership on symbols. Unions and enums should reuse those boundaries instead of adding backend-specific layout logic. Pattern matching should be added only after discriminant values and payload access are represented in MIR.
