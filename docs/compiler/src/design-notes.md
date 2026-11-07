# Design notes

The compiler favors explicit tables and simple transformations over a large type system. Struct layout is calculated centrally in `StructTable`; backends consume the resulting layout instead of recalculating it.

New aggregate types should follow the same boundary: define parser metadata, define semantic layout and compatibility, lower construction and field access to MIR, then teach both backends how to represent the layout. Ownership behavior should be stated in terms of `FType` categories so semantic move checks and codegen cleanup cannot drift apart.
