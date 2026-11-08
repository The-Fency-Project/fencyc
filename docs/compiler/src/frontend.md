# Frontend

The lexer produces compact tokens. The parser uses Pratt precedence for expressions and explicit routines for declarations, functions, structs, modules, traits, calls, arrays, and field access.

AST paths retain generic metadata separately from their path segments. The plain path string is used for symbol lookup; generic argument order is retained for monomorphization. Function and struct tables are collected while parsing so later phases can resolve declarations without rescanning source text.
