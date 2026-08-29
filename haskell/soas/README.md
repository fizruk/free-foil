# soas

Second-order abstract syntax, implemented via the free foil.

The language has metavariables, and this package implements substitution of metavariables, matching, and constraint solving against the types that `mkFreeFoil` generates. It is the more demanding client of the Template Haskell layer, with two mutually recursive syntactic categories (terms and types).

This package is a demonstration and is not published on Hackage. See the [repository README](https://github.com/fizruk/free-foil#readme).
