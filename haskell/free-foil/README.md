# free-foil

Efficient Type-Safe Capture-Avoiding Substitution for Free (Scoped Monads).

This package provides a scope-safe representation for syntax with binders. Scopes are tracked in a phantom type index, so that capture-avoidance is a property the type checker enforces rather than a discipline the programmer keeps. It builds on the foil of Maclaurin, Radul, and Paszke, extends it with patterns, and adds free scoped monads, so that substitution, α-equivalence, and conversion to and from a raw syntax are implemented once for every language whose syntax is given as a signature bifunctor.

- `Control.Monad.Foil` — names, scopes, binders, and the `Sinkable`/`CoSinkable` classes.
- `Control.Monad.Free.Foil` — the free foil: `AST binder sig n`, substitution, α-equivalence, supports, and conversions.
- `Control.Monad.Foil.TH` and `Control.Monad.Free.Foil.TH` — Template Haskell that generates the scope-safe syntax from a raw (BNFC-generated) one.
- `Control.Monad.Foil.Blocks` and `Control.Monad.Foil.Registry` — reserved ranges of names, for units that are checked independently and linked afterwards.
- `Control.Monad.Free.Foil.Binary` and `Control.Monad.Free.Foil.Artifact` — serialisation of a checked unit, and the checks that loading one rests on.

See the [repository README](https://github.com/fizruk/free-foil#readme) for the design and the papers behind it, and the [documentation on Hackage](https://hackage.haskell.org/package/free-foil) for the modules themselves.
