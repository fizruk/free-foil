# CHANGELOG for `free-foil`

# 0.2.0 — 2024-10-27

- Generate [`COMPLETE` pragma](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pragmas.html#complete-pragmas) in `mkPatternSynonyms` (see [#26](https://github.com/fizruk/free-foil/pull/26))
- Polykind `ZipMatchK` class with default generic implementation via [`kind-generics`](https://hackage.haskell.org/package/kind-generics) (see [#27](https://github.com/fizruk/free-foil/pull/27))
- New experimental TH generation for Free Foil with support for rich syntax in `Control.Monad.Free.Foil.TH.MkFreeFoil` (see [#28](https://github.com/fizruk/free-foil/pull/28))

# 0.1.0 — 2024-08-18

- Generalize functions for binders, support general patterns (see [#16](https://github.com/fizruk/free-foil/pull/16))

  - Add `withPattern` method to `CoSinkable`. It can be seen as a CPS-style traversal over binders in a pattern.
    Our Template Haskell support covers generation of `withPattern`,
    so normally the user does not have to think about it.

  - Generalize many functions to work with arbitrary patterns, not just `NameBinder`:

    - `withFreshPattern` — to
    - `withRefreshedPattern` and `withRefreshedPattern'`
    - `extendScopePattern` — extend a given scope with all binders in a given pattern
    - `namesOfPattern` — collect all names from a pattern
    - `unsinkNamePattern` — try to unsink names from a scope extended with binders from a given pattern
    - `assertDistinctPattern` — establish that extended scope is distinct (if outer scope is)
    - `assertDistinctExt` — establish that extended scope is distinct and indeed an extension

  - Implement unification for patterns in `unifyPatterns`.
    This turns out to be one of the most difficult places, especially for compound patterns.
    Implementing patterns properly on the user side not comfortable at all!
    Luckily, we provide useful helpers like `andThenUnifyPatterns` and `andThenUnifyNameBinders`,
    as well as Template Haskell support to derive `UnifiablePattern`.

  - Generalize Free Foil to support arbitrary patterns.

  - The `Foil` and `FreeFoilTH` implementations now make use of the generalized pattern support.

# 0.0.3 — 2024-06-20

- Add α-equivalence checks and α-normalization (see [#12](https://github.com/fizruk/free-foil/pull/12)):

  - `Control.Monad.Foil` now offers more helpers to work with binder renaming and binder unification.
    These helpers can be used to implement (efficient) α-equivalence.
  - In `Control.Monad.Free.Foil` general implementation of α-equivalence and α-normalization is provided.

- Add general conversion functions for free foil (see [#14](https://github.com/fizruk/free-foil/pull/14)):

  - `Control.Monad.Free.Foil` now offers `convertToAST` and `convertFromAST` functions
    enabling easier implementation of conversions raw and scope-safe representations.

- Add Template Haskell functions for free foil (see [#14](https://github.com/fizruk/free-foil/pull/14)):

  - `Control.Monad.Free.Foil.TH` contains many useful functions to generate free foil from
    a raw representation (e.g. generated via BNFC), including generation of the signature,
    convenient pattern synonyms, `ZipMatch` instance, and conversion helpers.

# 0.0.2 — 2024-06-18

- Improve TH to support parametrized data types (see [#11](https://github.com/fizruk/free-foil/pull/11))
- Split `lambda-pi` into its own package (see [#10](https://github.com/fizruk/free-foil/pull/10))
- Switch to `template-haskell >= 2.21.0.0` (to support latest Stackage Nightly)
- Fix doctests (see [#9](https://github.com/fizruk/free-foil/pull/9))

# 0.0.1 — 2024-06-08

First release, corresponding to the ICCQ 2024 paper.
