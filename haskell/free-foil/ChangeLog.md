# CHANGELOG for `free-foil`

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
