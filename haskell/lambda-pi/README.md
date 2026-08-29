# lambda-pi

λΠ-calculus with pairs, implemented via the foil and the free foil.

The same language is implemented four times, in increasing order of automation, so that the cost of each layer of the library can be read off directly:

- `Language.LambdaPi.Impl.Foil` — the scope-safe syntax written out by hand.
- `Language.LambdaPi.Impl.FoilTH` — the same, with Template Haskell generating most of it.
- `Language.LambdaPi.Impl.FreeFoil` — the free foil, with the signature written out by hand.
- `Language.LambdaPi.Impl.FreeFoilTH` — the free foil with Template Haskell, which is the most general of the four and the one the executable uses.

This package is a demonstration and is not published on Hackage. See the [repository README](https://github.com/fizruk/free-foil#readme).
