# mltt

A minimal Martin-Löf type theory, implemented via the free foil.

This is the third demo language in this repository, after `lambda-pi` and `soas`,
and it exists for a different reason than either. `lambda-pi` shows the same
calculus implemented four times, in increasing order of automation; `soas` is the
demanding client that pushes on metavariables and matching. `mltt` is meant to be
a language you could plausibly *write something in*: it type checks, and it is
the language a module and namespace layer is going to be built on top of.

## What is in it

The core is deliberately small.

- One universe `𝕌`, with type-in-type. The demo is about scoping, not about
  consistency, so `nf` can diverge on a well-typed term.
- `Π`, `Σ`, the identity type `Id`, and the unit type `𝟙` with its element `tt`.
- λ-abstraction, application, pairs, **and their eliminators**: `π₁`, `π₂`, and
  `J`. A 2024 reviewer of the free foil paper noted that the `lambda-pi` demo
  has pair construction and no eliminator; that is not repeated here.
- **Pattern binders**: `_`, a variable, and a pair pattern, nested arbitrarily.
  This is what makes the demo exercise free foil's custom-pattern layer rather
  than a flat list of binders.
- `let`, type ascription `(t : A)`, and the non-dependent sugar `A → B` and
  `A × B`.
- Top-level definitions, unfolded by δ-reduction.

Conversion is naive: both sides are normalised and compared with the library's
`alphaEquiv`.

## Running it

```sh
stack run mltt < haskell/mltt/examples/core.mltt
```

The interpreter understands three commands, separated by layout or by `;`:

```
def id : Π (A : 𝕌) → A → A := λ A . λ x . x

check id : Π (A : 𝕌) → A → A

compute id 𝟙 tt
```

## How it is put together

| Module | What it holds |
|---|---|
| `grammar/MLTT/Syntax.cf` | The BNFC grammar. The source of truth for the raw syntax; everything under `src/Language/MLTT/Syntax/` is regenerated from it on every `configure`. |
| `Language.MLTT.FreeFoilConfig` | The `FreeFoilConfig` that drives the Template Haskell. One term sort, with `Pattern'` as the binding type. |
| `Language.MLTT.Impl.Generated` | Where `mkFreeFoil` and `mkFreeFoilConversions` are spliced, plus the instances they need that Template Haskell does not supply. |
| `Language.MLTT.Eval` | Reduction: pattern matching as a substitution, `whnf`, `nf`, `conv`, and the desugaring of `→` and `×`. |
| `Language.MLTT.Typecheck` | A bidirectional type checker. |
| `Language.MLTT.Impl` | The interpreter: commands, the growing top-level scope, and printing. |

Two things are worth reading for the design rather than for the type theory.

**Opening a binder at one fresh variable.** To check `λ p . e` against
`Π (q : A) → B`, the checker allocates a *single* fresh variable and opens both
`p` and `q` at it, via `instantiate`. The two patterns need not have the same
shape, and neither needs to bind anything, so `λ (x, y) . e` against
`Π (z : Σ …) → B` and `λ _ . e` against `Π (z : A) → B` are the same rule. The
alternative — relating the two patterns' binders directly — cannot work, since
they may bind different numbers of names.

**A top-level constant is an ordinary name.** A `def` extends the ambient scope
with one more `Foil.Name`, whose entry in a `NameMap` says what it unfolds to.
That makes the top-level environment a growing foil scope, which is one of the
two candidate designs for a global environment; the alternative is a signature
node carrying an interned identifier, so that a top-level entry is a genuinely
closed term. Nothing here commits to either yet, and the `Display` map in
`Language.MLTT.Impl` is the seed of the interner that both would need.
