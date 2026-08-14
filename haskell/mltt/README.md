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

λ is written `λ x ⇒ e`. Not `λ x . e`, because a dot inside an identifier is
part of the identifier — `Nat.zero` is one token, so the parser never has to
decide whether a dot qualifies a name or separates a binder from a body. And
not `λ x → e`, so that the arrow of a λ-abstraction is not read as the arrow
of a Π-type; both turn up in one expression often enough for the distinction
to be worth seeing. Declarations are laid out rather than punctuated, and a
`namespace` block is opened by indenting under it.

Conversion is naive: both sides are normalised and compared with the library's
`alphaEquiv`.

## What is deliberately not here

The package exists to exercise free foil's scope handling, and to be the thing a
module and namespace layer is built on. Everything below is out of scope, and
most of it is somebody else's work elsewhere in this ecosystem rather than a gap
waiting to be filled here.

- **Elaboration and type-annotated terms.** The checker returns a type and
  throws away everything else: no elaborated output term, no implicit
  arguments, no inserted coercions. The library's scope-indexed annotation
  layer (`Control.Monad.Free.Foil.Annotated`) is not used.
- **Normalisation by evaluation.** Conversion normalises both sides and
  compares them. No closures, no delayed substitutions, no readback.
- **A generic typing algebra.** The rules are hand-written for this one
  signature. Deriving a checker from per-constructor typing rules, and the
  Pfenning recipe that picks the judgement, are a separate line of work.
- **Metavariables, unification and matching.** No holes and no `?m`. Generic
  second-order matching, higher-order preunification and pattern unification
  over free foil are Kudasov, Starikov, Ivanov and Afliatonov's
  ([UNIF 2025](https://hal.science/hal-05148806)), implemented in
  [`free-foil-hou`](https://github.com/fedor-ivn/free-foil-hou).
- **Data types, recursion and termination.** There are no declarations, no
  eliminators beyond `π₁`, `π₂` and `J`, and nothing is checked for
  termination or positivity.
- **Consistency.** Type-in-type is deliberate, so `nf` can diverge on a
  well-typed term.
- **Good errors and speed.** Source positions are carried through the AST but
  never printed; `let` substitutes rather than sharing; `conv` normalises both
  sides in full. Nothing here has been measured.

Refinement of a telescope and interned qualified names are not in this list.
They are not out of scope: they are what comes next, and what is here was built
to carry them.

## The module layer

A module is introduced by a `module` header and runs to the next one. It
declares namespaces, imports other modules, and marks declarations private.

Usually a module is a file, and the interpreter takes any number of files; but
nothing requires it, and the example below puts two modules in one file so
that the whole of it can be read at once. Build order is computed over every
module the interpreter was given, wherever it came from, so a file may import
a module declared in another file — or, as here, later in the same one.

```
module Prelude

namespace Nat where
  private def twice : Π (A : 𝕌) → (A → A) → A → A
    := λ A ⇒ λ f ⇒ λ x ⇒ f (f x)

  def quadruple : Π (A : 𝕌) → (A → A) → A → A
    := λ A ⇒ λ f ⇒ twice A (twice A f)

  -- A namespace may contain a namespace.
  namespace Extra where
    def octuple : Π (A : 𝕌) → (A → A) → A → A
      := λ A ⇒ λ f ⇒ quadruple A (quadruple A f)

module Client
import Prelude

open Nat
compute quadruple 𝟙 (λ x ⇒ x) tt
```

A namespace has nothing to do with the file a declaration lives in: `module
Data.Nat` may declare `namespace Peano`, and importers then write
`Peano.zero`. The module name orders the build; the namespace qualifies the
name.

**The point of the layer is that visibility is a property of a name table and
of nothing else.** A top-level definition is an ordinary `Foil.Name` whose
entry in a `NameMap` says what it unfolds to. Making a declaration `private`
removes a spelling from `Language.MLTT.Resolve`'s table; it does not touch the
term, the scope, or the definition map. So a client cannot *name* a private
helper and can still *reduce* through it:

```
$ stack run mltt -- prelude-and-client.mltt
module Prelude
  ✓ defined Nat.twice
  ✓ defined Nat.quadruple
module Client
  ↦ tt                          -- computing Nat.quadruple unfolded Nat.twice
  ✗ not in scope: Nat.twice     -- but the client cannot write it
```

That distinction is the reason narrowing belongs above free foil rather than
inside it, and `Language.MLTT.Resolve` is where it lives: nothing in that
module mentions a scope, a `Foil.Name`, or the kind `S`.

## Module parameters, and the `over` clause

A module may take parameters. Every declaration is checked with them in scope,
and leaves the module *discharged* over exactly the ones it turns out to use.

```
module Monoid (A : 𝕌) (unit : A) (mul : A → A → A)

def square over (A, mul) : A → A := λ x ⇒ mul x x
def neutral over (A, unit) : A := unit
def id : 𝟙 → 𝟙 := λ x ⇒ x
```

```
module Monoid
  ✓ defined square over (A, mul)
  ✓ defined neutral over (A, unit)
  ✓ defined id
```

`id` uses no parameter, so it is discharged over nothing and stays an
ordinary constant. `neutral` is discharged over `A` even though its body
mentions only `unit`: keeping `unit` puts `unit`'s type into the discharged
type, and that type is `A`. Relevance is upward closed in the telescope.

A declaration is closed at the point it is defined, and not when the module
ends, so nothing has to be rewritten when the module ends. Inside the module
the parameters are *put back on use*, so a later declaration reads as if none
of that had happened:

```
def squareNeutral over (A, unit, mul) : A := square neutral
```

This elaborates to `square A mul (neutral A unit)`. Note that `square` and
`neutral` were closed over different parameters, so there is no single
telescope being reinstated: each reference gets back what that declaration
took. Because the arguments really are there afterwards, they count as uses,
which is why `squareNeutral` comes out closed over all three without saying so.

Putting them back is elaboration and not textual replacement, so a local binder
of the same name shadows the declaration:

```
def shadowing : 𝟙 → 𝟙 := λ square ⇒ square
```

is the identity and is closed over nothing. A client gets no such help, and
wants none: it is applying a closed constant to a monoid of its choosing.

The `over` clause is optional and it never changes what is discharged. The
computed set is authoritative, and the clause is *checked against it*:

```
✗ declared: over (mul)
    actual: over (A, mul)
```

It is spelled `over` and not `uses` on purpose. rzk has a `uses` clause, and it
is a different thing: mandatory, and listing the implicit assumptions of a
definition rather than the parameters of its module.

**Discharge is where the demo needs scope restriction rather than extension.**
Checking happens in the scope the parameters extend the module's scope to, and
the result has to come back, because the module's scope is where its exports
live and where the next module starts. `Language.MLTT.Telescope` takes the
support of the type and of the value, once each, and closes that set under the
parameter types: keeping `(x : A)` puts `A` into it, and one pass from the
inside out settles that, since a parameter's type mentions only the parameters
before it. Free-foil's `withThinnedNameBinderList` then cuts the chain of
binders down to the closed set in one step, and the abstractions are rebuilt
along the thinned chain, restricting each kept parameter type and the body into
it with `unsinkAST`. So the used set is not declared and believed, and the term
is walked a fixed number of times rather than once per parameter, which asking
`unsinkAST` at every parameter in turn would do.

## Named telescopes and `include`

A parameter block can be declared once and reused. A `telescope` declaration is
a unit of its own, beside the modules, and it binds nothing: what it names is a
module header and not a term.

```
telescope Monoid (A : 𝕌) (unit : A) (mul : A → A → A)

module CommMonoid include Monoid
def square : A → A := λ x ⇒ mul x x

module Group include Monoid (inv : A → A)
def undo : A → A := λ x ⇒ mul x (inv x)
```

The included fields come first in the including module's telescope, before the
parameters it declares itself, and one of its own may mention them: `inv : A →
A` above resolves only because `A` came from `Monoid`. Everything downstream is
unchanged, so `undo` is discharged over `(A, mul, inv)` exactly as if the three
had been written out.

An include is resolved before the module is checked, so what reaches the checker
is an ordinary parametrised module. That is also what makes an include behave
like an import for the cache: a module's content hash is taken over its resolved
header, so changing a telescope rebuilds every module that includes it.

A telescope is elaborated afresh in each including module, so two includers share
nothing but the source they were written in. Instantiation is application: what
leaves an including module is a closed constant, and there is no `interpretation`
command because there is nothing for one to do.

Internally the parameters of a module are a labelled telescope, which is a
free-foil *pattern* with a label and a payload per binder. It is written out in
`Language.MLTT.Telescope`, with `CoSinkable` and `UnifiablePattern` by hand, so
that scope extension, the names of a block and α-equivalence of two blocks all
come from the library rather than from the demo. Its Haddock records what those
instances need that the pattern interface does not offer — a payload has to be
carried into the ambient scope, and `withPattern` exposes no renaming for it.

The idea is not new here. The framing followed is Jon Sterling's, in the
[Pterodactyl worklog](https://www.jonmsterling.com/01HC/), where a theory
expression denotes a telescope and refining a field leaves the remaining fields
as a telescope again, and that framing inherits in turn. Telescopes are
[de Bruijn's](<https://doi.org/10.1016/0890-5401(91)90066-B>), and labelling
their fields, so that a block can be declared once and projected from, is what
[dependent record types](https://doi.org/10.1007/s001650200018) are, with
[manifest fields](https://doi.org/10.1007/978-3-642-02444-3_15) for the refined
case, which is not implemented here. What is new is only that the telescope is a
scope-safe pattern rather than a construction on raw syntax.

## Running it

```sh
stack run mltt -- haskell/mltt/examples/core.mltt haskell/mltt/examples/modules.mltt
```

With no arguments the interpreter reads a program on standard input. Inside a
module it understands three commands:

```
def id : Π (A : 𝕌) → A → A := λ A ⇒ λ x ⇒ x

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
| `Language.MLTT.Resolve` | Name resolution: paths, name tables, `open`, and the free identifiers of a raw term. Deliberately free of any dependency on the foil. |
| `Language.MLTT.Telescope` | The labelled telescope, a foil pattern with a label and a payload per binder; module parameters as an instance of it, discharge over the fields a declaration uses, and the check of an `over` clause against that set. |
| `Language.MLTT.Impl` | The interpreter: build order, modules, declarations, the growing top-level scope, and printing. |

Two things are worth reading for the design rather than for the type theory.

**Opening a binder at one fresh variable.** To check `λ p ⇒ e` against
`Π (q : A) → B`, the checker allocates a *single* fresh variable and opens both
`p` and `q` at it, via `instantiate`. The two patterns need not have the same
shape, and neither needs to bind anything, so `λ (x, y) ⇒ e` against
`Π (z : Σ …) → B` and `λ _ ⇒ e` against `Π (z : A) → B` are the same rule. The
alternative — relating the two patterns' binders directly — cannot work, since
they may bind different numbers of names.

**A top-level constant is an ordinary name.** A `def` extends the ambient scope
with one more `Foil.Name`, whose entry in a `NameMap` says what it unfolds to.
That makes the top-level environment a growing foil scope, which is one of the
two candidate designs for a global environment; the alternative is a signature
node carrying an interned identifier, so that a top-level entry is a genuinely
closed term. Nothing here commits to either yet, and the `Display` map in
`Language.MLTT.Impl` is the seed of the interner that both would need.
