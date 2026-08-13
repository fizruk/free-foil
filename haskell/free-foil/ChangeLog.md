# CHANGELOG for `free-foil`

# Unreleased

Conversion between raw and scope-safe syntax. An additive release apart from one new requirement on `mkFreeFoilConversions`, noted below.

New:

- Scope **restriction**. The foil accounted for scope extension only: `NameBinder` adds names, `Ext` is the erasable evidence, `sink` is a coercion. Restriction is the other direction, and its only trace was `unsinkName`, at one binder and one name.

    - It needs no new constraint class. `Ext m n` read from the other end already *is* the statement that every name of `m` is a name of `n`, and the runtime witness of it is the smaller `Scope`.

    - `NameSet n` is a set of names of scope `n` — as opposed to `Scope n`, which is all of them and carries the invariants freshness rests on. `<>` is union and `mempty` is empty, so supports can be accumulated with `foldMap`. `unsinkNameSet` drops a pattern's names from a set in one `IntSet` operation rather than a membership test per name.

    - `withRestrictedScope` cuts a scope down to a subset of its names, handing the continuation `Ext m n` and `Distinct m`. Its haddock records what a restricted scope may *not* be used for: a name allocated from it is fresh with respect to `m` and not to `n`.

    - `supportOf` is a term's support, the annotation co-de-Bruijn syntax carries intrinsically and the foil, having free weakening, does not. `withRelevantScope` cuts a term down to the scope of exactly the names it uses; that is restriction imposed a priori, so nothing is tested and nothing can fail. `unsinkAST` is the a-posteriori form and the one that has to be paid for, and it now compares two `IntSet`s instead of walking a list of names with a membership test each.

    - `withThinnedNameBinderList` cuts a chain of binders down to those whose names are in a given set, handing the continuation `Ext n m` and `Ext m l` to place the thinned scope between the two. This is what turns a support into a smaller chain in one step: the alternative, asking `unsinkAST` at every binder whether the term can do without it, walks the term once per binder. The thinned scope is produced rather than given, since a term's relevant scope is a subset of `l` and generally not an extension of `n`.

    - `NameSet` is `Sinkable`, so a support computed under a binder can be used outside it without rebuilding the set.

- `tryConvertToASTWith` resolves some identifiers to a whole term rather than to a variable, which is what a language with constants, primitives or abbreviations needs: such an identifier stands for something that is not a variable, and conversion is the only place where the binders are known. The table of names is consulted first, so a binder still shadows an entry; the extra table is sunk when going under a binder, exactly as the names are, so its entries need not be closed. `mkFreeFoilConversions` emits a `tryToXWith` beside each `tryToX`. Note that `tryConvertToAST` now also requires `SinkableK` on the binder, which every client in this repository already derives.

- `mapWithName` is the keyed version of `NameMap`'s `Functor` instance. It cannot change which names the map is defined on, so a total map stays total, which makes it a safe way to build a `Substitution` out of one with `nameMapToSubstitution` — an elaborator that has to expand a reference into something larger than a variable can do it that way rather than by inserting into a substitution by name.

    Verifying a declared dependency — a `uses` clause, a module's parameters — is `withRelevantScope` plus a comparison. Computing one is `supportOf` and then `withThinnedNameBinderList`; that is how `mltt` closes a declaration over the module parameters it uses.

- `Control.Monad.Free.Foil.freeVarsOf` and `freeVarsOfScopedAST` come from `supportOf`, so they no longer repeat a variable that occurs more than once, and return names in ascending order of their identifiers. Previously each occurrence was listed, and the order followed the term.

- `tryConvertToAST` converts a raw term and reports the first identifier that does not resolve, instead of `error`-ing on it. `convertToAST` called `error "undefined variable"` on a name outside its map, which is the ordinary unbound-variable case in any front-end, so every client had either to pre-check names itself or to crash. The failure is an `UnresolvedName rawIdent`, carrying the identifier and what was in scope at that occurrence — including the binders passed on the way down, which is what a caller checking names beforehand cannot know. It is one pass, short-circuiting at the failure, so a term that resolves costs no more than `unsafeConvertToAST`; `unresolvedInScope` is built where it fails and is never computed on the way through. A caller wanting *every* unresolved identifier rather than the first pays a second pass for it, with `unresolvedNames`. That is the right way round: the successful path should be fast, and a failing one can afford to be walked again for a better message.

  Note what neither carries: a source position. These functions are generic in the raw term and see it only through `toSig`, so a location, if the syntax has one, is not theirs to read.

- `convertFromASTWith` names the variables that occur free in the whole term separately from the bound ones, taking a `Name n -> rawIdent` for the former and an `Int -> rawIdent` for the latter. `convertFromAST` applies one function to every variable it meets and gives it only a raw name, which is not enough: raw names are not unique across scope indices, so a binder inside a term may share one with a name of the ambient scope, and naming by raw name alone prints the bound variable as whatever the ambient scope calls that name. Keeping the typed name is what tells them apart, and `unsinkNamePattern`, composed one per binder on the way down, is the operation for it. `mltt` hit exactly this: a definition's body is elaborated before the definition's own name is allocated, so `def f := λ x ⇒ x` gave both `f` and its bound `x` the raw name 0, and the printer showed the body as `λ x0 ⇒ f`.

- `mkFreeFoilConversions` generates a `tryToX` beside each `toX`, so that clients of `mkFreeFoil` get the reporting conversion without spelling out its six arguments. The name is derived from the existing one rather than configured, to leave `FreeFoilConfig` alone.

- `Control.Monad.Foil` exports `nameBinderListOf`. It already exported `nameBindersList` and `getNameBinders`, so the list of a pattern's binders was reachable only by composing them.

- `withFreshIn` allocates a fresh name inside a reserved range. A `NameRange` is two `Int`s bounding the allocator, not a set of names. The allocated name is the successor of the largest scope member inside the range, or the range's low end, and it is fresh in the whole scope: a member inside the range is smaller, and a member outside the range cannot be equal to a name inside it. So nothing beyond the scope has to be consulted, and units that allocate from disjoint reservations can never collide, which is what separate checking of modules needs. `tryWithFreshIn` returns `Nothing` on an exhausted range, so a driver can report which unit ran out. `withFreshNameBinderListIn` is the list-shaped form, and `withFreshNameBinderList` is now the special case of the full non-negative range; on a scope without negative names it behaves exactly as before.

  Allocation is what `sink` rests on, so the same change adds property tests: `rawFreshNameIn` over scopes with negative names and `minBound`/`maxBound`, `Data.IntSet` against a `Data.Set` model across the sign bit, and `NameMap` over negative names. The tests caught two overflow bugs in the first formulation of the allocator (`lookupLT (hi + 1)` wraps around at `hi = maxBound`, and so does the successor of a taken `maxBound`); both are kept as regression tests.

- `Control.Monad.Foil.Blocks` links scopes that were extended independently. `ExtWithin n l` is evidence that scope `l` extends scope `n` only inside a given range. The range bounds the extension and not the scope, so the names of `n` itself (a unit's imports) may lie anywhere. The evidence is built next to allocation, with one range test per binder (`extWithinRefl` to start, then `extWithinStep`); `withExtendScopeRange` builds it in one step instead, extending a scope with the first `k` names of a range after checking that the scope does not touch the range. Two units that extend a common scope inside disjoint ranges have disjoint extensions, so `withDisjointUnion` produces the union scope with one range comparison and one `IntSet.union`, and no set has to be tested for disjointness.

  `withDisjointUnion` hands the continuation both extension facts at once, as `withThinnedNameBinderList` does, together with a `ScopeUnion n m k` witness: the constraints say that `k` contains `n` and `m`, and the witness says that it contains nothing else. The second half is what totality of a merged `NameMap` rests on (an extension constraint alone admits a strict superset), so `unionNameMaps` demands the witness. `checkScopeUnion` produces the same witness by an `IntSet` equality test, for the re-attachment path where the union scope was rebuilt rather than handed down.

  There is no composition for `ExtWithin`, on purpose: the composite would only be bounded by the convex hull of the two ranges, and the hull may cover an unrelated reservation, so a later disjointness test would fail where it should succeed. Linking more than two units, or re-attaching a unit checked in an earlier run, goes through `checkExtScope`, which tests that one scope is a subset of another (`IntSet.isSubsetOf`) and produces the `Ext` evidence. Its haddock states what it trusts: raw names from independently built scopes mean the same variable only under a deterministic reservation policy, and the test cannot check the policy itself.

  `containers >= 0.6.8` is now required, for `Data.IntSet.fromRange`.

Changed:

- `convertToAST` and `convertToScopedAST` are deprecated in favour of `unsafeConvertToAST` and `unsafeConvertToScopedAST`, which are the same functions under names that admit they call `error`. The old names still work.

- **`mkFreeFoilConversions` now requires a `Bifoldable` instance for each signature**, since the generated `tryToX` needs one to walk a term collecting unresolved names. Every client in this repository already derives it alongside `Bifunctor`; one that does not will need `deriveBifoldable` on its signature.

# 0.3.3 — 2026-07-20

A bugfix and documentation release. Upgrading from 0.3.2 needs no work.

Fixes:

- Unifying two patterns that bind different numbers of names no longer throws `PatternMatchFail`. The `UnifiablePattern NameBinderList` instance covered only the empty/empty and cons/cons cases, and since the default `unifyPatterns` flattens every pattern to a `NameBinderList`, this was reachable from any language with patterns of differing arity: in `lambda-pi`, `alphaEquiv` on `λ_.x` and `λy.x` crashed. Such patterns are now reported as not unifiable, so the terms are not α-equivalent. The missing case went unnoticed because `Control.Monad.Foil.Internal` sets `-Wno-incomplete-patterns`.

Documentation:

- `UnifiablePattern` states what its class default compares. The default flattens both patterns to their binders, so it ignores the constructor (two patterns built from different constructors with the same number of binders unify), non-binding fields, and the nesting of sub-patterns (`(x, (y, z))` unifies with `((x, y), z)`). For most languages this is the intended α-equivalence, since what a body can refer to is exactly the pattern's binders in order, but every client gets it from an empty instance and nothing said so. The new `Control.Monad.Foil.UnifiablePatternSpec` pins the behaviour down.

- `withRefreshedPattern` and `withRefreshedPattern'` explain why they have no fast path for the case when every binder is already fresh in the ambient scope. Testing all binders at once and handing the continuation `sink` would be unsound: `addRename`'s delete is how a binder shadows an outer binding of the same raw name, and `sink` is a coercion that does not rename, so a binder can share a raw name with its own enclosing scope. `addRename` now says that its delete is not only an optimization.

Changed:

- `deriveUnifiablePattern` is deprecated. It reifies the raw (BNFC) pattern type and synthesises the scope-safe type and constructor names by prefixing `"Foil"`, and it errors on GADT constructors, so it cannot produce an instance for any pattern type `mkFoilPattern` or `mkFreeFoil` generates, nor for a hand-written pattern GADT. It has no call sites and predates the `GenericK` route clients use. Deprecated rather than removed, since `Control.Monad.Foil.TH` re-exports the module wholesale; removal is scheduled for the next major. Structural derivation of `UnifiablePattern` remains tracked in [#23](https://github.com/fizruk/free-foil/issues/23), and when it lands it will be opt-in rather than a new default, since changing the default would silently change α-equivalence for every existing client.

# 0.3.2 — 2026-07-15

An additive release: the annotation layer, the `ZipMatchK` derivers, and a set of performance improvements. Upgrading from 0.3.1 needs no work.

New:

- `Control.Monad.Free.Foil.Annotated`, a layer that annotates every node with an `ann term` built from the node's own term ([#42](https://github.com/fizruk/free-foil/pull/42), [#46](https://github.com/fizruk/free-foil/pull/46)). `Bifoldable` skips the annotation, so `alphaEquiv` is annotation-blind; `freeVarsOfAnnotated` sees the variables inside annotations that `freeVarsOf` skips. `AnnSig`'s `ZipMatchK` is derived rather than generic, since on an annotated signature it sits on a typechecker's hottest path. An annotation-blind instance must return `Just` lazily, and the module documents why a strict one is wrong.

- `Data.ZipMatchK.TH`, Template Haskell derivers for `ZipMatchK` ([#43](https://github.com/fizruk/free-foil/pull/43)). `deriveZipMatchK` zips every type parameter, `deriveZipMatchK2` the last two (for a signature with an annotation parameter), with `deriveZipMatchK1` and `deriveZipMatchKWith` for the rest. The generic instance rebuilds a `Generics.Kind` view of every node on every comparison, at a cost that grows with the number of constructors. The derived instance is flat, and on a 44-constructor signature runs `alphaEquiv` 1.8 times faster for 2.3 times less allocation. It replaces the deriver 0.3.0 dropped along with the old `ZipMatch` class.

- `sinkContainer` sinks a whole container of sinkables (an `IntMap` or `Map` of terms) in O(1) by coercion, instead of `fmap sink` over the spine ([#44](https://github.com/fizruk/free-foil/pull/44)). A `Scope` is not sinkable and a `NameMap` must stay total, both noted with the function.

- `zipmatchk` and `normalize` benchmarks ([#43](https://github.com/fizruk/free-foil/pull/43), [#45](https://github.com/fizruk/free-foil/pull/45)): `alphaEquiv` across signature sizes, and full β-normalisation of untyped λ-terms. CI builds them and does not run them.

Performance:

- `alphaEquiv` and `unsafeEqAST` no longer copy the node into a tuple before folding over it. They recurse inside the zipping functions, allocating nothing and short-circuiting on the first mismatch ([#44](https://github.com/fizruk/free-foil/pull/44)). On the benchmark, 294 µs to 217 µs and 3.1 MB to 2.8 MB with a derived instance. Behaviour is unchanged.

- `substitute`, `alphaEquiv`, `refreshAST` and friends are now `INLINABLE`, so a call site can specialise them for its own signature instead of passing dictionaries ([#44](https://github.com/fizruk/free-foil/pull/44)).

Changed:

- `soas` and `Language.LambdaPi.Impl.FreeFoilTH` derive their `ZipMatchK` instances. `Language.LambdaPi.Impl.FreeFoil` writes them out by hand, so the two implementations show both ways.

- The `base` lower bound is now `>= 4.19` (GHC 9.8). The package has required GHC 9.8 all along through `template-haskell >= 2.21`, so this only makes the bound honest, and lets Hackage's documentation builder pick a compatible GHC ([#15](https://github.com/fizruk/free-foil/issues/15)).

# 0.3.1 — 2026-07-14

A bug fix and a set of additions, all of them prompted by the projects built on free-foil. Nothing is removed or changed, so upgrading from 0.3.0 needs no work.

Fixes:

- `mkFreeFoil` and `mkFreeFoilConversions` generated ill-typed code for a raw constructor whose shape does not line up with the free foil node it becomes (see [#38](https://github.com/fizruk/free-foil/pull/38)):

  ```
  Let    ::= Pattern Term ScopedTerm        -- a term between the pattern and its scope
  LetRec ::= Pattern ScopedTerm ScopedTerm  -- one pattern binding two scopes
  ```

  - The pattern synonym's arguments and its type signature were computed by two traversals that disagreed, and the conversions had the mirror problem.
  - A constructor binding several scopes binds the same raw name in each of them, so raw-to-foil now sends that one binder into every scoped child, and foil-to-raw reads it back from the first.
  - Constructors with at most one scoped child generate exactly what they did before.
  - Reported and diagnosed by [@AbsoluteNikola](https://github.com/AbsoluteNikola), who had to vendor the generated code by hand in [free-foil-refinement-types](https://github.com/AbsoluteNikola/free-foil-refinement-types).

New functions, absorbed from the projects built on free-foil, several of which were importing `Control.Monad.Foil.Internal` to get at them (see [#40](https://github.com/fizruk/free-foil/pull/40)):

- `popNameBinder` — the inverse of `addNameBinder`, for leaving a binder.
- `withFreshNameBinderList` — a fresh binder for each element of a list, bound to it in a `NameMap`.
- `snocNameBinderList` and `concatNameBinderLists`.
- `nameBindersList`, `fromNameBindersList` and `nameMapToScope` are now exported (they existed, but were unreachable).
- With thanks to [@Probirochniy](https://github.com/Probirochniy), [@fedor-ivn](https://github.com/fedor-ivn) and [@snejugal](https://github.com/snejugal) ([free-foil-hou](https://github.com/fedor-ivn/free-foil-hou)), and to [@evermake](https://github.com/evermake), [@frog-da](https://github.com/frog-da) and [@Vikono](https://github.com/Vikono) ([free-foil-typecheck](https://github.com/evermake/free-foil-typecheck)), whose copies of these helpers carried the comment *"Should be in `Control.Monad.Foil`"*.

Documentation:

- `unifyNameBinders` renames the binder with the larger name towards the one with the smaller name. That is safe, since the renaming is pushed through a term with `liftRM`, which refreshes a binder whenever it would capture. The haddock now says so, with a test to match (see [#39](https://github.com/fizruk/free-foil/pull/39)). Raised by [@AbsoluteNikola](https://github.com/AbsoluteNikola).

# 0.3.0 — 2026-07-14

This release makes generic deriving the default way to instantiate the library:
`Sinkable`, `CoSinkable`, `UnifiablePattern` and `ZipMatchK` can now all be
derived via [`kind-generics`](https://hackage.haskell.org/package/kind-generics),
so a user-defined pattern normally needs no hand-written instances at all.
The cost is one breaking change, described first.

## Breaking changes

- The `ZipMatch` class is **removed** in favour of the kind-polymorphic `ZipMatchK`,
  and the modules are reorganised (see [#30](https://github.com/fizruk/free-foil/pull/30)):

  - `Control.Monad.Free.Foil.Generic` is replaced by `Data.ZipMatchK`
    (with `Data.ZipMatchK.Bifunctor`, `Data.ZipMatchK.Functor`,
    `Data.ZipMatchK.Generic` and `Data.ZipMatchK.Mappings`);
  - `Control.Monad.Free.Foil.TH.ZipMatch` (and its `deriveZipMatch`) is removed,
    and `Control.Monad.Free.Foil.TH` no longer re-exports it.

  To migrate, delete the `ZipMatch` instances and any `deriveZipMatch` splices,
  and keep only the `ZipMatchK` ones. Where you had

  ```haskell
  import Control.Monad.Free.Foil.Generic

  instance ZipMatchK a => ZipMatchK (TermSig a)
  instance ZipMatchK a => ZipMatch  (TermSig a) where zipMatch = genericZipMatch2
  ```

  the second instance simply goes away:

  ```haskell
  import Data.ZipMatchK

  instance ZipMatchK a => ZipMatchK (TermSig a)
  ```

  `ZipMatchK` is derived generically, so the signature needs a `GenericK` instance
  (`deriveGenericK ''TermSig` from `kind-generics-th`). Note that `kind-generics-th`
  is not on Stackage, and is not a dependency of this library: a package using
  `deriveGenericK` must depend on it itself.

- α-equivalence and refreshing now ask for more of the binder: `alphaEquiv`,
  `alphaEquivRefreshed`, `refreshAST` and `refreshScopedAST` require
  `SinkableK binder` (and `ZipMatchK sig` in place of `ZipMatch sig`).
  For binders and patterns generated by our Template Haskell, or derived generically,
  this constraint is already satisfied and no change is needed.

## Generic deriving of patterns (see [#31](https://github.com/fizruk/free-foil/pull/31))

- New `SinkableK` class, generalising both `Sinkable` and `CoSinkable`:
  a type `f n₁ n₂ … nₖ` is treated as a generalised binder with variables and terms
  in scopes `n₁, n₂, …, nₖ`. Generic (kind-polymorphic) implementations are provided
  for `sinkabilityProof` and `coSinkabilityProof`, so `Sinkable` and `CoSinkable`
  instances can be left empty.
- New `HasNameBinders` class, generalising access to the nested `NameBinder`s of a pattern.
  This is what makes a *generic* `withPattern` possible, so user-defined patterns
  no longer need a hand-written traversal.
- `UnifiablePattern` now has a default implementation via `CoSinkable`,
  so `instance UnifiablePattern MyPattern` normally suffices.
- Malformed user-defined patterns are now rejected with a readable type error
  by a separate generic check (`GValidNameBinders`), instead of failing obscurely
  deeper in the machinery. Terms (and other types) are allowed in patterns,
  as long as the binders are threaded correctly.

## New functions (see [#32](https://github.com/fizruk/free-foil/pull/32))

- `unsinkAST` — unsink an `AST` from a larger scope into a smaller one, when possible.
- `freeVarsOf` and `freeVarsOfScopedAST` — collect the free variables of an `AST`.
- `nameMapToScope` — recover a `Scope` from a `NameMap`.
- `NameMap` is now a `Functor`, `Foldable` and `Traversable`.

## Fixes

- `GValidNameBinders` no longer rejects a valid constructor that equates its scopes
  and carries more than one field (substitution now recurses through sums and products).

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
