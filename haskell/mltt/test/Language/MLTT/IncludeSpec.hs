{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Named telescopes and the @include@ clause.
--
-- A telescope declaration names a block of module parameters, and an include
-- puts that block at the front of an including module's own. The property
-- under test is that nothing downstream of the parameter block changes: the
-- included fields are checked, discharged and reported exactly as parameters
-- written out by hand, and an include behaves like an import for staleness.
module Language.MLTT.IncludeSpec (spec) where

import           Data.List                    (isInfixOf)
import           System.Directory             (getTemporaryDirectory,
                                               removePathForcibly)
import           System.FilePath              ((</>))
import           Test.Hspec

import           Language.MLTT.Build
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText (..), sourceLines)

-- | Interpret a program, reporting a parse error as a failed command.
run :: String -> [CommandResult]
run input = case interpret (SourceText input) of
  Left err      -> [Failed ("parse error: " <> err)]
  Right results -> results

-- | The messages of every command that was rejected.
failures :: [CommandResult] -> [String]
failures results = [err | Failed err <- results]

-- | A monoid telescope, and whatever units are given after it.
withMonoid :: [String] -> String
withMonoid units = unlines
  ("telescope Monoid (A : 𝕌) (unit : A) (mul : A → A → A)" : units)

-- | A theory carrying a law, a lemma proved once in it, and an instance: the
-- Church numerals under addition, whose associativity holds on the nose.
theoryAndInstance :: String
theoryAndInstance = unlines
  [ "telescope Monoid (A : 𝕌) (mul : A → A → A)"
  , "  (assoc : Π (x : A) → Π (y : A) → Π (z : A)"
  , "         → Id(A, mul (mul x y) z, mul x (mul y z)))"
  , ""
  , "module Theory include Monoid"
  , "def square : A → A := λ x ⇒ mul x x"
  , "def squareAssoc : Π (x : A) → Id(A, mul (square x) x, mul x (square x))"
  , "  := λ x ⇒ assoc x x x"
  , ""
  , "module Church"
  , "def Nat : 𝕌 := Π (A : 𝕌) → (A → A) → A → A"
  , "def plus : Nat → Nat → Nat := λ m ⇒ λ n ⇒ λ A ⇒ λ f ⇒ λ x ⇒ m A f (n A f x)"
  , "def plusAssoc : Π (a : Nat) → Π (b : Nat) → Π (c : Nat)"
  , "              → Id(Nat, plus (plus a b) c, plus a (plus b c))"
  , "  := λ a ⇒ λ b ⇒ λ c ⇒ refl (plus (plus a b) c)"
  , ""
  , "module Client"
  , "import Theory"
  , "import Church"
  , "check squareAssoc Nat plus plusAssoc"
  , "    : Π (x : Nat) → Id(Nat, plus (plus x x) x, plus x (plus x x))"
  ]

spec :: Spec
spec = do
  describe "a module that includes a telescope" $ do
    it "is discharged over the included fields it uses" $
      run (withMonoid
            [ "module CommMonoid include Monoid"
            , "def square : A → A := λ x ⇒ mul x x" ])
        `shouldSatisfy` (Defined "square" ["A", "mul"] `elem`)

    it "puts the included fields before the ones it declares itself" $
      -- `inv` is the module's own and comes last, whatever it is used with.
      run (withMonoid
            [ "module Group include Monoid (inv : A → A)"
            , "def undo : A → A := λ x ⇒ mul x (inv x)" ])
        `shouldSatisfy` (Defined "undo" ["A", "mul", "inv"] `elem`)

    it "lets a parameter of its own mention an included field" $
      -- `inv : A → A` only resolves because `A` is already in the telescope.
      failures (run (withMonoid
            [ "module Group include Monoid (inv : A → A)"
            , "def unitInverse : A := inv unit" ]))
        `shouldBe` []

    it "may include a telescope declared after it" $
      -- Telescopes are resolved over the whole program, as imports are.
      failures (run (unlines
            [ "module M include Monoid"
            , "def square : A → A := λ x ⇒ mul x x"
            , ""
            , "telescope Monoid (A : 𝕌) (unit : A) (mul : A → A → A)" ]))
        `shouldBe` []

    it "shares nothing with another includer but the source" $
      -- Each module elaborates the telescope afresh, so what leaves them are
      -- two unrelated closed constants that a client instantiates separately.
      run (withMonoid
            [ "module One include Monoid"
            , "def sq : A → A := λ x ⇒ mul x x"
            , ""
            , "module Two include Monoid"
            , "def dup : A → A := λ x ⇒ mul x x"
            , ""
            , "module Client"
            , "import One"
            , "import Two"
            , "compute sq 𝟙 (λ x ⇒ λ y ⇒ x) tt"
            , "compute dup 𝟙 (λ x ⇒ λ y ⇒ x) tt" ])
        `shouldSatisfy` ([Computed "tt", Computed "tt"] ==)
          . filter isComputed

  describe "a theory and an instance" $ do
    it "discharges a lemma over the law field it uses, and not otherwise" $
      -- `square` needs the operation; `squareAssoc` needs the law as well.
      -- Nothing declares this, and nothing has to: it is what discharge finds.
      run theoryAndInstance `shouldSatisfy` \results ->
        Defined "square" ["A", "mul"] `elem` results
          && Defined "squareAssoc" ["A", "mul", "assoc"] `elem` results

    it "applies the theory's lemma at the instance, which is application" $
      -- The instance supplies the carrier, the operation and its own proof of
      -- the law, in telescope order. There is no interpretation step.
      failures (run theoryAndInstance) `shouldBe` []

  describe "a telescope that includes a telescope" $ do
    it "puts the included fields first, so a theory extends a poorer one" $
      -- The monoid block is the semigroup block with a unit after it, and a
      -- declaration in it is discharged in that order.
      run (unlines
            [ "telescope Semigroup (A : 𝕌) (mul : A → A → A)"
            , "telescope Monoid include Semigroup (unit : A)"
            , "module M include Monoid"
            , "def scaled : A → A := λ x ⇒ mul unit x" ])
        `shouldSatisfy` (Defined "scaled" ["A", "mul", "unit"] `elem`)

    it "expands a chain of includes, dependencies first" $
      -- Sterling's hierarchy, in miniature: Magma, Semigroup, Monoid.
      run (unlines
            [ "telescope Magma (A : 𝕌) (mul : A → A → A)"
            , "telescope Semigroup include Magma (e : A)"
            , "telescope Monoid include Semigroup (z : A)"
            , "module M include Monoid"
            , "def pick : A := mul e z" ])
        `shouldSatisfy` (Defined "pick" ["A", "mul", "e", "z"] `elem`)

    it "may include a telescope declared after it" $
      -- Telescopes are expanded in dependency order, not source order.
      failures (run (unlines
            [ "telescope Monoid include Semigroup (unit : A)"
            , "telescope Semigroup (A : 𝕌) (mul : A → A → A)"
            , "module M include Monoid"
            , "def u : A := unit" ]))
        `shouldBe` []

    it "composes with refinement, since refining yields a parameter list" $
      run (unlines
            [ "telescope Semigroup (A : 𝕌) (mul : A → A → A)"
            , "telescope Pointed include Semigroup / {A := 𝟙} (p : A)"
            , "module M include Pointed"
            , "def pick : A := p" ])
        `shouldSatisfy` (Defined "pick" ["p"] `elem`)

    it "reports a cycle by naming it" $
      failures (run (unlines
            [ "telescope A include B (x : 𝕌)"
            , "telescope B include A (y : 𝕌)"
            , "module M include A"
            , "def u : 𝟙 := tt" ]))
        `shouldBe` ["telescopes include each other in a cycle: A -> B -> A"]

    it "reports a self-include as the smallest cycle" $
      failures (run (unlines
            [ "telescope T include T (x : 𝕌)"
            , "module M include T"
            , "def u : 𝟙 := tt" ]))
        `shouldBe` ["telescopes include each other in a cycle: T -> T"]

    it "reports a missing telescope in a telescope's include" $
      failures (run (unlines
            [ "telescope T include Nope (x : 𝕌)"
            , "module M include T"
            , "def u : 𝟙 := tt" ]))
        `shouldBe` ["no telescope named Nope is declared"]

  describe "refining an include" $ do
    it "makes a fixed field manifest, so nothing is discharged over it" $
      -- `A` is fixed, so `square` takes the operation and not the carrier.
      run (withMonoid
            [ "module M include Monoid / {A := 𝟙}"
            , "def square : A → A := λ x ⇒ mul x x" ])
        `shouldSatisfy` (Defined "square" ["mul"] `elem`)

    it "leaves nothing to discharge when every field is fixed" $
      -- Fixing the whole block is what an instance is.
      run (withMonoid
            [ "module M include Monoid / {A := 𝟙, unit := tt, mul := λ x ⇒ λ y ⇒ x}"
            , "def twice : A → A := λ x ⇒ mul x x" ])
        `shouldSatisfy` (Defined "twice" [] `elem`)

    it "lets the type of a later field use a fixed one" $
      failures (run (withMonoid
            [ "module M include Monoid / {A := 𝟙}"
            , "def u : A := unit" ]))
        `shouldBe` []

    it "refuses a value that names a field of the telescope" $
      -- The admissibility condition, and Sterling's diagonal: a supplied value
      -- must come from the ambient context, so it cannot name a field that is
      -- still a variable. Nothing tests this — the value is elaborated before
      -- any of the block's binders, so the name is simply not in scope.
      failures (run (withMonoid
            [ "module M include Monoid / {A := 𝟙, unit := mul}"
            , "def x : 𝟙 := tt" ]))
        `shouldBe` ["cannot fix unit: it depends on mul, which is not fixed"]

    it "refuses fixing a field whose type is not fixed" $
      -- The same condition reaching the field's type rather than its value:
      -- `unit : A`, so fixing `unit` while `A` is a variable is not admissible.
      -- The fixed fields have to be closed under what they depend on.
      failures (run (withMonoid
            ["module M include Monoid / {unit := tt}", "def x : 𝟙 := tt"]))
        `shouldBe` ["cannot fix unit: it depends on A, which is not fixed"]

    it "checks a fixed value against the field's declared type" $
      failures (run (withMonoid
            ["module M include Monoid / {A := 𝟙, unit := 𝕌}", "def x : 𝟙 := tt"]))
        `shouldSatisfy` any ("expected type: 𝟙" `isInfixOf`)

    it "reports a field the telescope does not have" $
      failures (run (withMonoid
            ["module M include Monoid / {B := 𝟙}", "def x : 𝟙 := tt"]))
        `shouldBe` ["telescope Monoid has no field B"]

    it "reports a field fixed twice" $
      failures (run (withMonoid
            ["module M include Monoid / {A := 𝟙, A := 𝕌}", "def x : 𝟙 := tt"]))
        `shouldBe` ["field fixed twice: A"]

  describe "a telescope that is not there" $ do
    it "is reported, naming it" $
      failures (run (unlines
            ["module M include Nope", "def x : 𝟙 := tt"]))
        `shouldBe` ["no telescope named Nope is declared"]

    it "is reported once, whatever the module goes on to declare" $
      length (failures (run (unlines
            ["module M include Nope", "def x : 𝟙 := tt", "def y : 𝟙 := tt"])))
        `shouldBe` 1

  describe "a telescope declared twice" $
    it "is reported rather than one of them silently winning" $
      failures (run (unlines
            [ "telescope T (A : 𝕌)"
            , "telescope T (B : 𝕌)"
            , "module M include T"
            , "def x : 𝟙 := tt" ]))
        `shouldBe` ["telescope declared twice: T"]

  describe "the cache" $
    it "treats a changed telescope as a changed import of its includers" $ do
      dir <- (</> "mltt-include-spec-cache") <$> getTemporaryDirectory
      removePathForcibly dir
      let telescope fields = ("Tele.mltt", sourceLines ["telescope T " <> fields])
          user = ("User.mltt", sourceLines
                    ["module M include T", "def x : A → A := λ y ⇒ y"])
          build src = buildSources Linked (Just dir) [telescope src, user]
      r1 <- build "(A : 𝕌)"
      fmap loadedNames r1 `shouldBe` Right []
      r2 <- build "(A : 𝕌)"
      fmap loadedNames r2 `shouldBe` Right ["M"]
      -- The module's own source is untouched; only the telescope it includes
      -- has changed, and that has to be enough to rebuild it.
      r3 <- build "(A : 𝕌) (a : A)"
      fmap loadedNames r3 `shouldBe` Right []
      fmap checkedNames r3 `shouldBe` Right ["M"]
  where
    isComputed = \case
      Computed _ -> True
      _          -> False

    loadedNames results = [name | LoadedModule name <- results]
    checkedNames results = [name | EnteredModule name <- results]
