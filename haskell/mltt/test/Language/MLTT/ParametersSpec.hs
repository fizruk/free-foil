{-# LANGUAGE OverloadedStrings #-}
-- | Module parameters and discharge.
--
-- The property under test is that a declaration leaves a parametrised module
-- abstracted over exactly the parameters it uses, that this set is upward
-- closed in the telescope, and that an @over@ clause is checked against it
-- rather than believed.
module Language.MLTT.ParametersSpec (spec) where

import           Data.List          (isInfixOf)
import           Language.MLTT.Impl
import           Test.Hspec

-- | Interpret a program, reporting a parse error as a failed command.
run :: String -> [CommandResult]
run input = case interpret input of
  Left err      -> [Failed ("parse error: " <> err)]
  Right results -> results

-- | The messages of every command that was rejected.
failures :: [CommandResult] -> [String]
failures results = [err | Failed err <- results]

-- | The normal forms every @compute@ produced.
computed :: [CommandResult] -> [String]
computed results = [term | Computed term <- results]

-- | A monoid-shaped parameter block, and whatever declarations are given.
inMonoid :: [String] -> String
inMonoid decls = unlines
  ("module Monoid (A : 𝕌) (unit : A) (mul : A → A → A)" : decls)

spec :: Spec
spec = do
  describe "discharge" $ do
    it "abstracts a declaration over exactly the parameters it uses" $
      run (inMonoid ["def square : A → A := λ x ⇒ mul x x"])
        `shouldSatisfy` (Defined "square" ["A", "mul"] `elem`)

    it "leaves a declaration that uses no parameter a plain constant" $
      run (inMonoid ["def flip : 𝟙 → 𝟙 := λ x ⇒ x"])
        `shouldSatisfy` (Defined "flip" [] `elem`)

    it "keeps a parameter that only the value mentions, in the type as well" $
      -- The type `A` does not mention `unit`, the value does, and the two have
      -- to stay a matching pair.
      run (inMonoid ["def neutral : A := unit"])
        `shouldSatisfy` (Defined "neutral" ["A", "unit"] `elem`)

    it "closes the set upward: keeping a parameter keeps what its type needs" $
      -- Nothing in the body mentions `A`. Keeping `unit` puts `unit`'s type
      -- into the discharged type, and that type is `A`.
      run (inMonoid ["def neutral : 𝟙 → A := λ _ ⇒ unit"])
        `shouldSatisfy` (Defined "neutral" ["A", "unit"] `elem`)

  describe "the over clause" $ do
    it "accepts a clause that names exactly the parameters used" $
      failures (run (inMonoid ["def square over (A, mul) : A → A := λ x ⇒ mul x x"]))
        `shouldBe` []

    it "accepts it in any order, since the telescope fixes the real one" $
      failures (run (inMonoid ["def square over (mul, A) : A → A := λ x ⇒ mul x x"]))
        `shouldBe` []

    it "rejects a clause that omits a parameter, and reports the computed set" $
      failures (run (inMonoid ["def square over (mul) : A → A := λ x ⇒ mul x x"]))
        `shouldSatisfy` any (\err -> "declared: over (mul)" `isInfixOf` err
                                  && "actual: over (A, mul)" `isInfixOf` err)

    it "rejects a clause that names a parameter the declaration does not use" $
      failures (run (inMonoid ["def flip over (A) : 𝟙 → 𝟙 := λ x ⇒ x"]))
        `shouldSatisfy` any ("actual: over ()" `isInfixOf`)

    it "rejects a clause that omits what the closure adds" $
      failures (run (inMonoid ["def neutral over (unit) : A := unit"]))
        `shouldSatisfy` any ("actual: over (A, unit)" `isInfixOf`)

  describe "what leaves the module" $ do
    it "is closed, so a client instantiates it by application" $
      computed (run (unlines
        [ inMonoid ["def neutral : A := unit"]
        , "module Client"
        , "import Monoid"
        , "compute neutral 𝟙 tt" ]))
        `shouldBe` ["tt"]

    it "does not carry the parameters into the client's scope" $
      failures (run (unlines
        [ inMonoid ["def neutral : A := unit"]
        , "module Client"
        , "import Monoid"
        , "compute unit" ]))
        `shouldSatisfy` any ("not in scope: unit" `isInfixOf`)

  describe "checking under parameters" $ do
    it "lets a check see them" $
      failures (run (inMonoid ["check unit : A"]))
        `shouldBe` []

  describe "putting the parameters back on use" $ do
    it "lets a later declaration name an earlier one without applying it" $
      failures (run (inMonoid
        [ "def neutral : A := unit"
        , "def alsoNeutral : A := neutral" ]))
        `shouldBe` []

    it "counts the arguments it puts back as uses" $
      -- `square` takes `A` and `mul`, `neutral` takes `A` and `unit`, so a
      -- declaration naming both is closed over all three.
      run (inMonoid
        [ "def square : A → A := λ x ⇒ mul x x"
        , "def neutral : A := unit"
        , "def squareNeutral : A := square neutral" ])
        `shouldSatisfy` (Defined "squareNeutral" ["A", "unit", "mul"] `elem`)

    it "leaves a local binder of the same name alone" $
      run (inMonoid ["def shadowing : 𝟙 → 𝟙 := λ square ⇒ square"])
        `shouldSatisfy` (Defined "shadowing" [] `elem`)

    it "leaves a parameter alone when it shadows a declaration of the same name" $
      -- `dup` is both a parameter and a declaration. The spelling denotes the
      -- parameter, so putting anything back for it would be wrong.
      run (unlines
        [ "module M (A : 𝕌) (dup : A)"
        , "def dup : A := dup"
        , "def use : A := dup" ])
        `shouldSatisfy` (Defined "use" ["A", "dup"] `elem`)

    it "does not do it for a client, which applies the constant itself" $
      failures (run (unlines
        [ inMonoid ["def neutral : A := unit"]
        , "module Client"
        , "import Monoid"
        , "check neutral : Π (A : 𝕌) → Π (unit : A) → A" ]))
        `shouldBe` []

    it "reports an unresolvable parameter type once, not once per declaration" $
      failures (run (unlines
        [ "module M (x : Nope)"
        , "def a : 𝟙 := tt"
        , "def b : 𝟙 := tt" ]))
        `shouldBe` ["not in scope: Nope"]
