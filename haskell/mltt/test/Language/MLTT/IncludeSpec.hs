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
