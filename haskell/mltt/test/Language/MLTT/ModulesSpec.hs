{-# LANGUAGE OverloadedStrings #-}
-- | The module layer: build order, namespaces, qualified names, @open@, and
-- the distinction between what can be named and what can be reduced.
module Language.MLTT.ModulesSpec (spec) where

import           Control.Monad     (forM_)
import           Data.List         (isInfixOf)
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText (..))
import           Test.Hspec

-- | Interpret a program, reporting a parse error as a failed command so that
-- every assertion below can be made about the same list.
run :: String -> [CommandResult]
run input = case interpret (SourceText input) of
  Left err      -> [Failed ("parse error: " <> err)]
  Right results -> results

-- | The messages of every command that was rejected.
failures :: [CommandResult] -> [String]
failures results = [err | Failed err <- results]

-- | The normal forms every @compute@ produced.
computed :: [CommandResult] -> [RenderedTerm]
computed results = [term | Computed term <- results]

-- | Two modules: a Prelude with a private helper used by a public definition,
-- and a client that imports it.
withClient :: String -> String
withClient clientBody = unlines
  [ "module Prelude"
  , "namespace Nat where"
  , "  private def twice : Π (A : 𝕌) → (A → A) → A → A"
  , "    := λ A ⇒ λ f ⇒ λ x ⇒ f (f x)"
  , "  def quadruple : Π (A : 𝕌) → (A → A) → A → A"
  , "    := λ A ⇒ λ f ⇒ twice A (twice A f)"
  , ""
  , "module Client"
  , "import Prelude"
  , clientBody
  ]

spec :: Spec
spec = do
  describe "build order" $ do
    it "checks an imported module first, whatever the file order" $
      failures (run (unlines
        [ "module Client"
        , "import Prelude"
        , "compute Logic.id 𝟙 tt"
        , "module Prelude"
        , "namespace Logic where"
        , "  def id : Π (A : 𝕌) → A → A := λ A ⇒ λ x ⇒ x" ]))
        `shouldBe` []

    it "reports an import of a module that is not there" $
      failures (run "module A\nimport Nowhere\n")
        `shouldSatisfy` any ("imported module not found" `isInfixOf`)

    it "reports an import cycle instead of looping" $
      failures (run (unlines
        [ "module A", "import B"
        , "module B", "import A" ]))
        `shouldSatisfy` any ("import cycle" `isInfixOf`)

  describe "namespaces and qualified names" $ do
    it "qualifies a declaration by its namespace, not by its module" $
      run (withClient "check Nat.quadruple : Π (A : 𝕌) → (A → A) → A → A")
        `shouldSatisfy` (Defined "Nat.quadruple" [] `elem`)

    it "does not make a namespaced name available unqualified" $
      failures (run (withClient "compute quadruple 𝟙 (λ x ⇒ x) tt"))
        `shouldSatisfy` any ("not in scope: quadruple" `isInfixOf`)

    it "makes it available unqualified after open, without hiding the qualified spelling" $
      computed (run (withClient (unlines
        [ "open Nat"
        , "compute quadruple 𝟙 (λ x ⇒ x) tt"
        , "compute Nat.quadruple 𝟙 (λ x ⇒ x) tt" ])))
        `shouldBe` ["tt", "tt"]

    it "reaches a namespace nested inside a namespace by its full path" $
      computed (run (unlines
        [ "module M"
        , "namespace Outer where"
        , "  namespace Inner where"
        , "    def unit : 𝟙 := tt"
        , "compute Outer.Inner.unit" ]))
        `shouldBe` ["tt"]

  describe "narrowing: naming versus reducing" $ do
    it "lets a module name its own private declaration" $
      failures (run (unlines
        [ "module Prelude"
        , "private def secret : 𝟙 := tt"
        , "compute secret" ]))
        `shouldBe` []

    it "hides a private declaration from an importing module" $
      failures (run (withClient "compute Nat.twice 𝟙 (λ x ⇒ x) tt"))
        `shouldSatisfy` any ("not in scope: Nat.twice" `isInfixOf`)

    it "still reduces through that private declaration" $
      -- The client cannot write `Nat.twice`, and yet normalising
      -- `Nat.quadruple` has to unfold it to reach `tt`. Restricting the
      -- resolver's table leaves the terms, and δ-reduction, untouched.
      computed (run (withClient "compute Nat.quadruple 𝟙 (λ x ⇒ x) tt"))
        `shouldBe` ["tt"]

  describe "diagnostics" $ do
    it "suggests a qualified spelling for a bare one" $
      failures (run (withClient "compute quadruple 𝟙 (λ x ⇒ x) tt"))
        `shouldSatisfy` any ("did you mean Nat.quadruple?" `isInfixOf`)

    it "reports an unresolved name rather than crashing on an integer" $
      -- convertToAST used to call `error "undefined variable"` here.
      failures (run (unlines
        [ "module M"
        , "compute nowhere" ]))
        `shouldBe` ["not in scope: nowhere"]

  describe "printing" $
    it "does not confuse a bound variable with a definition of the same raw name" $
      -- A definition's body is elaborated before the definition's own name is
      -- allocated, so `f` and the `x` it binds are both raw name 0. Naming
      -- every occurrence of 0 after `f` used to print the body as `λ x0 ⇒ f`.
      computed (run (unlines
        [ "module M"
        , "def f : 𝟙 → 𝟙 := λ x ⇒ x"
        , "def g : 𝟙 := tt"
        , "compute f" ]))
        `shouldBe` ["λ x0 ⇒ x0"]

  describe "the example programs" $
    forM_ ["examples/core.mltt", "examples/modules.mltt", "examples/parameters.mltt"] $ \path ->
      it (path <> " is accepted in full") $ do
        input <- readFile path
        let results = run input
        forM_ (failures results) expectationFailure
        results `shouldSatisfy` (not . null)
