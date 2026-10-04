{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | The laws of "Control.Monad.Foil.Laws" and "Control.Monad.Free.Foil.Laws"
-- for the terms of second-order abstract syntax ("Language.SOAS.Impl.Generated"):
-- operators with scoped arguments, metavariables, and lists of binders,
-- whose 'Control.Monad.Foil.CoSinkable' instance 'Control.Monad.Free.Foil.TH.mkFreeFoil'
-- generates.
module Language.SOAS.LawsSpec (spec) where

import           Data.List                     (intercalate)
import           Test.Hspec

import           Control.Monad.Foil
import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.Laws
import           Language.SOAS.Impl.Generated
import qualified Language.SOAS.Syntax.Abs      as Raw

-- | Lists of up to three hinted binders.
genBinders :: GenPattern (Binders' Raw.BNFC'Position)
genBinders ctx = do
  PatIn binders <- genNameBinderList ctx
  pure (PatIn (fromList binders))
  where
    fromList :: NameBinderList n l -> Binders' Raw.BNFC'Position n l
    fromList = \case
      NameBinderListEmpty         -> NoBinders Nothing
      NameBinderListCons b rest -> SomeBinders Nothing b (fromList rest)

-- | Two lists of binders of the same length.
genBindersPair :: GenPatternPair (Binders' Raw.BNFC'Position)
genBindersPair ctx = do
  PatPair l r <- genNameBinderListPair ctx
  pure (PatPair (fromList l) (fromList r))
  where
    fromList :: NameBinderList n l -> Binders' Raw.BNFC'Position n l
    fromList = \case
      NameBinderListEmpty         -> NoBinders Nothing
      NameBinderListCons b rest -> SomeBinders Nothing b (fromList rest)

-- | The names of a list of binders, in order.
bindersNames :: PatternNames (Binders' a)
bindersNames = \case
  NoBinders _            -> []
  SomeBinders _ b rest   -> nameId (nameOf b) : bindersNames rest

-- | Terms with a few operators and metavariables. Locations are 'Nothing'.
termSyntax :: SyntaxGen (Binders' Raw.BNFC'Position) (Term'Sig Raw.BNFC'Position)
termSyntax = SyntaxGen
  { sgShapes =
      [ OpSig loc (Raw.OpIdent "Lam") [OpArgSig loc ()]
      , OpSig loc (Raw.OpIdent "App") [PlainOpArgSig loc (), PlainOpArgSig loc ()]
      , OpSig loc (Raw.OpIdent "Let") [PlainOpArgSig loc (), OpArgSig loc ()]
      , OpSig loc (Raw.OpIdent "Unit") []
      , MetaVarSig loc (Raw.MetaVarIdent "?m") [(), ()]
      , MetaVarSig loc (Raw.MetaVarIdent "?n") []
      ]
  , sgPattern = genBinders
  , sgPatternNames = bindersNames
  , sgShowNode = \case
      OpSig _ (Raw.OpIdent op) args ->
        op <> "(" <> intercalate ", " (map showArg args) <> ")"
      MetaVarSig _ (Raw.MetaVarIdent m) ts ->
        m <> "[" <> intercalate ", " ts <> "]"
  }
  where
    loc = Nothing
    showArg = \case
      OpArgSig _ s      -> s
      PlainOpArgSig _ t -> t

spec :: Spec
spec = do
  describe "CoSinkable Binders" $ coSinkableSpec bindersNames genBinders extensionByCoercion
  describe "UnifiablePattern Binders" $
    unifyPatternsSpec bindersNames genBindersPair Holds
  describe "α-equivalence" $ alphaSpec termSyntax (const Holds)
  describe "relative monad" $ relMonadSpec termSyntax (\_ _ -> Holds)
  describe "functor" $ functorSpec termSyntax (\_ _ -> Holds) $ \cls -> \case
    SinkAgreesWithLiftRM -> sinkAgreesOnInclusions cls
    _                    -> Holds
