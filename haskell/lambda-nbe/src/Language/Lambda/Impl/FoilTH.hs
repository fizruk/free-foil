{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeSynonymInstances                  #-}
{-# LANGUAGE FlexibleInstances                  #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
-- | Foil implementation of the \(\lambda\Pi\)-calculus (with pairs)
-- using Template Haskell and "Generics.Kind" to reduce boilerplate.
--
-- Template Haskell helpers __generate__ the following:
--
-- 1. Scope-safe AST, generated from a raw definition. See 'FoilTerm', 'FoilScopedTerm', and 'FoilPattern'.
-- 2. Conversion between scope-safe and raw term representation (the latter is generated via BNFC), see 'toFoilTerm'' and 'fromFoilTerm''.
-- 3. Helper functions for patterns. See 'extendScopeFoilPattern'' and 'withRefreshedFoilPattern''.
--
-- The following is provided via kind-polymophic generics (see "Generics.Kind"):
--
-- 1. 'Sinkable' instance for 'FoilTerm''.
-- 2. 'CoSinkable' instance for 'FoilPattern'', giving access to 'extendScopePattern' and 'withRefreshedPattern' (among other utilities).
--
-- The following is implemented __manually__ in this module:
--
-- 1. Correct capture-avoiding substitution (see 'substitute').
-- 2. Computation of weak head normal form (WHNF), see 'whnf'.
-- 3. Entry point, gluing everything together. See 'defaultMain'.
--
-- The following is __not implemented__:
--
-- 1. \(\alpha\)-equivalence checks and \(\alpha\)-normalization helpers.
--
-- This implementation supports (nested) patterns for pairs.
module Language.Lambda.Impl.FoilTH where


import           Control.Monad.Foil
import           Control.Monad.Foil.TH
import qualified Data.Map                        as Map
import Data.String (IsString(..))
import qualified Language.Lambda.Syntax.Abs    as Raw
import qualified Language.Lambda.Syntax.Layout as Raw
import qualified Language.Lambda.Syntax.Lex    as Raw
import qualified Language.Lambda.Syntax.Par    as Raw
import qualified Language.Lambda.Syntax.Print  as Raw
import           Generics.Kind.TH

-- * Generated code

-- ** Scope-safe AST
mkFoilData ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
-- mkInstancesFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

deriveGenericK ''FoilTerm'
deriveGenericK ''FoilScopedTerm'
deriveGenericK ''FoilPattern'
instance SinkableK (FoilTerm' a)
instance SinkableK (FoilScopedTerm' a)
instance SinkableK (FoilPattern' a)
instance HasNameBinders (FoilPattern' a)

instance Sinkable (FoilTerm' a)
instance CoSinkable (FoilPattern' a)

-- ** Conversion from raw to scope-safe AST
mkToFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

-- ** Conversion from scope-safe to raw AST
mkFromFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

type FoilTerm = FoilTerm' Raw.BNFC'Position
type FoilPattern = FoilPattern' Raw.BNFC'Position

-- | Convert a /closed/ scope-safe term into a raw term.
fromFoilTermClosed
  :: [Raw.VarIdent]   -- ^ A stream of fresh variable identifiers.
  -> FoilTerm VoidS       -- ^ A scope safe term in scope @n@.
  -> Raw.Term
fromFoilTermClosed freshVars = fromFoilTerm' freshVars emptyNameMap

instance InjectName (FoilTerm' a) where
  injectName = FoilVar (error "undefined location")

-- * User-defined

-- ** Substitution

-- | Perform substitution in a \(\lambda\Pi\)-term.
substitute :: Distinct o => Scope o -> Substitution FoilTerm i o -> FoilTerm i -> FoilTerm o
substitute scope subst = \case
    FoilVar _loc name -> lookupSubst subst name
    FoilApp loc f x -> FoilApp loc (substitute scope subst f) (substitute scope subst x)
    FoilLam loc1 pattern (FoilAScopedTerm loc2 body) -> withRefreshedPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          body' = substitute scope' subst' body
       in FoilLam loc1 pattern' (FoilAScopedTerm loc2 body')

-- ** Computation

-- | Match a pattern against an expression.
matchPattern :: FoilPattern n l -> FoilTerm n -> Substitution FoilTerm l n
matchPattern pattern expr = go pattern expr identitySubst
  where
    go :: FoilPattern i l -> FoilTerm n -> Substitution FoilTerm i n -> Substitution FoilTerm l n
    go (FoilPatternVar _loc x) e    = \subst -> addSubst subst x e

-- | Compute weak head normal form (WHNF).
--
-- >>> whnf emptyScope "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)"
-- λ x1 . λ x2 . x1
whnf :: Distinct n => Scope n -> FoilTerm n -> FoilTerm n
whnf scope = \case
  FoilApp loc f arg ->
    case whnf scope f of
      FoilLam _loc pat (FoilAScopedTerm _loc' body) ->
        let subst = matchPattern pat arg
         in whnf scope (substitute scope subst body)
      f' -> FoilApp loc f' arg
  t -> t

-- ** Pretty-printing

-- | Pretty-print a /closed/ scode-safe \(\lambda\Pi\)-term
-- using BNFC-generated printer (via 'Raw.Term').
printFoilTerm :: FoilTerm VoidS -> String
printFoilTerm = Raw.printTree . fromFoilTermClosed
  [ Raw.VarIdent ("x" <> show i) | i <- [1 :: Integer ..] ]

instance Show (FoilTerm VoidS) where
  show = printFoilTerm

-- ** Parsing

unsafeParseFoilTerm :: String -> FoilTerm VoidS
unsafeParseFoilTerm input =
  case Raw.pTerm (Raw.tokens input) of
    Left err -> error err
    Right term -> toFoilTerm' emptyScope Map.empty term

instance IsString (FoilTerm VoidS) where
  fromString = unsafeParseFoilTerm

-- ** Closure-representation

data Neutral n where
  NVar :: Name n -> Neutral n
  NApp :: Neutral n -> Value n -> Neutral n

data Value n where
  VClosure :: Substitution Value i o -> NameBinder i l -> FoilTerm l -> Value o
  VNeutral :: Neutral n -> Value n

instance InjectName Value where
  injectName = VNeutral . NVar

instance Sinkable Value where
  sinkabilityProof = undefined

quote :: Distinct n => Scope n -> Value n -> FoilTerm n
quote scope = \case
  VClosure env binder body ->
    withRefreshed scope (nameOf binder) $ \binder' ->
      let scope' = extendScope binder' scope
          env' = addRename (sink env) binder (nameOf binder')
      in FoilLam noLocation (FoilPatternVar noLocation binder') $
            FoilAScopedTerm noLocation (quote scope' (eval scope' env' body))
  VNeutral (NVar x) -> FoilVar noLocation x
  VNeutral (NApp neu val) -> FoilApp noLocation (quote scope (VNeutral neu)) (quote scope val)

eval :: Distinct o => Scope o -> Substitution Value i o -> FoilTerm i -> Value o
eval scope env = \case
  FoilVar _loc x -> lookupSubst env x
  FoilApp _loc f x ->
    case eval scope env f of
      VClosure env' binder body ->
        let arg = eval scope env x
            env'' = addSubst env' binder arg
         in eval scope env'' body
      VNeutral neu ->
        VNeutral (NApp neu (eval scope env x))
  FoilLam _loc (FoilPatternVar _ binder) (FoilAScopedTerm _ body) ->
    VClosure env binder body

noLocation :: Raw.BNFC'Position
noLocation = error "no location"

-- | Normal form.
-- 
-- >>> nf Foil.emptyScope "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)"
-- λ x1 . λ x2 . x1
nf :: Distinct n => Scope n -> FoilTerm n -> FoilTerm n
nf scope term = quote scope (eval scope identitySubst term)