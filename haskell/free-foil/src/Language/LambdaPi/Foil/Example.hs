{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-} -- Убрать
{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- Убрать
module Language.LambdaPi.Foil.Example where

import Data.String (IsString)

import Language.LambdaPi.Foil (Scope(..), Name (UnsafeName), NameBinder(UnsafeNameBinder)
                            , Distinct
                            , Sinkable(..), CoSinkable(..), nameOf, ppName)
import Language.LambdaPi.Foil.TH
import Unsafe.Coerce (unsafeCoerce)


data Term
  = Var VarIdent
  | Lit !Int
  | App Term Term
  | Lam Pattern ScopedTerm
  deriving (Show)

data Pattern
  = PatternVar VarIdent
  | PatternPair Pattern Pattern
  | PatternLit !Int
  deriving (Show)

newtype VarIdent = VarIdent String
  deriving newtype (Show, Eq, IsString)

data ScopedTerm = ScopedTerm Term
  deriving (Show)

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoilPattern ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern

-- toFoilTerm :: Distinct n => (VarIdent -> Name n) -> Scope n -> Term -> FoilTerm n
-- toFoilTerm toName scope = \case
--     Var x -> FoilVar (toName x)
--     Lit n -> FoilLit n
--     App fun arg -> FoilApp (toFoilTerm toName scope fun) (toFoilTerm toName scope arg)
--     Lam pat scopedTerm -> withPattern toName scope pat $ \pat' toName' scope' ->
--       FoilLam pat' (toFoilScopedTerm toName' scope' scopedTerm)

-- withPattern toName scope pat $ \pat' toName' scope' -> pat'

-- withPattern
--   :: Distinct n
--   => (VarIdent -> Name n)
--   -> Scope n
--   -> Pattern
--   -> (forall l. Distinct l => FoilPattern n l -> (VarIdent -> Name l) -> Scope l -> r)
--   -> r
-- withPattern toName scope pat cont =
--   case pat of
--     PatternVar var ->
--       withFresh scope $ \binder ->
--         let scope' = extendScope binder scope
--             toName' x
--               | x == var = nameOf binder
--               | otherwise = sink (toName x)
--             pat' = FoilPatternVar binder
--         in cont pat' toName' scope'

--     PatternPair pat1 var1 pat2 ->
--       withPattern toName scope pat1 $ \pat1' toName' scope' ->
--         withFresh scope' $ \binder1 ->
--         let scope'' = extendScope binder1 scope'
--             toName'' x
--               | x == var1 = nameOf binder1
--               | otherwise = sink (toName' x)
--         in withPattern toName'' scope'' pat2 $ \pat2' toName''' scope''' ->
--           let pat' = FoilPatternPair pat1' binder1 pat2'
--           in cont pat' toName''' scope'''

--     PatternLit n ->
--       let pat' = FoilPatternLit n
--       in cont pat' toName scope


-- toFoilPattern0 :: NameBinder n l -> Pattern -> FoilPattern n n1 l
-- toFoilPattern0 binder = \case
--   PatternVar _ -> FoilPatternVar binder
--   PatternLit n -> FoilPatternLit n

-- toFoilPattern2 :: NameBinder n n1 -> NameBinder n1 l -> Pattern -> FoilPattern n n1 l
-- toFoilPattern2 binder1 binder2 = \case
--   PatternPair _ _ -> FoilPatternPair binder1 binder2

-- toFoilScopedTerm :: Distinct n => (VarIdent -> Name n) -> Scope n -> ScopedTerm -> FoilScopedTerm n
-- toFoilScopedTerm toName scope = \case
--   ScopedTerm term -> FoilScopedTerm (toFoilTerm toName scope term)


-- fromFoilTerm :: FoilTerm n -> Term
-- fromFoilTerm = \case
--   FoilVar x -> Var (VarIdent (ppName x))
--   FoilLit n -> Lit n
--   FoilApp fun arg -> App (fromFoilTerm fun) (fromFoilTerm arg)
--   FoilLam pat scopedTerm -> Lam (fromFoilPattern pat) (fromFoilScopedTerm scopedTerm)

-- fromFoilPattern :: FoilPattern n n1 l -> Pattern
-- fromFoilPattern = \case
--     FoilPatternVar (UnsafeNameBinder binder) -> PatternVar (VarIdent (ppName binder))
--     FoilPatternPair (UnsafeNameBinder binder1) (UnsafeNameBinder binder2)
--       -> PatternPair (VarIdent (ppName binder1)) (VarIdent (ppName binder2))
--     FoilPatternLit n -> PatternLit n

-- fromFoilScopedTerm :: FoilScopedTerm n -> ScopedTerm
-- fromFoilScopedTerm = \case
  -- FoilScopedTerm term -> ScopedTerm (fromFoilTerm term)

-- instance Sinkable FoilTerm where
--   sinkabilityProof :: (Name n -> Name l) -> FoilTerm n -> FoilTerm l
--   sinkabilityProof f (FoilVar n) = FoilVar (f n)
--   sinkabilityProof _ (FoilLit i) = FoilLit i
--   sinkabilityProof f (FoilApp t1 t2) = FoilApp (sinkabilityProof f t1) (sinkabilityProof f t2)
--   sinkabilityProof f (FoilLam pattern body) =
--     extendRenamingPattern f pattern $ \f' pattern' ->
--       FoilLam pattern' (sinkabilityProof f' body)

-- TODO:
-- 1. Why not a typeclass for patterns and name binders (CoSinkable?)?
-- 2. How do they implement it in Dex?
-- 3. Is it always safe to use unsafeCoerce here?

-- extendRenamingPattern
--   :: (Name n -> Name n')
--   -> FoilPattern n l
--   -> (forall l'. (Name l -> Name l') -> FoilPattern n' l' -> r)
--   -> r
-- extendRenamingPattern _ pattern cont =
--   cont unsafeCoerce (unsafeCoerce pattern)

-- instance Sinkable (FoilPattern n t1) where
--   sinkabilityProof :: (Name n2 -> Name l) -> FoilPattern n1 t1 n2 -> FoilPattern n1 t1 l
--   sinkabilityProof f (FoilPatternPair (UnsafeNameBinder _) (UnsafeNameBinder var2)) = FoilPatternVar (UnsafeNameBinder (f var2))
--   sinkabilityProof f (FoilPatternVar (UnsafeNameBinder var)) = FoilPatternVar (UnsafeNameBinder (f var))
--   sinkabilityProof _ (FoilPatternLit i) = FoilPatternLit i

-- instance Sinkable FoilScopedTerm where
--   sinkabilityProof :: (Name n -> Name l) -> FoilScopedTerm n -> FoilScopedTerm l
--   sinkabilityProof f (FoilScopedTerm t) = FoilScopedTerm (sinkabilityProof f t)


-- substitute :: Distinct o => FoilTerm o -> FoilTerm i -> FoilTerm o
-- substitute substTerm = \case
--   FoilVar name -> substTerm
--   FoilLit n -> substTerm
--   FoilApp term1 term2 -> substTerm
--   FoilLam (FoilPatternLit pat) (FoilScopedTerm term) -> substTerm
--   FoilLam (FoilPatternPair pat1 pat2) (FoilScopedTerm term) -> FoilLam (FoilPatternPair pat1 pat2) (FoilScopedTerm term)
--   FoilLam (FoilPatternVar pat) (FoilScopedTerm term) -> substituteHelper substTerm (nameOf pat) term


-- substituteHelper :: FoilTerm o -> Name i -> FoilTerm i -> FoilTerm o
-- substituteHelper substTerm substName = \case
--   FoilVar name
--     | ppName name == ppName substName -> substTerm
--     | otherwise -> FoilVar (UnsafeName (ppName name))
--   FoilLit n -> FoilLit n
--   FoilApp term1 term2 -> FoilApp (substituteHelper substTerm substName term1) (substituteHelper substTerm substName term2)
--   FoilLam (FoilPatternLit pat) (FoilScopedTerm term) -> FoilLam (FoilPatternLit pat) (FoilScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
--   FoilLam (FoilPatternPair pat1 pat2) (FoilScopedTerm term) -> FoilLam (FoilPatternPair pat1 pat2) (FoilScopedTerm term)
--   FoilLam (FoilPatternVar pat) (FoilScopedTerm term)
--     | ppName (nameOf pat) == ppName substName -> substituteHelper substTerm (UnsafeName (ppName substName)) term
--     | otherwise -> FoilLam (FoilPatternVar newPat) (FoilScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
--       where
--         newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))


-- type FoilPatternArg n l = Either (NameBinder n l) (FoilPattern n l)
-- data NameBinderSeq n l =  ANameBinderSeq {first :: forall tn . FoilPatternArg n tn,
--                                           next :: forall ti tj tk . FoilPatternArg ti tj -> FoilPatternArg tj tk,
--                                           last :: forall ti tj . FoilPatternArg ti tj -> FoilPatternArg tj l}

-- toFoilPattern :: forall n l . NewBinderSeq n l -> Pattern -> FoilPattern n l
-- toFoilPattern (ANewBinderSeq first _ _) (PatternVar _) = 
--   case first of 
--     Left leftFirst -> FoilPatternVar leftFirst
-- toFoilPattern (ANewBinderSeq first _ last) (PatternPair _ _ ) = 
--   case first of 
--     Right rightFirst -> 
--       case last first of 
--         Right rightSecond -> FoilPatternPair rightFirst rightSecond

toFoilPattern0 :: forall n . Pattern -> FoilPattern n n
toFoilPattern0 (PatternLit n) = FoilPatternLit n

two :: Term
two = Lam (PatternVar "s") (ScopedTerm (Lam (PatternVar "z") (ScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

foilTwo :: FoilTerm n
foilTwo = FoilLam
            (FoilPatternVar (UnsafeNameBinder (UnsafeName "s")))
            (FoilScopedTerm (FoilLam
                              (FoilPatternVar (UnsafeNameBinder (UnsafeName "s")))
                              (FoilScopedTerm (FoilApp
                                                  (FoilVar (UnsafeName "s"))
                                                  (FoilApp
                                                      (FoilVar (UnsafeName "s"))
                                                      (FoilVar (UnsafeName "s")))))))

foilThree :: Name n
foilThree = UnsafeName "s" :: Name n

foilFour :: FoilTerm n
foilFour = FoilVar (UnsafeName "zz" :: Name n)

func :: VarIdent -> Name n
func (VarIdent s) = UnsafeName s :: Name n
