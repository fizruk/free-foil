{-# LANGUAGE LambdaCase #-}
-- | Interned top-level constants.
--
-- This module is the difference between the two candidate designs for a global
-- environment. Here a top-level declaration is __not__ a name in a scope: it is
-- an interned identifier carried by a @Const@ node, which has no scope index of
-- its own. A checked declaration is therefore a @Term' a VoidS@ — closed by
-- /type/ rather than by discipline — and the foil index means the local context
-- only.
--
-- Resolving an identifier to a constant is not done here: free foil's generated
-- conversions take a table of identifiers that denote whole terms, so it
-- happens where the binders are already known. What is left is the read-back
-- direction, which has no binders to respect.
module Language.MLTT.Interner where

import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import qualified Language.MLTT.Syntax.Abs as Raw

-- | The identifier of a top-level constant.
--
-- 'Integer' rather than 'Int' because that is what BNFC gives the @Const@ node.
type ConstId = Integer

-- | Replace every constant by the name it was interned under, for printing.
--
-- A constant is never bound and never shadowed, so this pass has no binders to
-- account for.
nameConsts :: Map ConstId Raw.VarIdent -> Raw.Term -> Raw.Term
nameConsts names = go
  where
    go = \case
      Raw.Const loc i          -> Raw.Var loc (Map.findWithDefault (unknown i) i names)
      Raw.Pi loc pat ty body   -> Raw.Pi loc pat (go ty) (under body)
      Raw.Sigma loc pat ty body -> Raw.Sigma loc pat (go ty) (under body)
      Raw.Lam loc pat body     -> Raw.Lam loc pat (under body)
      Raw.Let loc pat val body -> Raw.Let loc pat (go val) (under body)
      Raw.Arrow loc t1 t2      -> Raw.Arrow loc (go t1) (go t2)
      Raw.Product loc t1 t2    -> Raw.Product loc (go t1) (go t2)
      Raw.App loc t1 t2        -> Raw.App loc (go t1) (go t2)
      Raw.First loc t          -> Raw.First loc (go t)
      Raw.Second loc t         -> Raw.Second loc (go t)
      Raw.IdType loc tyA x y   -> Raw.IdType loc (go tyA) (go x) (go y)
      Raw.Refl loc x           -> Raw.Refl loc (go x)
      Raw.J loc motive base p  -> Raw.J loc (go motive) (go base) (go p)
      Raw.Pair loc l r         -> Raw.Pair loc (go l) (go r)
      Raw.Ann loc t ty         -> Raw.Ann loc (go t) (go ty)
      leaf                     -> leaf

    under (Raw.AScopedTerm loc body) = Raw.AScopedTerm loc (go body)
    unknown i = Raw.VarIdent ("#const" <> show i)
