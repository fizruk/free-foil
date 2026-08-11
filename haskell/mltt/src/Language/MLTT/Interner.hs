{-# LANGUAGE LambdaCase #-}
-- | Interned top-level constants, and the two raw-syntax passes they need.
--
-- This module is the difference between the two candidate designs for a global
-- environment. Here a top-level declaration is __not__ a name in a scope: it is
-- an interned identifier carried by a @Const@ node, which has no scope index of
-- its own. A checked declaration is therefore a @Term' a VoidS@ — closed by
-- /type/ rather than by discipline — and the foil index means the local context
-- only.
--
-- The price is that resolution has to happen on the raw syntax, before
-- conversion. Free foil's generated conversions map an identifier to a
-- 'Control.Monad.Foil.Name', and there is no way to ask them to map one to a
-- node instead, so 'internTerm' does that itself and has to know about binders
-- to do it. 'rewriteRaw' is the traversal both passes share.
module Language.MLTT.Interner where

import           Data.List                (foldl')
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Set                 (Set)
import qualified Data.Set                 as Set
import qualified Language.MLTT.Syntax.Abs as Raw

-- | The identifier of a top-level constant.
--
-- 'Integer' rather than 'Int' because that is what BNFC gives the @Const@ node.
type ConstId = Integer

-- | Rewrite a raw term, knowing which identifiers are bound where.
--
-- The function is tried at every node; when it declines, the node is rebuilt
-- from its rewritten children, and the identifiers a binder binds are added to
-- the set on the way under it. Both passes below rewrite only leaves, so
-- nothing here has to consider a rewrite that itself contains identifiers.
rewriteRaw
  :: (Set Raw.VarIdent -> Raw.Term -> Maybe Raw.Term)
  -> Raw.Term
  -> Raw.Term
rewriteRaw f = go Set.empty
  where
    go bound term
      | Just term' <- f bound term = term'
      | otherwise = case term of
          Raw.Pi loc pat ty body ->
            Raw.Pi loc pat (go bound ty) (under bound pat body)
          Raw.Sigma loc pat ty body ->
            Raw.Sigma loc pat (go bound ty) (under bound pat body)
          Raw.Lam loc pat body    -> Raw.Lam loc pat (under bound pat body)
          Raw.Let loc pat val body ->
            Raw.Let loc pat (go bound val) (under bound pat body)
          Raw.Arrow loc t1 t2     -> Raw.Arrow loc (go bound t1) (go bound t2)
          Raw.Product loc t1 t2   -> Raw.Product loc (go bound t1) (go bound t2)
          Raw.App loc t1 t2       -> Raw.App loc (go bound t1) (go bound t2)
          Raw.First loc t         -> Raw.First loc (go bound t)
          Raw.Second loc t        -> Raw.Second loc (go bound t)
          Raw.IdType loc tyA x y  -> Raw.IdType loc (go bound tyA) (go bound x) (go bound y)
          Raw.Refl loc x          -> Raw.Refl loc (go bound x)
          Raw.J loc motive base p -> Raw.J loc (go bound motive) (go bound base) (go bound p)
          Raw.Pair loc l r        -> Raw.Pair loc (go bound l) (go bound r)
          Raw.Ann loc t ty        -> Raw.Ann loc (go bound t) (go bound ty)
          leaf                    -> leaf

    under bound pat (Raw.AScopedTerm loc body) =
      Raw.AScopedTerm loc (go (Set.union (patternIdents pat) bound) body)

-- | The identifiers a pattern binds.
patternIdents :: Raw.Pattern -> Set Raw.VarIdent
patternIdents = \case
  Raw.PatternWildcard _loc -> Set.empty
  Raw.PatternVar _loc x    -> Set.singleton x
  Raw.PatternPair _loc l r -> Set.union (patternIdents l) (patternIdents r)

-- | Replace every identifier that denotes a top-level declaration by that
-- declaration's constant, applied to the module parameters it was closed over.
--
-- Resolving the identifier and putting the parameters back are the same step
-- here, so a declaration of a parametrised module can be named plainly from
-- inside that module. A locally bound identifier of the same spelling is left
-- alone, which is why the traversal has to know about binders.
internTerm :: Map Raw.VarIdent (ConstId, [Raw.VarIdent]) -> Raw.Term -> Raw.Term
internTerm table = rewriteRaw $ \bound -> \case
  Raw.Var loc x
    | not (x `Set.member` bound)
    , Just (i, params) <- Map.lookup x table
    -> Just (foldl' (apply loc) (Raw.Const loc i) params)
  _ -> Nothing
  where
    apply loc f x = Raw.App loc f (Raw.Var loc x)

-- | Replace every constant by the name it was interned under, for printing.
--
-- A constant is never shadowed and never bound, so this pass ignores binders.
nameConsts :: Map ConstId Raw.VarIdent -> Raw.Term -> Raw.Term
nameConsts names = rewriteRaw $ \_bound -> \case
  Raw.Const loc i -> Just (Raw.Var loc (Map.findWithDefault (unknown i) i names))
  _               -> Nothing
  where
    unknown i = Raw.VarIdent ("#const" <> show i)
