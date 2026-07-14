{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Annotating every node of a free foil term.
--
-- A node can be annotated with anything: a source position, a type, a memoised
-- normal form. 'AnnSig' turns a signature into an annotated one, and
-- 'AnnAST' is the annotated syntax it generates.
--
-- The annotation is a /functor of the term/, and that is what lets it depend on
-- the node's scope. In @'AST' binder sig n@ the signature's term parameter /is/
-- the AST at the node's own scope, so an annotation built from it holds terms in
-- that scope — which is what a type annotation in a dependent language needs.
-- An annotation that ignores the term (a source position, say) is @'Const' a@.
--
-- Whether two annotations must agree for their nodes to match is a property of
-- @ann@, not of 'AnnSig'. Two examples, and they are the two you will want:
--
-- An annotation that ignores the term (a source position) and /is/ compared:
--
-- > instance Eq a => ZipMatchK (Const (a :: Type)) where
-- >   zipMatchWithK _ (Const l) (Const r)
-- >     | l == r    = Just (Const l)
-- >     | otherwise = Nothing
--
-- An annotation that holds terms (a type, with a memoised normal form) and is
-- /ignored/, so that two terms differing only in their types are α-equivalent:
--
-- > data TypeInfo term = TypeInfo { infoType :: term, infoWHNF :: Maybe term }
-- >
-- > instance ZipMatchK TypeInfo where
-- >   zipMatchWithK (f :^: M0) (TypeInfo t1 w1) (TypeInfo t2 w2) =
-- >     TypeInfo <$> f t1 t2 <*> pure (do { a <- w1; b <- w2; f a b })
--
-- __Do not reach for the generic instance here.__ It compares the annotation's
-- /shape/, so a node carrying a memoised normal form would fail to match the same
-- node without one. An annotation-blind instance is one that always succeeds,
-- pairing the terms it can and dropping the rest — as above. (Nor is
-- 'zipMatchViaChooseLeft' available: an annotation holding terms must /construct/ a
-- value at the result index, and cannot simply pick a side.)
--
-- __Note the asymmetry__ in the instances below: 'Bifunctor' and 'Bitraversable'
-- traverse the annotation, but 'Bifoldable' does /not/. This is deliberate — see
-- 'AnnSig'.
module Control.Monad.Free.Foil.Annotated (
  AnnSig(..),
  AnnAST,
  AnnScopedAST,
  pattern AnnNode,
  annotationOf,
  freeVarsOfAnnotated,
) where

import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Kind             (Type)
import           Data.Maybe            (mapMaybe)
import           Data.ZipMatchK
import           Generics.Kind         (GenericK (..), Field, Var0, Var1, (:$:),
                                        Atom ((:@:)), (:*:))
import qualified GHC.Generics          as GHC

import qualified Control.Monad.Foil    as Foil
import           Control.Monad.Free.Foil

-- | A signature, with every node annotated by an @ann@ built from the node's term.
--
-- The annotation is applied to the /term/ parameter, so in an
-- @'AST' binder ('AnnSig' ann sig) n@ it holds terms in the node's own scope.
--
-- 'Bifoldable' deliberately __skips the annotation__. That is what makes
-- α-equivalence annotation-blind: 'Control.Monad.Free.Foil.alphaEquiv' consumes a
-- zipped node with 'bifoldMap', so a type annotation is never compared, and two
-- terms that differ only in their annotations are α-equivalent. The price is that
-- 'Control.Monad.Free.Foil.freeVarsOf', which is also 'Bifoldable', does not see
-- variables occurring inside annotations. Use 'freeVarsOfAnnotated' when those
-- matter.
data AnnSig (ann :: Type -> Type) (sig :: Type -> Type -> Type) scope term
  = AnnSig (ann term) (sig scope term)
  deriving (GHC.Generic)

deriving instance (Functor ann, Functor (sig scope))
  => Functor (AnnSig ann sig scope)
deriving instance (Foldable ann, Foldable (sig scope))
  => Foldable (AnnSig ann sig scope)
deriving instance (Traversable ann, Traversable (sig scope))
  => Traversable (AnnSig ann sig scope)

instance (Functor ann, Bifunctor sig) => Bifunctor (AnnSig ann sig) where
  bimap f g (AnnSig ann sig) = AnnSig (fmap g ann) (bimap f g sig)

-- | __The annotation is not folded.__ See 'AnnSig'.
instance Bifoldable sig => Bifoldable (AnnSig ann sig) where
  bifoldMap f g (AnnSig _ann sig) = bifoldMap f g sig

instance (Traversable ann, Bitraversable sig) => Bitraversable (AnnSig ann sig) where
  bitraverse f g (AnnSig ann sig) = AnnSig <$> traverse g ann <*> bitraverse f g sig

instance GenericK (AnnSig ann sig) where
  type RepK (AnnSig ann sig) =
    Field (ann :$: Var1) :*: Field ((sig :$: Var0) :@: Var1)

instance (ZipMatchK ann, ZipMatchK sig)
  => ZipMatchK (AnnSig (ann :: Type -> Type) (sig :: Type -> Type -> Type))

-- | An annotated scope-safe term.
type AnnAST binder ann sig = AST binder (AnnSig ann sig)

-- | An annotated scope-safe term under a binder.
type AnnScopedAST binder ann sig = ScopedAST binder (AnnSig ann sig)

-- | An annotated node.
pattern AnnNode
  :: ann (AnnAST binder ann sig n)
  -> sig (AnnScopedAST binder ann sig n) (AnnAST binder ann sig n)
  -> AnnAST binder ann sig n
pattern AnnNode ann sig = Node (AnnSig ann sig)

{-# COMPLETE Var, AnnNode #-}

-- | The annotation of a term, unless it is a variable (which is not a node, so it
-- carries none).
annotationOf :: AnnAST binder ann sig n -> Maybe (ann (AnnAST binder ann sig n))
annotationOf = \case
  Var _         -> Nothing
  AnnNode ann _ -> Just ann

-- | The free variables of an annotated term, __including__ those occurring inside
-- annotations.
--
-- 'Control.Monad.Free.Foil.freeVarsOf' misses the latter, since 'Bifoldable' skips
-- the annotation (see 'AnnSig').
freeVarsOfAnnotated
  :: (Foil.Distinct n, Foil.CoSinkable binder, Bifoldable sig, Foldable ann)
  => AnnAST binder ann sig n -> [Foil.Name n]
freeVarsOfAnnotated = \case
  Var name -> [name]
  AnnNode ann sig ->
    foldMap freeVarsOfAnnotated ann
      <> bifoldMap freeVarsOfAnnotatedScoped freeVarsOfAnnotated sig

-- | The free variables of an annotated scoped term, including those inside
-- annotations.
freeVarsOfAnnotatedScoped
  :: (Foil.Distinct n, Foil.CoSinkable binder, Bifoldable sig, Foldable ann)
  => AnnScopedAST binder ann sig n -> [Foil.Name n]
freeVarsOfAnnotatedScoped (ScopedAST binder body) =
  case Foil.assertDistinct binder of
    Foil.Distinct ->
      mapMaybe (Foil.unsinkNamePattern binder) (freeVarsOfAnnotated body)
