{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Control.Monad.Foil.Relative where

import           Control.Monad.Foil
import           Data.Kind          (Type)

-- | Relative monads, restricted to types indexed by scopes in kind 'S'.
class RelMonad (f :: S -> Type) (m :: S -> Type) where
  -- | Relative version of 'return'.
  rreturn :: f a -> m a

  -- | Relative version of '>>='.
  --
  -- Note the two special additions to the usual definition of a relative binding operation:
  --
  -- 1. @'Scope' b@ is added since is corresponds to the runtime counterpart of the type parameter @b@.
  -- 2. @t'Distinct' b@ constraint helps to ensure we only work with scopes that are distinct.
  --
  -- Technically, it is also possible add similar components for @a@ parameter.
  -- Also, we could probably treat types in 'S' as singletons and extract distinct scopes that way,
  -- preserving the more general type signature for 'rbind'.
  rbind :: Distinct b => Scope b -> m a -> (f a -> m b) -> m b

-- | Relative version of 'liftM' (an 'fmap' restricted to 'Monad').
liftRM :: (RelMonad f m, Distinct b) => Scope b -> (f a -> f b) -> m a -> m b
liftRM scope f m = rbind scope m (rreturn . f)
