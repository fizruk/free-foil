-- | Relative monads over scopes, and 'liftRM' for renaming with them.
module Control.Monad.Foil.Relative (
  RelMonad (..),
  liftRM,
) where

import           Control.Monad.Foil
import           Control.Monad.Foil.Internal (RelMonad (..))

-- | Relative version of @liftM@ (an 'fmap' restricted to 'Monad').
--
-- @since 0.0.3
liftRM :: (RelMonad f m, Distinct b) => Scope b -> (f a -> f b) -> m a -> m b
liftRM scope f m = rbind scope m (rreturn . f)
