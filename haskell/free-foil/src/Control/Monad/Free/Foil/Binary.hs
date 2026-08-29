{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | 'Binary' instances for the scope-safe syntax: the wire view of a term
-- is the term itself, raw ids and all.
--
-- The instances are deliberately orphans in a module of their own, so that
-- they are opt-in: importing this module is what brings them into scope,
-- and nothing else in the library does. (The dependency this costs is
-- @binary@, a GHC boot library.)
--
-- Note that decoding /mints/ scope evidence: a 'Foil.Name' comes back at
-- whatever scope index the context asks for, and the existential scope
-- under a binder is chosen arbitrarily. Thus the instances are a trust
-- boundary, in the sense of 'Control.Monad.Foil.Blocks.checkExtScope'. The
-- bytes are meaningful only under the discipline of the layer that wrote
-- them, and that layer is expected to validate what it can on the way in.
-- In particular, it should resolve the references it made
-- world-independent, and check that the names it left verbatim lie where its
-- allocation policy says. "Control.Monad.Free.Foil.Artifact" supplies those
-- checks.
module Control.Monad.Free.Foil.Binary () where

import           Data.Binary                 (Binary (..))
import           Data.Binary.Get             (Get, getWord8)
import           Data.Binary.Put             (putWord8)

import           Control.Monad.Foil.Internal
import           Control.Monad.Free.Foil     (AST (..), ScopedAST (..))

-- | The raw id and nothing else. See the module documentation for what
-- decoding trusts.
instance Binary (Name n) where
  put (UnsafeName raw) = put raw
  get = UnsafeName <$> get

-- | See the 'Binary' instance of 'Name'.
instance Binary (NameBinder n l) where
  put (UnsafeNameBinder name) = put name
  get = UnsafeNameBinder <$> get

-- | The two bounds. A range carries no scope index, so nothing is minted:
-- this instance is layout metadata for the serialising layer.
instance Binary NameRange where
  put (NameRange lo hi) = put lo <> put hi
  get = NameRange <$> get <*> get

-- | The binder and the body, one after the other. Decoding mints the scope
-- under the binder. See the module documentation.
instance (forall x y. Binary (binder x y), forall l. Binary (AST binder sig l))
    => Binary (ScopedAST binder sig n) where
  put (ScopedAST binder body) = put binder <> put body
  get = do
    binder <- get :: Get (binder n n)
    body <- get
    pure (ScopedAST binder body)

-- | A tag byte, then the name or the node.
instance ( forall x y. Binary (binder x y)
         , forall scope term. (Binary scope, Binary term) => Binary (sig scope term)
         ) => Binary (AST binder sig n) where
  put (Var x)     = putWord8 0 <> put x
  put (Node node) = putWord8 1 <> put node
  get = getWord8 >>= \case
    0   -> Var <$> get
    1   -> Node <$> get
    tag -> fail ("unknown AST tag " <> show tag)
