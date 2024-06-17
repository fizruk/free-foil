{-# LANGUAGE PatternSynonyms                 #-}
{-# LANGUAGE ViewPatterns                 #-}
{-# LANGUAGE LambdaCase            #-}
module Control.Monad.Foil.TH.Util where

import Language.Haskell.TH

peelConT :: Type -> Maybe (Name, [Type])
peelConT (ConT name) = Just (name, [])
peelConT (AppT f x) =
  case peelConT f of
    Just (g, xs) -> Just (g, xs ++ [x])
    Nothing -> Nothing
peelConT _ = Nothing

unpeelConT :: Name -> [Type] -> Type
unpeelConT = foldl AppT . ConT

pattern PeelConT :: Name -> [Type] -> Type
pattern PeelConT name types <- (peelConT -> Just (name, types)) where
  PeelConT name types = unpeelConT name types

tvarName :: TyVarBndr a -> Name
tvarName = \case
  PlainTV name _ -> name
  KindedTV name _ _ -> name
