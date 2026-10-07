{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}

-- | How a type is declared, read back with 'reify', for the tests of the pattern
-- types that 'Control.Monad.Free.Foil.TH.MkFreeFoil.mkFreeFoil' generates.
module Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Declaration (declarationOf) where

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (lift)

-- | A splice for the declaration of a type: @"newtype"@ or @"data"@, and the
-- source strictness of every field of every constructor, as
-- @"{-# UNPACK #-} !"@, @"!"@ or @""@.
declarationOf :: Name -> Q Exp
declarationOf name = reify name >>= \case
  TyConI (NewtypeD _ _ _ _ con _) -> lift ("newtype", fieldsOf con)
  TyConI (DataD _ _ _ _ cons _)   -> lift ("data", concatMap fieldsOf cons)
  _ -> fail ("declarationOf: " <> show name <> " is not a data type or a newtype")
  where
    fieldsOf :: Con -> [(String, [String])]
    fieldsOf = \case
      ForallC _ _ con        -> fieldsOf con
      NormalC con bts        -> [(nameBase con, map (bangOf . fst) bts)]
      RecC con vbts          -> [(nameBase con, [ bangOf b | (_, b, _) <- vbts ])]
      InfixC l con r         -> [(nameBase con, map (bangOf . fst) [l, r])]
      GadtC cons bts _       -> [ (nameBase con, map (bangOf . fst) bts) | con <- cons ]
      RecGadtC cons vbts _   -> [ (nameBase con, [ bangOf b | (_, b, _) <- vbts ]) | con <- cons ]

    bangOf (Bang unpackedness strictness) =
      unwords (filter (not . null) [unpackednessOf unpackedness, strictnessOf strictness])
    unpackednessOf = \case
      SourceUnpack   -> "{-# UNPACK #-}"
      SourceNoUnpack -> "{-# NOUNPACK #-}"
      NoSourceUnpackedness -> ""
    strictnessOf = \case
      SourceStrict -> "!"
      SourceLazy   -> "~"
      NoSourceStrictness -> ""
