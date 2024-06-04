-- {-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fno-warn-unused-binds  #-}
module Language.LambdaPi.Impl.FoilTH where


import           Control.Monad.Foil.TH
import qualified Language.LambdaPi.Syntax.Abs as Raw

-- * Generated code

-- ** Scope-safe AST
mkFoilData ''Raw.Term ''Raw.VarIdent ''Raw.ScopedTerm ''Raw.Pattern

-- ** Conversion from raw to scope-safe AST
mkToFoil ''Raw.Term ''Raw.VarIdent ''Raw.ScopedTerm ''Raw.Pattern

-- mkFromFoil ''Raw.Term ''Raw.VarIdent ''Raw.ScopedTerm ''Raw.Pattern
-- mkInstancesFoil ''Raw.Term ''Raw.VarIdent ''Raw.ScopedTerm ''Raw.Pattern

-- substitute :: FoilTerm o -> FoilTerm i -> FoilTerm o
-- substitute substTerm = \case
--   FoilVar name -> substTerm
--   FoilApp term1 term2 -> substTerm
--   FoilLam (FoilPatternVar pat) (FoilAScopedTerm term) -> substituteHelper substTerm (nameOf pat) term
--     where
--       substituteHelper :: FoilTerm o -> Name i -> FoilTerm i -> FoilTerm o
--       substituteHelper substTerm substName = \case
--         FoilVar name
--           | ppName name == ppName substName -> substTerm
--           | otherwise -> FoilVar (UnsafeName (ppName name))
--         FoilApp term1 term2 -> FoilApp (substituteHelper substTerm substName term1) (substituteHelper substTerm substName term2)
--         FoilLam (FoilPatternVar pat) (FoilAScopedTerm term)
--           | ppName (nameOf pat) == ppName substName -> substituteHelper substTerm (UnsafeName (ppName substName)) term
--           | otherwise -> FoilLam (FoilPatternVar newPat) (FoilAScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
--             where
--               newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))

-- two :: Term
-- two = Lam (PatternVar "s") (AScopedTerm (Lam (PatternVar "z") (AScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

-- -- twoFoil :: FoilTerm n
-- -- twoFoil = FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "s"))) (FoilAScopedTerm (FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) (FoilAScopedTerm (FoilApp (FoilVar (UnsafeName "s")) (FoilApp (FoilVar (UnsafeName "s")) (FoilVar (UnsafeName "z")))))))

-- -- foilFour :: FoilTerm n
-- -- foilFour = FoilVar (UnsafeName "zz" :: Name n)

-- -- func :: VarIdent -> Name n
-- -- func (VarIdent s) = UnsafeName s :: Name n

-- -- substed = FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) (FoilAScopedTerm (FoilApp (FoilVar (UnsafeName "zz")) (FoilApp (FoilVar (UnsafeName "zz")) (FoilVar (UnsafeName "z")))))

-- -- -- Control.Monad.Foil.LambdaPiExample.toFoilTerm Control.Monad.Foil.LambdaPiExample.func Control.Monad.Foil.emptyScope Control.Monad.Foil.LambdaPiExample.two
