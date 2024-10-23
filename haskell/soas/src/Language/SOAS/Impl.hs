{-# OPTIONS_GHC -fno-warn-orphans -ddump-splices #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Language.SOAS.Impl where

import           Control.Monad.Free.Foil.TH.MkFreeFoil
import qualified Language.SOAS.Syntax.Abs    as Raw
import qualified Language.SOAS.Syntax.Lex    as Raw
import qualified Language.SOAS.Syntax.Par    as Raw
import qualified Language.SOAS.Syntax.Print  as Raw
import           System.Exit                     (exitFailure)
-- import Control.Monad.Free.Foil.Generic
-- import Generics.Kind.TH (deriveGenericK)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

mkFreeFoil FreeFoilConfig
  { rawQuantifiedNames =
      [ ''Raw.Subst'
      , ''Raw.MetaVarTyping'
      , ''Raw.OpTyping'
      , ''Raw.Constraint'
      , ''Raw.VarTyping'
      , ''Raw.TermTyping'
      ]
  , freeFoilTermConfigs =
      [ FreeFoilTermConfig
          { rawIdentName = ''Raw.VarIdent
          , rawTermName = ''Raw.Term'
          , rawBindingName = ''Raw.Binders'
          , rawScopeName = ''Raw.ScopedTerm'
          , rawVarConName = 'Raw.Var
          , rawSubTermNames = [ ''Raw.OpArg' ]
          }
      , FreeFoilTermConfig
          { rawIdentName = ''Raw.TypeVarIdent'
          , rawTermName = ''Raw.Type'
          , rawBindingName = ''Raw.TypeBinders'
          , rawScopeName = ''Raw.ScopedType'
          , rawVarConName = 'Raw.TypeVar
          , rawSubTermNames = [ ''Raw.OpArgTyping' ]
          } ]
  , freeFoilNameModifier = id
  , freeFoilScopeNameModifier = ("Scoped" ++ )
  , freeFoilConNameModifier = id
  , signatureNameModifier = (++ "Sig")
  , ignoreNames = []
  }

-- | A SOAS interpreter implemented via the free foil.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case Raw.pTermTyping (Raw.tokens input) of
    Left err -> do
      putStrLn err
      exitFailure
    Right typing -> putStrLn (Raw.printTree typing)
