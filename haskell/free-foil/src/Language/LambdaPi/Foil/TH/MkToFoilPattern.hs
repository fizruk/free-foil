{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.LambdaPi.Foil.TH.MkToFoilPattern (mkToFoilPattern) where

import Language.Haskell.TH

import qualified Language.LambdaPi.Foil as Foil
import Language.Haskell.TH.Syntax (leftName, rightName)
import qualified Data.Either


mkToFoilPattern :: Name -> Name -> Name -> Name -> Q [Dec]
mkToFoilPattern _ nameT _ patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT

  newBinderSeqCons <- newBinderSeqCon n l
  let toFoilPatternClauses = map toFoilPatternClause patternCons

  return
    [ TySynD foilPatternArg [PlainTV n (), PlainTV l ()] (foilPatternArgCon n l)
    , DataD [] newBinderSeq [PlainTV n (), PlainTV l ()] Nothing [newBinderSeqCons] []
    , SigD toFoilPattern (toFoilPatternSigType n l)
    , FunD toFoilPattern toFoilPatternClauses
    ]
  where
    toFoilPattern = mkName ("toFoil" ++ nameBase patternT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)
    foilPatternArg = mkName ("Foil" ++ nameBase patternT ++ "Arg")
    newBinderSeq = mkName "NewBinderSeq"
    aNewBinderSeq = mkName "ANewBinderSeq"

    foilPatternArgCon :: Name -> Name -> Type
    foilPatternArgCon n l =
      AppT (AppT (ConT $ mkName "Either") nameBinder) foilPattern
      where
        nameBinder = AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l)
        foilPattern = AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l)

    newBinderSeqCon :: Name -> Name -> Q Con
    newBinderSeqCon n l = do
      firstName <- newName "first"
      nextName <- newName "next"
      lastName <- newName "last"
      tn <- newName "tn"
      ti <- newName "ti"
      tj <- newName "tj"
      tk <- newName "tk"
      return (RecC aNewBinderSeq [(firstName, noBang, firstType tn),
                            (nextName, noBang, nextType ti tj tk),
                            (lastName, noBang, lastType ti tj)])
        where
          noBang = Bang NoSourceUnpackedness NoSourceStrictness

          firstType :: Name -> Type
          firstType tn = ForallT [PlainTV tn SpecifiedSpec] []
                          (foldl AppT (ConT foilPatternArg) [VarT n, VarT tn])
          nextType ti tj tk = ForallT (map (`PlainTV` SpecifiedSpec) [ti, tj, tk]) []
                                (AppT (AppT ArrowT
                                  (foldl AppT (ConT foilPatternArg) [VarT ti, VarT tj]))
                                  (foldl AppT (ConT foilPatternArg) [VarT tj, VarT tk]))
          lastType ti tj = ForallT (map (`PlainTV` SpecifiedSpec) [ti, tj]) []
                                (AppT (AppT ArrowT
                                  (foldl AppT (ConT foilPatternArg) [VarT ti, VarT tj]))
                                  (foldl AppT (ConT foilPatternArg) [VarT tj, VarT l]))

    toFoilPatternSigType :: Name -> Name -> Type
    toFoilPatternSigType n l =
      ForallT [PlainTV n SpecifiedSpec, PlainTV l SpecifiedSpec] []
      (AppT (AppT ArrowT
        (foldl AppT (ConT newBinderSeq) [VarT n, VarT l]))
        (AppT (AppT ArrowT (ConT patternT))
        (AppT (AppT (ConT ''Data.Either.Either) (foldl AppT (ConT foilPatternT) [VarT n, VarT n])) 
                                                (foldl AppT (ConT foilPatternT) [VarT n, VarT l]))))

    toFoilPatternClause :: Con -> Clause
    toFoilPatternClause (NormalC conName params) =
      Clause pats body []
      where
        firstName = mkName "first"
        nextName = mkName "next"
        lastName = mkName "last"
        conPats = toPats 0 conTypes
        conTypes = map snd params
        pats = [ConP aNewBinderSeq [] [VarP firstName, VarP nextName, VarP lastName],
          ConP conName [] conPats]

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = WildP:toPats n types
          | tyName == patternT = WildP:toPats n types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        isScopeChanged :: [Type] -> Bool
        isScopeChanged _types =
          any filterTypes _types
          where
            filterTypes :: Type -> Bool
            filterTypes (ConT tyName)
              | tyName == nameT = True
              | tyName == patternT = True
              | otherwise = False

        conBody :: [Exp] -> Body
        conBody args
          | isScopeChanged conTypes = NormalB (AppE (ConE 'Data.Either.Right) (foldl AppE (ConE (mkName ("Foil" ++ nameBase conName))) args))
          | otherwise = NormalB (AppE (ConE 'Data.Either.Left) (foldl AppE (ConE (mkName ("Foil" ++ nameBase conName))) args))

        initCase = VarE firstName

        body
          | null conTypes = conBody []
          | otherwise =
            let _typeName = case head conTypes of (ConT _name) -> _name
                _pat = head conPats
                restTypes = tail conTypes
                restPats = tail conPats
            in 
              if _typeName == nameT || _typeName == patternT
                then
                  let
                    newFPAName = mkName ("case" ++ show (length conTypes))
                    newPat
                      | _typeName == nameT = ConP leftName [] [VarP newFPAName]
                      | otherwise = ConP rightName [] [VarP newFPAName]

                  in NormalB (CaseE (VarE firstName) [Match newPat 
                    (toFoilPatternBody initCase [VarE newFPAName] (zip restTypes restPats)) []])
                else
                  case _pat of
                    VarP patName -> toFoilPatternBody initCase [VarE patName] (zip restTypes restPats)

        toFoilPatternBody :: Exp -> [Exp] -> [(Type, Pat)] -> Body
        toFoilPatternBody _ args [] = conBody args
        toFoilPatternBody prevCaseExp args [(ConT _typeName,_pat)] =
          if _typeName == nameT || _typeName == patternT
            then
              let
                newCaseExp = AppE (VarE lastName) prevCaseExp
                newFPAName = mkName "case1"
                newPat
                      | _typeName == nameT = ConP leftName [] [VarP newFPAName]
                      | otherwise = ConP rightName [] [VarP newFPAName]
              in NormalB (CaseE newCaseExp [Match newPat (conBody (args ++ [VarE newFPAName])) []])
            else
              case _pat of
                VarP patName -> conBody (args ++ [VarE patName])
        toFoilPatternBody prevCaseExp args ((ConT _typeName,_pat):rest) =
           if _typeName == nameT || _typeName == patternT
            then
              let
                newCaseExp = AppE (VarE nextName) prevCaseExp
                newFPAName = mkName ("case" ++ show (length rest))
                newPat
                  | _typeName == nameT = ConP leftName [] [VarP newFPAName]
                  | otherwise = ConP rightName [] [VarP newFPAName]
                in NormalB (CaseE newCaseExp [Match newPat (toFoilPatternBody (ParensE newCaseExp) (args ++ [VarE newFPAName]) rest) []])
            else
              case _pat of
                VarP patName ->
                  toFoilPatternBody prevCaseExp (args ++ [VarE patName]) rest

