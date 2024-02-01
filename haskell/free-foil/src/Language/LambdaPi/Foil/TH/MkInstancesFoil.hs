{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.LambdaPi.Foil.TH.MkInstancesFoil (mkInstancesFoil) where

import Language.Haskell.TH

import qualified Language.LambdaPi.Foil as Foil
import Data.Maybe (fromJust)
import Data.Coerce (coerce)

-- Foil

-- data FoilTerm n where
--   FoilVar :: Foil.Name n -> FoilTerm n
--   FoilApp :: FoilTerm n -> FoilTerm n -> FoilTerm n
--   FoilLam :: FoilPattern n l -> FoilTerm l -> FoilTerm n

-- data FoilPattern n l where
--   FoilPatternVar :: Foil.NameBinder n l -> FoilPattern n l

-- data FoilScopedTerm n where
--   FoilScopedTerm :: FoilTerm n -> FoilScopedTerm n

mkInstancesFoil :: Name -> Name -> Name -> Name -> Q [Dec]
mkInstancesFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT
  let foilPatternCons = map (toPatternCon n l) patternCons
  let foilScopeCons = map (toScopeCon n) scopeCons
  let foilTermCons = map (toTermCon n l) termCons

  return [
      InstanceD Nothing [] (AppT (ConT (mkName "Sinkable")) (ConT foilScopeT))
      [FunD (mkName "sinkabilityProof") (map clauseScopedTerm foilScopeCons)]
    -- , InstanceD Nothing [] (AppT (ConT (mkName "Sinkable")) (AppT (ConT foilPatternT) (VarT n)))
    --   [FunD (mkName "sinkabilityProof") (map clausePattern foilPatternCons)]
    , InstanceD Nothing [] (AppT (ConT (mkName "Sinkable")) (ConT foilTermT))
      [FunD (mkName "sinkabilityProof") (map clauseTerm foilTermCons)]
    , FunD extendRenamingPatternT [Clause [WildP, VarP (mkName "pattern"), VarP (mkName "cont")] extendRenamingPatternBody []]
    ]

  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)
    extendRenamingPatternT = mkName ("extendRenaming" ++ nameBase patternT)

    clauseScopedTerm :: Con -> Clause
    clauseScopedTerm (NormalC conName params) =
      let conPats = toPats 0 conTypes
          conTypes = map snd params
      in
        Clause [VarP (mkName "f"), ConP conName [] conPats] (matchBody conTypes conName conPats) []
        where
          toPats :: Int -> [Type] -> [Pat]
          toPats _ [] = []
          toPats n ((AppT (ConT tyName) _):types)
            | tyName == ''Foil.Name = VarP (mkName ("varName" ++ show n)):toPats (n+1) types
            | tyName == foilPatternT = VarP (mkName "pat"):toPats (n+1) types
            | tyName == foilScopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
            | tyName == foilTermT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
            | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

          matchBody :: [Type] -> Name -> [Pat] -> Body
          matchBody matchTypes name _conPats = NormalB (foldl AppE (ConE name) (zipWith toExpr matchTypes _conPats))

          toExpr :: Type -> Pat -> Exp
          toExpr ((AppT (ConT tyName) _)) (VarP patName)
            | tyName == ''Foil.Name = AppE (VarE (mkName "f")) (VarE patName)
            | tyName == foilTermT = AppE (AppE (VarE (mkName "sinkabilityProof")) (VarE (mkName "f"))) (VarE patName)
            | otherwise = VarE patName


    clausePattern :: Con -> Clause
    clausePattern (NormalC conName params) =
      let
        conPats = toPats 0 conTypes
        conTypes = map snd params
      in Clause [VarP (mkName "f"), ConP conName [] conPats] (matchBody conTypes conName conPats) []

      where

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT simple):types) = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        toPats n ((AppT (AppT (ConT var) (VarT _)) (VarT _)):types)
          | var == ''Foil.NameBinder = ConP 'Foil.UnsafeNameBinder [] [VarP (mkName ("var" ++ show n))]:toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Name -> [Pat] -> Body
        matchBody matchTypes name _conPats = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes _conPats))

        toExpr :: Type -> Pat -> Exp
        toExpr ((AppT (AppT (ConT var) (VarT _)) (VarT _))) (ConP unsafeBinder [] [VarP singleVar])
          | var == ''Foil.NameBinder = AppE (ConE 'Foil.UnsafeNameBinder) (AppE (VarE (mkName "f")) (VarE singleVar))
        toExpr _ (VarP patName) = VarE patName

    clauseTerm :: Con -> Clause
    -- clauseTerm (NormalC conNameTerm paramsTerm) =
    clauseTerm (GadtC [conNameTerm] paramsTerm _) =
      Clause [VarP (mkName "f"), ConP conNameTerm [] conPats]
        (matchBody conTypes conNameTerm conPats)
      []

      where
        conPats = toPats 0 conTypes
        conTypes = map snd paramsTerm

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n (AppT (AppT (ConT fPT) (VarT _)) (VarT _):types)
          | fPT == foilPatternT = VarP (mkName $ "pattern" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        toPats n (AppT (ConT _conName) (VarT _):types)
          | _conName == ''Foil.Name = VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | _conName == foilTermT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | _conName == foilScopeT = VarP (mkName $ "body" ++ show n):toPats (n+1) types -- Плохо что используется foilSopeT
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        toPats n (_:types) = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Name -> [Pat] -> Body
        matchBody matchTypes name _conPats = NormalB constr

          where
            constr = if checkPatScope matchTypes False
              then sinkProofPatScope
              else foldl AppE (ConE name) (zipWith toExpr matchTypes _conPats)


            checkPatScope :: [Type] -> Bool -> Bool
            checkPatScope [] _ = False
            checkPatScope (AppT (AppT (ConT fPT) (VarT _)) (VarT _):rest) patFound
              | fPT == foilPatternT = checkPatScope rest True
              | otherwise = checkPatScope rest patFound
            checkPatScope (AppT (ConT _conName) (VarT _):rest) patFound
              | _conName == foilScopeT && patFound = True
              | otherwise = checkPatScope rest patFound
            checkPatScope (_:rest) patFound = checkPatScope rest patFound

            toExpr :: Type -> Pat -> Exp
            toExpr ((AppT (ConT _conName) (VarT _))) (VarP varName)
              | _conName == ''Foil.Name = AppE (VarE (mkName "f")) (VarE varName)
              | _conName == foilTermT = AppE (AppE (VarE (mkName "sinkabilityProof")) (VarE (mkName "f"))) (VarE varName)
              | otherwise = VarE varName
            toExpr _ (VarP patName) = VarE patName

            sinkProofPatScope =
              AppE (AppE (AppE (VarE extendRenamingPatternT) (VarE (mkName "f"))) (VarE (fromJust (findPatternName matchTypes _conPats))))
                (LamE [VarP (mkName "f'"), VarP (mkName "pattern'")]
                  (foldl AppE (ConE name) (zipWith toExprSink matchTypes _conPats)))
                  where
                    findPatternName :: [Type] -> [Pat] -> Maybe Name
                    findPatternName [] [] = Nothing
                    findPatternName  (AppT (AppT (ConT fPT) (VarT _)) (VarT _):_) ((VarP varName):_)
                      | fPT == foilPatternT = Just varName
                    findPatternName (_:restT) (_:restP) = findPatternName restT restP

                    toExprSink :: Type -> Pat -> Exp
                    toExprSink (AppT (AppT (ConT _conName) (VarT _)) (VarT _)) (VarP varName)
                      | _conName == foilPatternT = VarE (mkName "pattern'")
                      | otherwise = VarE varName
                    toExprSink ((AppT (ConT _conName) (VarT _))) (VarP varName)
                      | _conName == foilScopeT = AppE (AppE (VarE (mkName "sinkabilityProof")) (VarE (mkName "f'"))) (VarE varName)
                      | _conName == foilTermT = AppE (AppE (VarE (mkName "sinkabilityProof")) (VarE (mkName "f"))) (VarE varName)
                      | _conName == ''Foil.Name = AppE (VarE (mkName "f")) (VarE varName)
                      | otherwise = VarE varName

    extendRenamingPatternBody = NormalB (AppE (AppE (VarE (mkName "cont")) (VarE (mkName "unsafeCoerce"))) (AppE (VarE (mkName "unsafeCoerce")) (VarE (mkName "pattern")) ))

    toPatternCon :: Name -> Name -> Con -> Con
    toPatternCon n l (NormalC conName  params) =
      NormalC foilConName (map toPatternParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toPatternParam (_bang, ConT tyName)
          | tyName == nameT = (_bang, AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l))
        toPatternParam _bangType = _bangType

    toScopeCon :: Name -> Con -> Con
    toScopeCon n (NormalC conName params) =
      NormalC foilConName (map toScopeParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toScopeParam (_bang, ConT tyName)
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toScopeParam _bangType = _bangType

    toTermCon :: Name -> Name -> Con -> Con
    toTermCon n l (NormalC conName params) =
      GadtC [foilConName] (map toTermParam params) (AppT (ConT foilTermT) (VarT n))
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (_bang, ConT tyName)
          | tyName == patternT = (_bang, AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l))
          | tyName == nameT = (_bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (_bang, AppT (ConT foilScopeT) (VarT l))
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toTermParam _bangType = _bangType