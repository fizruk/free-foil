{-# LANGUAGE TemplateHaskell #-}
-- | A generator for signature bifunctors of a given size.
--
-- The cost of the generic 'Data.ZipMatchK.ZipMatchK' instance is expected to
-- grow with the number of constructors — a constructor is represented as a
-- chain of @L1@\/@R1@ wrappers as long as its index — so the benchmark needs
-- signatures of several sizes, and hand-writing them would defeat the purpose.
module Signature (mkSig) where

import           Language.Haskell.TH

-- | @mkSig \"Sig\" n@ declares a signature bifunctor @Sig@ with @n@
-- constructors: @n-1@ application-like nodes (two terms) and one λ-like node
-- (one scoped term), with 'Bifunctor', 'Bifoldable' and 'Bitraversable'
-- instances. It also declares two builders,
--
-- > appSig :: Int -> term -> term -> Sig scope term   -- the i-th application node
-- > lamSig :: scope -> Sig scope term
--
-- named after the type (@appSig@ and @lamSig@ for @Sig@), so that one term
-- builder can serve every signature.
--
-- The 'Data.Bifunctor.Bifunctor' and 'Data.ZipMatchK.ZipMatchK' instances are
-- left to the caller: they need a splice of their own, as Template Haskell
-- cannot reify a type declared in the same declaration group.
mkSig :: String -> Int -> Q [Dec]
mkSig name n = do
  scope <- newName "scope"
  term <- newName "term"
  let typeName = mkName name
      appName i = mkName (name ++ "App" ++ show i)
      lamName = mkName (name ++ "Lam")
      appCon i = NormalC (appName i)
        [ (noBang, VarT term), (noBang, VarT term) ]
      lamCon = NormalC lamName [ (noBang, VarT scope) ]
      noBang = Bang NoSourceUnpackedness NoSourceStrictness
      cons = map appCon [0 .. n - 2] ++ [lamCon]
      dataDec = DataD [] typeName [PlainTV scope BndrReq, PlainTV term BndrReq] Nothing cons
        [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]]

  -- appSig i = the i-th application constructor, cycling.
  i <- newName "i"
  let sigType t = ForallT [PlainTV scope SpecifiedSpec, PlainTV term SpecifiedSpec] [] t
      appType = sigType (arrows [ConT ''Int, VarT term, VarT term] result)
      lamType = sigType (arrows [VarT scope] result)
      result = AppT (AppT (ConT typeName) (VarT scope)) (VarT term)
      arrows args res = foldr (\a b -> AppT (AppT ArrowT a) b) res args
      appFn = mkName ("app" ++ name)
      appDec = FunD appFn
        [ Clause [VarP i]
            (NormalB (CaseE (InfixE (Just (VarE i)) (VarE 'mod) (Just (LitE (IntegerL (toInteger (n - 1))))))
              ([ Match (LitP (IntegerL (toInteger k))) (NormalB (ConE (appName k))) []
               | k <- [0 .. n - 3] ]
               ++ [ Match WildP (NormalB (ConE (appName (n - 2)))) [] ])))
            [] ]
      lamFn = mkName ("lam" ++ name)
      lamDec = FunD lamFn [ Clause [] (NormalB (ConE lamName)) [] ]

  return [dataDec, SigD appFn appType, appDec, SigD lamFn lamType, lamDec]
