module Main where

import LambdaPi.Simple.Interpret
import Language.LambdaPi.Foil
import qualified Language.LambdaPi.FreeFoil as FreeFoil

main :: IO ()
-- main = foilMain
-- main = defaultMain
main = FreeFoil.main
