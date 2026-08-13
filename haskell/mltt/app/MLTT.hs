module Main where

import Language.MLTT.Build (buildMain)
import System.Environment (getArgs)

main :: IO ()
main = buildMain =<< getArgs
