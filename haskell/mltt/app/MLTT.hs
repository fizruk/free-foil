module Main where

import Language.MLTT.Impl  (defaultMain)
import System.Environment (getArgs)

main :: IO ()
main = defaultMain =<< getArgs
