module Main where

import GHC.IO.Encoding    (setLocaleEncoding)
import Language.MLTT.Build (buildMain)
import System.Environment (getArgs)
import System.IO          (hSetEncoding, stderr, stdin, stdout, utf8)

-- | MLTT sources are UTF-8 wherever they come from, so fix every channel to
-- it up front: the locale default covers files the builder reads, and the
-- standard handles cover piped sources, the session and the output. On
-- Windows the default is the local code page, which garbles Π and 𝟙 on the
-- way in and refuses them on the way out.
main :: IO ()
main = do
  setLocaleEncoding utf8
  mapM_ (`hSetEncoding` utf8) [stdin, stdout, stderr]
  buildMain =<< getArgs
