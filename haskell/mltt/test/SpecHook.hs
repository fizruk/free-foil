-- | Set Unicode-capable input and output before any test runs; hspec
-- discovers this module and wraps every spec in 'hook'.
--
-- On Windows, GHC encodes handles with the local code page, which cannot
-- represent characters such as Π or 𝟙: the reporter used to die printing a
-- test description (@commitBuffer: invalid argument@), and a spec that
-- 'readFile's a UTF-8 example mis-decoded it and failed to parse. Setting
-- the standard handles and the locale default (which every newly opened
-- file inherits) to UTF-8 in-process covers both, including redirected
-- output that a @chcp@ call in the workflow never reached.
module SpecHook (hook) where

import           GHC.IO.Encoding (setLocaleEncoding)
import           System.IO       (hSetEncoding, stderr, stdout, utf8)
import           Test.Hspec      (Spec, runIO)

hook :: Spec -> Spec
hook spec = runIO setUtf8 >> spec
  where
    setUtf8 = do
      setLocaleEncoding utf8
      hSetEncoding stdout utf8
      hSetEncoding stderr utf8
