-- | Set Unicode-capable output before any test output is printed; hspec
-- discovers this module and wraps every spec in 'hook'.
--
-- On Windows, GHC encodes standard output with the local code page, which
-- cannot represent characters such as Π or 𝟙 that appear in the test
-- descriptions, so the reporter dies with @commitBuffer: invalid argument@.
-- Setting the handles to UTF-8 in-process also covers redirected output,
-- which a @chcp@ call in the workflow never reached.
module SpecHook (hook) where

import           System.IO  (hSetEncoding, stderr, stdout, utf8)
import           Test.Hspec (Spec, runIO)

hook :: Spec -> Spec
hook spec = runIO (hSetEncoding stdout utf8 >> hSetEncoding stderr utf8) >> spec
