{-# LANGUAGE DeriveGeneric #-}
-- | Name resolution: which surface spellings denote which declarations.
--
-- Nothing in this module mentions a scope, a 'Control.Monad.Foil.Name', or the
-- kind @S@, and that is the point. Resolution decides /which declaration/ an
-- identifier denotes; the foil decides /which index/ a binder has. The first
-- runs before the second and cannot know its answers, so the two are separated
-- here by a type parameter: a 'Table' maps a spelling to whatever the
-- elaborator wants to hand back, and this module never looks inside it.
--
-- The practical consequence for this demo is that restricting what a client can
-- name (@private@, and what an @import@ brings in) is a computation on
-- 'Table' alone. It never touches a term, so a private helper stays perfectly
-- reducible while being unnameable. That is the distinction between what can be
-- /named/ and what can be /reduced/, and it is why narrowing needs no support
-- from the library at all.
--
-- == Influences
--
-- * Separating resolution from everything downstream of it, and treating a
--   module as a construct that is named, encapsulates declarations and can be
--   imported rather than as a primitive, follows Néron, Tolmach, Visser and
--   Wachsmuth's
--   <https://eelcovisser.org/publications/2015/NeronTVW15.pdf A Theory of Name Resolution>
--   (ESOP 2015). None of the scope-graph machinery is reproduced here; the
--   two-stage split is.
-- * 'visibleAt' and 'openNamespace' follow Lean 4's
--   <https://github.com/leanprover/lean4/blob/master/src/Lean/ResolveName.lean ResolveName>
--   (@resolveUsingNamespace@, @resolveOpenDecls@), with one simplification:
--   Lean collects every candidate and reports an ambiguity, whereas here a
--   nearer declaration silently shadows a farther one.
-- * Restricting the resolver's table rather than the environment is Jon
--   Sterling's, from the <https://jonmsterling.com/01HC/ Pterodactyl worklog>,
--   where @NarrowToUnit@ runs before @ElaborateUnit@.
module Language.MLTT.Resolve where

import           Data.Binary              (Binary)
import           Data.List                (inits, intercalate, stripPrefix)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Maybe               (mapMaybe)
import           GHC.Generics             (Generic)
import qualified Language.MLTT.Syntax.Abs as Raw

-- $setup
-- >>> import qualified Data.Map as Map
-- >>> import qualified Language.MLTT.Syntax.Abs as Raw
-- >>> let declared = Map.fromList [(Raw.VarIdent k, k) | k <- ["Nat.zero", "Nat.Extra.double", "Bool.true"]]

-- * Paths

-- | A namespace path, outermost segment first. The empty path is the top level
-- of a module.
--
-- A path has nothing to do with the file a declaration lives in: @module
-- Data.Nat@ may declare @namespace Peano@, and importers then say
-- @Peano.zero@. The module name orders the build; the namespace qualifies the
-- name.
type Path = [String]

-- | Split a dotted identifier into its segments.
--
-- >>> segments (Raw.VarIdent "Data.Nat.zero")
-- ["Data","Nat","zero"]
segments :: Raw.VarIdent -> [String]
segments (Raw.VarIdent x) = split x
  where
    split s = case break (== '.') s of
      (seg, [])       -> [seg]
      (seg, _ : rest) -> seg : split rest

-- | Show a raw identifier as it was written.
--
-- >>> prettyVarIdent (Raw.VarIdent "Data.Nat.zero")
-- "Data.Nat.zero"
prettyVarIdent :: Raw.VarIdent -> String
prettyVarIdent (Raw.VarIdent x) = x

-- | Join segments back into an identifier.
--
-- >>> joinSegments ["Data","Nat","zero"]
-- VarIdent "Data.Nat.zero"
joinSegments :: [String] -> Raw.VarIdent
joinSegments = Raw.VarIdent . intercalate "."

-- | Qualify a name by a namespace path.
--
-- >>> qualify ["Data","Nat"] (Raw.VarIdent "zero")
-- VarIdent "Data.Nat.zero"
-- >>> qualify [] (Raw.VarIdent "zero")
-- VarIdent "zero"
qualify :: Path -> Raw.VarIdent -> Raw.VarIdent
qualify path name = joinSegments (path <> segments name)

-- * Name tables

-- | Every spelling nameable in some context, and what it denotes.
--
-- The type of what it denotes is a parameter: the elaborator uses this at
-- @'Control.Monad.Foil.Name' n@, and the doctests here use it at 'String'.
type Table v = Map Raw.VarIdent v

-- | Which spellings a table of /fully qualified/ names offers at a given
-- namespace path.
--
-- A declaration @A.B.f@ is nameable as @f@ from inside @A.B@, as @B.f@ from
-- inside @A@, and as @A.B.f@ from anywhere. The rule is one line: strip any
-- prefix of the current path. Longer prefixes are applied later and so win, so
-- a nearer declaration shadows a farther one of the same spelling.
--
-- >>> Map.keys (visibleAt [] declared)
-- [VarIdent "Bool.true",VarIdent "Nat.Extra.double",VarIdent "Nat.zero"]
-- >>> Map.keys (visibleAt ["Nat"] declared)
-- [VarIdent "Bool.true",VarIdent "Extra.double",VarIdent "Nat.Extra.double",VarIdent "Nat.zero",VarIdent "zero"]
-- >>> Map.keys (visibleAt ["Nat","Extra"] declared)
-- [VarIdent "Bool.true",VarIdent "Extra.double",VarIdent "Nat.Extra.double",VarIdent "Nat.zero",VarIdent "double",VarIdent "zero"]
visibleAt :: Path -> Table v -> Table v
visibleAt path declared = Map.fromList
  [ (joinSegments suffix, v)
  | prefix <- inits path                       -- shortest first, so nearest wins
  , (name, v) <- Map.toList declared
  , Just suffix <- [stripPrefix prefix (segments name)]
  , not (null suffix)
  ]

-- | Bring the contents of a namespace into scope unqualified.
--
-- Every spelling starting with the given prefix gains a second spelling with
-- that prefix stripped. The qualified spellings stay, so @open Nat@ never
-- hides @Nat.zero@.
--
-- >>> Map.keys (openNamespace (Raw.VarIdent "Nat") (visibleAt [] declared))
-- [VarIdent "Bool.true",VarIdent "Extra.double",VarIdent "Nat.Extra.double",VarIdent "Nat.zero",VarIdent "zero"]
--
-- Opening a namespace that does not exist brings in nothing, and is not an
-- error:
--
-- >>> Map.keys (openNamespace (Raw.VarIdent "Missing") declared) == Map.keys declared
-- True
openNamespace :: Raw.VarIdent -> Table v -> Table v
openNamespace prefix t = Map.union (Map.fromList opened) t
  where
    prefixSegments = segments prefix
    opened = mapMaybe strip (Map.toList t)
    strip (name, v) = do
      suffix <- stripPrefix prefixSegments (segments name)
      case suffix of
        [] -> Nothing
        _  -> Just (joinSegments suffix, v)

-- * Visibility

-- | Whether a declaration leaves the module that declares it.
data Visibility
  = Public
    -- ^ Exported: an importing module may name it.
  | Private
    -- ^ Not exported. An importing module cannot /name/ it, and can still
    -- /reduce/ through it, since withholding a spelling touches no term.
  deriving (Eq, Show, Read, Generic)

-- | One tag byte, from the 'Generic' shape.
instance Binary Visibility

-- | Add a declaration to what a module exports, if it is public.
--
-- >>> Map.keys (export Public (Raw.VarIdent "Nat.two") "Nat.two" Map.empty)
-- [VarIdent "Nat.two"]
-- >>> Map.keys (export Private (Raw.VarIdent "Nat.two") "Nat.two" Map.empty)
-- []
export :: Visibility -> Raw.VarIdent -> v -> Table v -> Table v
export Public  name v = Map.insert name v
export Private _    _ = id

-- * Suggestions

-- | Spellings in scope that end in the same segment as an unresolved one.
--
-- @Nat.quadruple@ is a plausible thing to have meant by @quadruple@, and in a
-- language with namespaces it is usually the only useful hint there is.
--
-- >>> suggestions (Raw.VarIdent "double") (Map.keys declared)
-- [VarIdent "Nat.Extra.double"]
-- >>> suggestions (Raw.VarIdent "nope") (Map.keys declared)
-- []
suggestions :: Raw.VarIdent -> [Raw.VarIdent] -> [Raw.VarIdent]
suggestions name inScope =
    [ candidate
    | candidate <- inScope
    , candidate /= name
    , lastSegment candidate == lastSegment name ]
  where
    lastSegment = last . segments
