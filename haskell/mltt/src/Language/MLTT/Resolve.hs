{-# LANGUAGE LambdaCase #-}
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
-- name — @private@, and what an @import@ brings in — is a computation on
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

import           Data.List                (inits, intercalate, nub, stripPrefix)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Maybe               (mapMaybe)
import           Data.Set                 (Set)
import qualified Data.Set                 as Set
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

-- | Every spelling in a table, for an error message.
spellings :: Table v -> [String]
spellings t = [x | Raw.VarIdent x <- Map.keys t]

-- * Free identifiers of a raw term
--
-- The elaborator has to know that every identifier a term mentions resolves
-- /before/ it converts the term, because conversion crashes on an unknown name
-- rather than reporting one. Doing the check here is what turns an unnameable
-- private helper into a diagnostic with a name in it.

-- | The identifiers a raw pattern binds.
--
-- >>> patternIdents (Raw.PatternPair () (Raw.PatternVar () (Raw.VarIdent "x")) (Raw.PatternWildcard ()))
-- [VarIdent "x"]
patternIdents :: Raw.Pattern' a -> [Raw.VarIdent]
patternIdents = \case
  Raw.PatternWildcard _ -> []
  Raw.PatternVar _ x    -> [x]
  Raw.PatternPair _ l r -> patternIdents l <> patternIdents r

-- | The identifiers a raw term mentions free, in order of first occurrence.
freeIdents :: Raw.Term' a -> [Raw.VarIdent]
freeIdents = nub . go Set.empty
  where
    scoped bound (Raw.AScopedTerm _ body) = go bound body

    bind :: Raw.Pattern' a -> Set Raw.VarIdent -> Set Raw.VarIdent
    bind p bound = foldr Set.insert bound (patternIdents p)

    go :: Set Raw.VarIdent -> Raw.Term' a -> [Raw.VarIdent]
    go bound = \case
      Raw.Var _ x
        | x `Set.member` bound -> []
        | otherwise            -> [x]
      Raw.Pi _ p ty body    -> go bound ty <> scoped (bind p bound) body
      Raw.Sigma _ p ty body -> go bound ty <> scoped (bind p bound) body
      Raw.Lam _ p body      -> scoped (bind p bound) body
      Raw.Let _ p val body  -> go bound val <> scoped (bind p bound) body
      Raw.Arrow _ a b       -> go bound a <> go bound b
      Raw.Product _ a b     -> go bound a <> go bound b
      Raw.App _ f x         -> go bound f <> go bound x
      Raw.First _ t         -> go bound t
      Raw.Second _ t        -> go bound t
      Raw.Universe _        -> []
      Raw.UnitType _        -> []
      Raw.UnitVal _         -> []
      Raw.IdType _ a x y    -> go bound a <> go bound x <> go bound y
      Raw.Refl _ x          -> go bound x
      Raw.J _ m c p         -> go bound m <> go bound c <> go bound p
      Raw.Pair _ l r        -> go bound l <> go bound r
      Raw.Ann _ t ty        -> go bound t <> go bound ty

-- | The identifiers a term mentions that the table cannot resolve.
unresolved :: Table v -> Raw.Term' a -> [Raw.VarIdent]
unresolved table = filter (`Map.notMember` table) . freeIdents
