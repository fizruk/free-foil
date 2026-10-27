-- | This module defines a variation of
-- free scoped (relative) monads relying on the foil for
-- the scope-safe efficient handling of the binders.
--
-- See description of the approach in [«Free Foil: Generating Efficient and Scope-Safe Abstract Syntax»](https://arxiv.org/abs/2405.16384).
module Control.Monad.Free.Foil (
  -- * Terms
  AST(..),
  ScopedAST(..),

  -- * Substitution
  substitute,
  substituteRefreshed,
  substitutePattern,

  -- * Transformations between signatures
  foldAST,
  hoistAST,

  -- * \(\alpha\)-equivalence
  refreshAST,
  refreshScopedAST,
  alphaEquivRefreshed,
  alphaEquiv,
  alphaEquivScoped,
  renamedId,
  bindPairs,
  alphaEquivEnv,
  alphaEquivScopedEnv,

  -- ** Unsafe equality checks
  unsafeEqAST,
  unsafeEqScopedAST,
  unsafeEqASTIn,
  unsafeEqScopedASTIn,

  -- * Converting to and from free foil
  -- ** Convert to free foil
  UnresolvedName(..),
  unresolvedNames,
  unresolvedNamesWith,
  tryConvertToAST,
  tryConvertToASTWith,
  unsafeConvertToAST,
  unsafeConvertToScopedAST,

  -- ** Convert from free foil
  convertFromAST,
  convertFromScopedAST,
  convertFromASTWith,

  -- ** Unsinking AST
  supportOf,
  supportOfScopedAST,
  withRelevantScope,
  unsinkAST,
  freeVarsOf,
  freeVarsOfScopedAST,
) where

import           Control.Monad.Free.Foil.Internal
