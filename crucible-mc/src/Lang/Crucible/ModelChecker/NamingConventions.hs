{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.NamingConventions
-- Description      : Decisions about how to name Crucible variables in the model
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.NamingConventions
  ( blockArgumentName,
    currentBlockVariable,
    functionArgumentName,
    hasReturnedVariable,
    natOfBlockID,
    namesForContext,
  )
where

import Data.Functor.Const (Const (..))
import Data.Functor.Identity (runIdentity)
import qualified Data.Parameterized.Context as Ctx
import GHC.Natural
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.Types

-- | @currentBlockVariable@ will be used for the name of the variable
-- representing the current basic block of execution
currentBlockVariable :: String
currentBlockVariable = "block__CRUCIBLEMC__"

-- | @returnValueVariable@ will be used for the name of the variable
-- representing the return value of the entire program
-- returnValueVariable :: String
-- returnValueVariable = "ret__CRUCIBLEMC__"

-- | @hasReturnedVariable@ will be used to indicate when the original program is
-- considered to have returned, so as to condition when the final result
-- equation is meant to hold
hasReturnedVariable :: String
hasReturnedVariable = "hasReturned__CRUCIBLEMC__"

natOfBlockID :: Core.BlockID ctx tp -> Natural
natOfBlockID = intToNatural . Ctx.indexVal . Core.blockIDIndex

-- | @blockArgumentName@ is the naming convention for the arguments of a given block
blockArgumentName ::
  Core.BlockID ctx tp ->
  -- we actually don't care that the index comes from the same context
  forall ctx' (tp' :: CrucibleType). Ctx.Index ctx' tp' -> String
blockArgumentName blockID idx =
  "block_" ++ show (natOfBlockID blockID) ++ "_argument_" ++ Core.showF idx

-- | @functionArgumentName@ is the naming convention for the arguments of a given function
-- FIXME: pass the function name and use it?
functionArgumentName ::
  forall ctx (tp :: CrucibleType). Ctx.Index ctx tp -> String
functionArgumentName idx =
  "function_argument_" ++ Core.showF idx

-- | @namesForContext@ takes as input a naming convention for some elements of
-- an assignment, and returns the corresponding assignment of names
namesForContext ::
  (forall tp. Ctx.Index ctx tp -> String) ->
  Ctx.Assignment TypeRepr ctx ->
  Ctx.Assignment (Const String) ctx
namesForContext nameForIndex =
  runIdentity . Ctx.traverseWithIndex (\index _ -> pure (Const (nameForIndex index)))
