-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator
-- Description      : Reexports of relevant parts of submodules
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module reexports the parts of the symbolic simulator codebase
-- that are most relevant for users.  Additional types and operations
-- are exported from the relavant submodules if necessary.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator
  ( -- * Register values
    RegValue
  , RegValue'(..)
    -- ** Variants
  , VariantBranch(..)
  , injectVariant
    -- ** Any Values
  , AnyValue(..)
    -- ** Function Values
  , FnVal(..)
  , fnValType
    -- ** Recursive Values
  , RolledType(..)

    -- * Register maps
  , RegEntry(..)
  , RegMap(..)
  , emptyRegMap
  , regVal
  , assignReg
  , reg

    -- * SimError
  , SimErrorReason(..)
  , SimError(..)
  , ppSimError

    -- * SimGlobalState
  , GlobalVar(..)
  , SymGlobalState
  , emptyGlobals

    -- * GlobalPair
  , GlobalPair(..)
  , gpValue
  , gpGlobals

    -- * AbortedResult
  , AbortedResult(..)

    -- * Partial result
  , PartialResult(..)
  , partialValue

    -- * Execution states
  , ExecResult(..)
  , ExecState(..)
  , ExecCont
  , execResultContext

    -- * Simulator context
    -- ** Function bindings
  , Override(..)
  , FnState(..)
  , FunctionBindings

    -- ** Extensions
  , ExtensionImpl(..)
  , EvalStmtFunc
  , emptyExtensionImpl

    -- ** SimContext record
  , IsSymInterfaceProof
  , SimContext(..)
  , initSimContext
  , ctxSymInterface
  , functionBindings
  , cruciblePersonality
  , profilingMetrics

    -- * SimState
  , SimState
  , initSimState
  , defaultAbortHandler
  , AbortHandler(..)
  , CrucibleState
  , stateContext

    -- * Intrinsic types
  , IntrinsicClass
  , IntrinsicMuxFn(..)
  , IntrinsicTypes
  , emptyIntrinsicTypes

    -- * Evaluation
  , executeCrucible
  , singleStepCrucible
  , evalReg
  , evalArgs
  , stepStmt
  , stepTerm
  , stepBasicBlock
  , ExecutionFeature
  , GenericExecutionFeature
  , genericToExecutionFeature
  , timeoutFeature

    -- * OverrideSim monad
  , module Lang.Crucible.Simulator.OverrideSim
  ) where

import Lang.Crucible.CFG.Common
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.EvalStmt
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.Intrinsics
import Lang.Crucible.Simulator.Operations
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.SimError
