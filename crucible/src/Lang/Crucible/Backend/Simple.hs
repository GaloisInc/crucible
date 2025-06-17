------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Backend.Simple
-- Description : The "simple" solver backend
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Ryan Scott <rscott@galois.com>, Langston Barrett <langston@galois.com>
-- Stability   : provisional
--
-- An "offline" backend for communicating with SMT solvers. In contrast to
-- "Lang.Crucible.Backend.Online", this backend does not maintain a persistent
-- connection to a solver.
-- ----------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Backend.Simple
  ( -- * SimpleBackend
    SimpleBackend
  , newSimpleBackend
    -- * Re-exports
  , B.FloatMode
  , B.FloatModeRepr(..)
  , B.FloatIEEE
  , B.FloatUninterpreted
  , B.FloatReal
  , B.Flags
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad (void)
import           Data.IORef (readIORef)

import           What4.Config
import           What4.Interface
import qualified What4.Expr.Builder as B

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

------------------------------------------------------------------------
-- SimpleBackend

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

type AS t =
     AssumptionStack (CrucibleAssumptions (B.Expr t))
                     (LabeledPred (B.BoolExpr t) SimError)

data SimpleBackend t st fs =
  SimpleBackend
  { sbAssumptionStack :: AS t
  , sbExprBuilder :: B.ExprBuilder t st fs
  }

newSimpleBackend ::
  B.ExprBuilder t st fs ->
  IO (SimpleBackend t st fs)
newSimpleBackend sym =
  do as <- AS.initAssumptionStack (sym ^. B.exprCounter)
     tryExtendConfig backendOptions (getConfiguration sym)
     return SimpleBackend
            { sbAssumptionStack = as
            , sbExprBuilder = sym
            }

instance HasSymInterface (B.ExprBuilder t st fs) (SimpleBackend t st fs) where
  backendGetSym = sbExprBuilder  

instance IsSymInterface (B.ExprBuilder t st fs) =>
  IsSymBackend (B.ExprBuilder t st fs) (SimpleBackend t st fs) where

  addDurableProofObligation bak a =
     AS.addProofObligation a (sbAssumptionStack bak)

  addAssumption bak a =
    case impossibleAssumption a of
      Just rsn -> abortExecBecause rsn
      Nothing  -> AS.appendAssumptions (singleAssumption a) (sbAssumptionStack bak)

  addAssumptions bak ps = do
    AS.appendAssumptions ps (sbAssumptionStack bak)

  collectAssumptions bak =
    AS.collectAssumptions (sbAssumptionStack bak)

  getProofObligations bak = do
    AS.getProofObligations (sbAssumptionStack bak)

  clearProofObligations bak = do
    AS.clearProofObligations (sbAssumptionStack bak)

  pushAssumptionFrame bak = do
    AS.pushFrame (sbAssumptionStack bak)

  popAssumptionFrame bak ident = do
    AS.popFrame ident (sbAssumptionStack bak)

  popAssumptionFrameAndObligations bak ident = do
    AS.popFrameAndGoals ident (sbAssumptionStack bak)

  popUntilAssumptionFrame bak ident = do
    void $ AS.popFramesUntil ident (sbAssumptionStack bak)

  saveAssumptionState bak = do
    AS.saveAssumptionStack (sbAssumptionStack bak)

  restoreAssumptionState bak newstk = do
    AS.restoreAssumptionStack newstk (sbAssumptionStack bak)

  getBackendState bak = readIORef (AS.proofObligations (sbAssumptionStack bak))
