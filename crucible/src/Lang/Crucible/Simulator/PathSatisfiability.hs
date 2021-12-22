-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.PathSatisfiability
-- Description      : Support for performing path satisfiability checks
--                    at symbolic branch points
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.PathSatisfiability
  ( checkPathSatisfiability
  , pathSatisfiabilityFeature
  , checkSatToConsiderBranch
  , BranchResult(..)
  ) where

import           Control.Lens( (^.) )
import           Control.Monad.Reader
import qualified Prettyprinter as PP

import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.Online (BranchResult(..))
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.Operations

import           What4.Concrete
import           What4.Config
import           What4.Interface
import           What4.ProgramLoc
import           What4.SatResult

checkPathSatisfiability :: ConfigOption BaseBoolType
checkPathSatisfiability = configOption knownRepr "checkPathSat"

pathSatOptions :: [ConfigDesc]
pathSatOptions =
  [ mkOpt
      checkPathSatisfiability
      boolOptSty
      (Just (PP.pretty "Perform path satisfiability checks at symbolic branches"))
      (Just (ConcreteBool True))
  ]


pathSatisfiabilityFeature :: forall sym.
  IsSymInterface sym =>
  sym ->
  (Maybe ProgramLoc -> Pred sym -> IO BranchResult)
   {- ^ An action for considering the satisfiability of a predicate.
        In the current state of the symbolic interface, indicate what
        we can determine about the given predicate. -} ->
  IO (GenericExecutionFeature sym)
pathSatisfiabilityFeature sym considerSatisfiability =
  do extendConfig pathSatOptions (getConfiguration sym)
     pathSatOpt <- liftIO $ getOptionSetting checkPathSatisfiability (getConfiguration sym)
     return $ GenericExecutionFeature $ onStep pathSatOpt

 where
 onStep ::
   OptionSetting BaseBoolType ->
   ExecState p sym ext rtp ->
   IO (ExecutionFeatureResult p sym ext rtp)

 onStep pathSatOpt (SymbolicBranchState p tp fp _tgt st) =
   getOpt pathSatOpt >>= \case
     False -> return ExecutionFeatureNoChange
     True ->
       do loc <- getCurrentProgramLoc sym
          considerSatisfiability ploc p >>= \case
               IndeterminateBranchResult ->
                 return ExecutionFeatureNoChange
               NoBranch chosen_branch -> withBackend (st ^. stateContext) $ \bak ->
                 do p' <- if chosen_branch then return p else notPred sym p
                    let frm = if chosen_branch then tp else fp
                    addAssumption bak (BranchCondition loc (pausedLoc frm) p')
                    ExecutionFeatureNewState <$> runReaderT (resumeFrame frm (asContFrame (st^.stateTree))) st
               UnsatisfiableContext ->
                 return (ExecutionFeatureNewState (AbortState (InfeasibleBranch loc) st))
   where
     ploc = st ^. stateLocation

 onStep _ _ = return ExecutionFeatureNoChange


checkSatToConsiderBranch ::
  IsSymInterface sym =>
  sym ->
  (Pred sym -> IO (SatResult () ())) ->
  (Pred sym -> IO BranchResult)
checkSatToConsiderBranch sym checkSat p =
  do pnot <- notPred sym p
     p_res <- checkSat p
     pnot_res <- checkSat pnot
     case (p_res, pnot_res) of
       (Unsat{}, Unsat{}) -> return UnsatisfiableContext
       (_      , Unsat{}) -> return (NoBranch True)
       (Unsat{}, _      ) -> return (NoBranch False)
       _                  -> return IndeterminateBranchResult
