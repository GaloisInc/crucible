-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.BoundedExec
-- Description      : Support for bounding loop depth
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an execution feature for bounding the
-- number of iterations that a loop will exeucte in the simulator.
------------------------------------------------------------------------
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.BoundedExec
  ( boundedExecFeature
  ) where

import           Control.Lens ( (^.), to )
import           Control.Monad ( when )
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Semigroup( (<>) )
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.Analysis.Fixpoint (cfgWeakTopologicalOrdering)
import           Lang.Crucible.Analysis.Fixpoint.Components
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.SimError

import           What4.Interface

data FrameBoundData =
  forall args ret.
    FrameBoundData
    { frameBoundHandle :: !(FnHandle args ret)
    , frameBoundLimit :: !Int
    , frameWtoMap :: !(Map Int (Int,Int))
    , frameBoundCounts :: IORef (Seq Int)
    }

-- | This function takes weak topological order data and computes
--   a mapping from block ID number to (position, depth) pair.  The
--   position value indicates which the position in the WTO listing
--   in which the block ID appears, and the depth indicates the number
--   of nested components the block ID appears in.  Loop backedges
--   occur exactly at places where control flows from a higher position
--   number to a lower position number.  Jumps that exit inner loops
--   to the next iteration of an outer loop are identified by backedges
--   that pass from higher depths to lower depths.
buildWTOMap :: [WTOComponent (Some (BlockID blocks))] -> Map Int (Int,Int)
buildWTOMap = snd . go 0 0 Map.empty
 where
 go :: Int -> Int -> Map Int (Int,Int) -> [WTOComponent (Some (BlockID blocks))] -> (Int, Map Int (Int,Int))
 go !x !_ m [] = (x,m)
 go !x !d m (Vertex (Some bid) : cs) =
    let m' = Map.insert (Ctx.indexVal (blockIDIndex bid)) (x,d) m
     in go (x+1) d m' cs
 go !x !d m (SCC (Some hd) subcs : cs) =
    let m'  = Map.insert (Ctx.indexVal (blockIDIndex hd)) (x,d+1) m
        (x',m'') = go (x+1) (d+1) m' subcs
     in go x' d m'' cs


-- | This function updates the loop bound count at the given depth.
--   Any loop bounds deeper than this are discarded.  If the given
--   sequence is too short to accomidate the given depth, the sequence
--   is extended with 0 counters to the correct depth.
incrementBoundCount :: IORef (Seq Int) -> Int -> IO Int
incrementBoundCount ref depth =
  do cs <- readIORef ref
     case Seq.lookup depth cs of
       Just n ->
         do let n' = n+1
            let cs' = Seq.update depth n' $ Seq.take (depth+1) cs
            writeIORef ref cs'
            return $! n'
       Nothing ->
         do let cs' = cs <> Seq.replicate (depth - Seq.length cs) 0 <> Seq.singleton 1
            writeIORef ref cs'
            return 1


-- | This execution feature allows users to place a bound on the number
--   of iterations that a loop will execute.  Each time a function is called,
--   the included action is called to determine if the loops in that function
--   should be bounded, and what their iteration bound should be.
--
--   The boolean argument indicates if we should generate proof obligations when
--   we cut off loop execution.  If true, loop cutoffs will generate proof obligations
--   which will be provable only if the loop actualy could not have executed that number
--   of iterations.  If false, the execution of loops will be aborted without generating
--   side conditions.
--
--   Note that we compute a weak topological ordering on control flow graphs
--   to determine loop heads and loop nesting structure.  Loop bounds for inner
--   loops are reset on every iteration through an outer loop.
boundedExecFeature ::
  (SomeHandle -> IO (Maybe Int))
    {- ^ Action for computing loop bounds for functions when they are called -} ->
  Bool {- ^ Produce a proof obligation when resources are exhausted? -} ->
  IO (GenericExecutionFeature sym)
boundedExecFeature getLoopBounds generateSideConditions =
  do stackRef <- newIORef []
     return $ GenericExecutionFeature $ onStep stackRef

 where
 buildFrameData :: ResolvedCall p sym ext ret -> IO (Maybe FrameBoundData)
 buildFrameData OverrideCall{} = return Nothing
 buildFrameData (CrucibleCall _entry CallFrame{ _frameCFG = g }) =
   do let wtoMap = buildWTOMap (cfgWeakTopologicalOrdering g)
      mn <- getLoopBounds (SomeHandle (cfgHandle g))
      case mn of
        Nothing -> return Nothing
        Just n ->
          do cntRef <- newIORef mempty
             let fbd = FrameBoundData
                       { frameBoundHandle = cfgHandle g
                       , frameBoundLimit  = n
                       , frameWtoMap      = wtoMap
                       , frameBoundCounts = cntRef
                       }
             return (Just fbd)

 checkBackedge :: IORef [Maybe FrameBoundData] -> Some (BlockID blocks) -> BlockID blocks tgt_args -> IO (Maybe Int)
 checkBackedge stackRef (Some bid_curr) bid_tgt =
   do readIORef stackRef >>= \case
        ( Just fbd : _ ) ->
          do let id_curr = Ctx.indexVal (blockIDIndex bid_curr)
             let id_tgt  = Ctx.indexVal (blockIDIndex bid_tgt)
             let m = frameWtoMap fbd
             case (Map.lookup id_curr m, Map.lookup id_tgt m) of
               (Just (cx, _cd), Just (tx, td)) | tx <= cx ->
                  do q <- incrementBoundCount (frameBoundCounts fbd) td
                     if q > frameBoundLimit fbd then
                       return (Just (frameBoundLimit fbd))
                     else
                       return Nothing
               _ -> return Nothing

        _ -> return Nothing

 onStep ::
   IORef [Maybe FrameBoundData] ->
   ExecState p sym ext rtp ->
   IO (Maybe (ExecState p sym ext rtp))

 onStep stackRef exst = case exst of
   UnwindCallState _vfv _ar _st ->
     do modifyIORef stackRef (drop 1)
        return Nothing
   InitialState{} ->
     do writeIORef stackRef [Nothing]
        return Nothing
   CallState _rh call _st ->
     do boundData <- buildFrameData call
        modifyIORef stackRef (boundData:)
        return Nothing
   TailCallState _vfv call _st ->
     do boundData <- buildFrameData call
        modifyIORef stackRef ((boundData:) . drop 1)
        return Nothing
   ReturnState _nm _vfv _pr _st ->
     do modifyIORef stackRef (drop 1)
        return Nothing
   ControlTransferState res st -> stateSolverProof st $
     let sym = st^.stateSymInterface
         msg n = "reached maximum number of loop iterations (" ++ show n ++ ")"
         err loc n = SimError loc (ResourceExhausted (msg n))
     in
     case res of
       ContinueResumption (ResolvedJump tgt_id _) ->
         do let loc = st^.stateCrucibleFrame.to frameProgramLoc
            overLimit <- checkBackedge stackRef (st^.stateCrucibleFrame.frameBlockID) tgt_id
            case overLimit of
              Just n ->
                do when generateSideConditions
                        (addProofObligation sym (LabeledPred (falsePred sym) (err loc n)))
                   return (Just (AbortState (AssumedFalse (AssumingNoError (err loc n))) st))
              Nothing -> return Nothing

       CheckMergeResumption (ResolvedJump tgt_id _) ->
         do let loc = st^.stateCrucibleFrame.to frameProgramLoc
            overLimit <- checkBackedge stackRef (st^.stateCrucibleFrame.frameBlockID) tgt_id
            case overLimit of
              Just n ->
                do when generateSideConditions
                        (addProofObligation sym (LabeledPred (falsePred sym) (err loc n)))
                   return (Just (AbortState (AssumedFalse (AssumingNoError (err loc n))) st))
              Nothing ->
                do return Nothing

       _ -> return Nothing
   _ -> return Nothing
