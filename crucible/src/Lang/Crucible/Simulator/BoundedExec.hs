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
-- number of iterations that a loop will execute in the simulator.
------------------------------------------------------------------------
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-orphans #-}
module Lang.Crucible.Simulator.BoundedExec
  ( boundedExecFeature,
    emptyBoundedExecVariable,
    HasBoundedExec(..)
  ) where

import           Control.Lens ( (^.), to, (&), (%~), (.~) )
import           Control.Monad ( when )
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Word


import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

import           Lang.Crucible.Analysis.Fixpoint.Components
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Panic
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.SimError

import           What4.FunctionName
import           What4.Interface
import qualified Control.Lens as Lens
import qualified Lang.Crucible.Simulator as C

data FrameBoundData =
  forall args ret.
    FrameBoundData
    { frameBoundHandle :: !(FnHandle args ret)
    , frameBoundLimit :: !Word64
    , frameWtoMap :: !(Map Int (Int,Int))
    , frameBoundCounts :: Seq Word64
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
 go !x !d m (SCC scc : cs) =
    let m'  = viewSome (\hd -> Map.insert (Ctx.indexVal (blockIDIndex hd)) (x,d+1) m) (wtoHead scc)
        (x',m'') = go (x+1) (d+1) m' $ wtoComps scc
     in go x' d m'' cs


-- | This function updates the loop bound count at the given depth.
--   Any loop bounds deeper than this are discarded.  If the given
--   sequence is too short to accommodate the given depth, the sequence
--   is extended with 0 counters to the correct depth.
incrementBoundCount :: Seq Word64 -> Int -> (Seq Word64, Word64)
incrementBoundCount cs depth =
  case Seq.lookup depth cs of
     Just n ->
       do let n' = n+1
          let cs' = Seq.update depth n' $ Seq.take (depth+1) cs
          n' `seq` cs' `seq` (cs', n')
     Nothing ->
       do let cs' = cs <> Seq.replicate (depth - Seq.length cs) 0 <> Seq.singleton 1
          cs' `seq` (cs', 1)

instance IntrinsicClass sym "BoundedExecFrameData" where
  type Intrinsic sym "BoundedExecFrameData" ctx = [Either FunctionName FrameBoundData]

  muxIntrinsic _sym _iTypes _nm _ _p fd1 fd2 = combineFrameBoundData fd1 fd2

mergeCounts :: Seq Word64 -> Seq Word64 -> Seq Word64
mergeCounts cx cy =
  Seq.fromFunction
    (max (Seq.length cx) (Seq.length cy))
    (\i -> max (fromMaybe 0 $ Seq.lookup i cx)
               (fromMaybe 0 $ Seq.lookup i cy))

mergeFBD ::
  FrameBoundData ->
  FrameBoundData ->
  IO FrameBoundData
mergeFBD x@FrameBoundData{ frameBoundHandle = hx } y@FrameBoundData{ frameBoundHandle = hy }
  | Just _ <- testEquality (handleID hx) (handleID hy) =
       return x{ frameBoundCounts = mergeCounts (frameBoundCounts x) (frameBoundCounts y) }

  | otherwise =
       panic "BoundedExec.mergeFBD"
       [ "Attempted to merge frame bound data from different function activations: "
       , " ** " ++ show hx
       , " ** " ++ show hy
       ]


combineFrameBoundData ::
  [Either FunctionName FrameBoundData] ->
  [Either FunctionName FrameBoundData] ->
  IO [Either FunctionName FrameBoundData]
combineFrameBoundData [] [] = return []

combineFrameBoundData (Left nmx:xs) (Left nmy : _) | nmx == nmy
  = return (Left nmx : xs)

combineFrameBoundData (Right x:xs) (Right y:_)
  = (\x' -> Right x' : xs) <$> mergeFBD x y

combineFrameBoundData xs ys
  = panic "BoundedExec.combineFrameBoundData"
      [ "Attempt to combine incompatible frame bound data: stack shape mismatch:"
      , " *** " ++ show (printStack xs)
      , " *** " ++ show (printStack ys)
      ]

printStack :: [Either FunctionName FrameBoundData] -> [String]
printStack [] = []
printStack (Left nm :xs) = show nm : printStack xs
printStack (Right FrameBoundData{ frameBoundHandle = h } : xs) = show h : printStack xs


type BoundedExecGlobal = GlobalVar (IntrinsicType "BoundedExecFrameData" EmptyCtx)

class HasBoundedExec p where
  boundedExecVariable :: Lens.Lens' p BoundedExecGlobal

emptyBoundedExecVariable :: BoundedExecGlobal
emptyBoundedExecVariable = (error "Global variable for BoundedExecData not initialized")

-- | This execution feature allows users to place a bound on the number
--   of iterations that a loop will execute.  Each time a function is called,
--   the included action is called to determine if the loops in that function
--   should be bounded, and what their iteration bound should be.
--
--   The boolean argument indicates if we should generate proof obligations when
--   we cut off loop execution.  If true, loop cutoffs will generate proof obligations
--   which will be provable only if the loop actually could not have executed that number
--   of iterations.  If false, the execution of loops will be aborted without generating
--   side conditions.
--
--   Note that we compute a weak topological ordering on control flow graphs
--   to determine loop heads and loop nesting structure.  Loop bounds for inner
--   loops are reset on every iteration through an outer loop.
boundedExecFeature :: HasBoundedExec p =>
  (SomeHandle -> IO (Maybe Word64))
    {- ^ Action for computing loop bounds for functions when they are called -} ->
  Bool {- ^ Produce a proof obligation when resources are exhausted? -} ->
  IO (ExecFeatureWithPersonality sym p)
boundedExecFeature getLoopBounds generateSideConditions =
     return $ ExecFeatureWithPersonality $ onStep

 where
 buildFrameData :: ResolvedCall p sym ext ret -> IO (Either FunctionName FrameBoundData)
 buildFrameData (OverrideCall ov _) = return (Left (overrideName ov))
 buildFrameData (CrucibleCall _entry CallFrame{ _frameCFG = g }) =
   do let wtoMap = buildWTOMap (cfgWeakTopologicalOrdering g)
      mn <- getLoopBounds (SomeHandle (cfgHandle g))
      case mn of
        Nothing -> return $ Left  $ handleName (cfgHandle g)
        Just n  -> return $ Right $ FrameBoundData
                       { frameBoundHandle = cfgHandle g
                       , frameBoundLimit  = n
                       , frameWtoMap      = wtoMap
                       , frameBoundCounts = mempty
                       }

 checkBackedge ::
  BoundedExecGlobal ->
   Some (BlockID blocks) ->
   BlockID blocks tgt_args ->
   SymGlobalState sym ->
   IO (SymGlobalState sym, Maybe Word64)
 checkBackedge gv (Some bid_curr) bid_tgt globals =
      case fromMaybe [] (lookupGlobal gv globals) of
        ( Right fbd : rest ) ->
          do let id_curr = Ctx.indexVal (blockIDIndex bid_curr)
             let id_tgt  = Ctx.indexVal (blockIDIndex bid_tgt)
             let m = frameWtoMap fbd
             case (Map.lookup id_curr m, Map.lookup id_tgt m) of
               (Just (cx, _cd), Just (tx, td)) | tx <= cx ->
                  do let cs       = frameBoundCounts fbd
                     let (cs', q) = incrementBoundCount cs td
                     let fbd'     = fbd{ frameBoundCounts = cs' }
                     let globals' = insertGlobal gv (Right fbd' : rest) globals
                     if q > frameBoundLimit fbd then
                       return (globals', Just (frameBoundLimit fbd))
                     else
                       return (globals', Nothing)

               _ -> return (globals, Nothing)
        _ -> return (globals, Nothing)

 modifyStackState :: HasBoundedExec p =>
   (SimState p sym ext rtp f args -> ExecState p sym ext rtp) ->
   SimState p sym ext rtp f args ->
   ([Either FunctionName FrameBoundData] -> [Either FunctionName FrameBoundData]) ->
   IO (ExecutionFeatureResult p sym ext rtp)
 modifyStackState mkSt st f =
      let gv = st Lens.^. C.stateContext . C.cruciblePersonality . boundedExecVariable
          xs = case lookupGlobal gv (st ^. stateGlobals) of
                 Nothing -> error "bounded execution global not defined!"
                 Just v  -> v
          st' = st & stateGlobals %~ insertGlobal gv (f xs) in
      return (ExecutionFeatureModifiedState (mkSt st'))

 onTransition :: HasBoundedExec p =>
   BlockID blocks tgt_args ->
   ControlResumption p sym ext rtp (CrucibleLang blocks ret) ->
   SimState p sym ext rtp (CrucibleLang blocks ret) ('Just a) ->
   IO (ExecutionFeatureResult p sym ext rtp)
 onTransition tgt_id res st = stateSolverProof st $
  do let sym = st^.stateSymInterface
     let simCtx = st^.stateContext
     let gv = st Lens.^. C.stateContext . C.cruciblePersonality . boundedExecVariable
     (globals', overLimit) <- checkBackedge gv (st^.stateCrucibleFrame.frameBlockID) tgt_id (st^.stateGlobals)
     let st' = st & stateGlobals .~ globals'
     case overLimit of
       Just n ->
         do let msg = "reached maximum number of loop iterations (" ++ show n ++ ")"
            let loc = st^.stateCrucibleFrame.to frameProgramLoc
            let err = SimError loc (ResourceExhausted msg)
            when generateSideConditions $ withBackend simCtx $ \bak ->
              addProofObligation bak (LabeledPred (falsePred sym) err)
            return (ExecutionFeatureNewState (AbortState (AssertionFailure err) st'))
       Nothing -> return (ExecutionFeatureModifiedState (ControlTransferState res st'))

 onStep :: HasBoundedExec p =>
   ExecState p sym ext rtp ->
   IO (ExecutionFeatureResult p sym ext rtp)

 onStep = \case
   InitialState simctx globals ah ret cont ->
     do let halloc = simHandleAllocator simctx
        gv <- freshGlobalVar halloc (Text.pack "BoundedExecFrameData") knownRepr
        let globals' = insertGlobal gv [Left "_init"] globals
        let simctx' = simctx{ ctxIntrinsicTypes = MapF.insert (knownSymbol @"BoundedExecFrameData") IntrinsicMuxFn (ctxIntrinsicTypes simctx) } & C.cruciblePersonality . boundedExecVariable Lens..~ gv
        return (ExecutionFeatureModifiedState (InitialState simctx' globals' ah ret cont))

   CallState rh call st ->
     do boundData <- buildFrameData call
        modifyStackState (CallState rh call) st (boundData:)

   TailCallState vfv call st ->
     do boundData <- buildFrameData call
        modifyStackState (TailCallState vfv call) st ((boundData:) . drop 1)

   ReturnState nm vfv pr st ->
        modifyStackState (ReturnState nm vfv pr) st (drop 1)

   UnwindCallState vfv ar st ->
        modifyStackState (UnwindCallState vfv ar) st (drop 1)

   ControlTransferState res st ->
     case res of
       ContinueResumption (ResolvedJump tgt_id _)  ->  onTransition tgt_id res st
       CheckMergeResumption (ResolvedJump tgt_id _) -> onTransition tgt_id res st
       _ -> return ExecutionFeatureNoChange

   _ -> return ExecutionFeatureNoChange
