-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.BoundedRecursion
-- Description      : Support for bounding function recursion depth
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an execution feature for bounding recursion.
-- Essentially, we bound the number of times any particular function
-- is allowed to have active frames on the call stack.
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
module Lang.Crucible.Simulator.BoundedRecursion
  ( boundedRecursionFeature
  ) where

import           Control.Lens ( (^.), (&), (%~) )
import           Control.Monad (when)
import           Data.IORef
import           Data.Maybe
import qualified Data.Text as Text
import           Data.Word
import qualified Data.Map.Strict as Map

import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Map as MapF

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Panic
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Types

type BoundedRecursionMap = Map.Map SomeHandle Word64

instance IntrinsicClass sym "BoundedRecursionData" where
  type Intrinsic sym "BoundedRecursionData" ctx = [BoundedRecursionMap]
  muxIntrinsic _sym _iTypes _nm _ _p x _y = return x

type BoundedRecursionGlobal = GlobalVar (IntrinsicType "BoundedRecursionData" EmptyCtx)

-- | This execution feature allows users to place a bound on the number of
--   recursive calls that a function can execute.  Each time a function is
--   called, the number of activations of the functions is incremented, and
--   the path is aborted if the bound is exceeded.
--
--   The boolean argument indicates if we should generate proof obligations when
--   we cut off recursion.  If true, recursion cutoffs will generate proof obligations
--   which will be provable only if the function actually could not have executed that number
--   of times.  If false, the execution of recursive functions will be aborted without
--   generating side conditions.
boundedRecursionFeature ::
  (SomeHandle -> IO (Maybe Word64))
    {- ^ Action for computing what recursion depth to allow for the given function -}  ->
  Bool {- ^ Produce a proof obligation when resources are exhausted? -} ->
  IO (GenericExecutionFeature sym)

boundedRecursionFeature getRecursionBound generateSideConditions =
  do gvRef <- newIORef (error "Global variable for BoundedRecusionData not initilized" :: BoundedRecursionGlobal)
     return $ GenericExecutionFeature $ onStep gvRef

 where
 popFrame ::
   IORef BoundedRecursionGlobal ->
   (SimState p sym ext rtp f args -> ExecState p sym ext rtp) ->
   SimState p sym ext rtp f args ->
   IO (ExecutionFeatureResult p sym ext rtp)
 popFrame gvRef mkSt st =
   do gv <- readIORef gvRef
      case lookupGlobal gv (st ^. stateGlobals) of
        Nothing -> panic "bounded recursion" ["global not defined!"]
        Just [] -> panic "bounded recursion" ["pop on empty stack!"]
        Just (_:xs) ->
          do let st' = st & stateGlobals %~ insertGlobal gv xs
             return (ExecutionFeatureModifiedState (mkSt st'))

 pushFrame ::
   IORef BoundedRecursionGlobal ->
   (BoundedRecursionMap -> BoundedRecursionMap -> [BoundedRecursionMap] -> [BoundedRecursionMap]) ->
   SomeHandle ->
   (SimState p sym ext rtp f args -> ExecState p sym ext rtp) ->
   SimState p sym ext rtp f args ->
   IO (ExecutionFeatureResult p sym ext rtp)
 pushFrame gvRef rebuildStack h mkSt st = stateSolverProof st $
     do let sym = st^.stateSymInterface
        gv <- readIORef gvRef
        case lookupGlobal gv (st ^. stateGlobals) of
          Nothing -> panic "bounded recursion" ["global not defined!"]
          Just [] -> panic "bounded recursion" ["empty stack!"]
          Just (x:xs) ->
            do mb <- getRecursionBound h
               let v = 1 + fromMaybe 0 (Map.lookup h x)
               case mb of
                 Just b | v > b ->
                   do loc <- getCurrentProgramLoc sym
                      let msg = ("reached maximum number of recursive calls to function " ++ show h ++ " (" ++ show b ++ ")")
                      let err = SimError loc (ResourceExhausted msg)
                      when generateSideConditions (addProofObligation sym (LabeledPred (falsePred sym) err))
                      return (ExecutionFeatureNewState (AbortState (AssumedFalse (AssumingNoError err)) st))
                 _ ->
                   do let x'  = Map.insert h v x
                      let st' = st & stateGlobals %~ insertGlobal gv (rebuildStack x' x xs)
                      x' `seq` return (ExecutionFeatureModifiedState (mkSt st'))

 onStep ::
   IORef BoundedRecursionGlobal ->
   ExecState p sym ext rtp ->
   IO (ExecutionFeatureResult p sym ext rtp)

 onStep gvRef = \case

   InitialState simctx globals ah ret cont ->
     do let halloc = simHandleAllocator simctx
        gv <- freshGlobalVar halloc (Text.pack "BoundedRecursionData") knownRepr
        writeIORef gvRef gv
        let simctx'  = simctx{ ctxIntrinsicTypes = MapF.insert
                                   (knownSymbol @"BoundedRecursionData")
                                   IntrinsicMuxFn
                                   (ctxIntrinsicTypes simctx) }
        let globals' = insertGlobal gv [mempty] globals
        return (ExecutionFeatureModifiedState (InitialState simctx' globals' ah ret cont))

   CallState rh call st ->
     pushFrame gvRef (\a b xs -> a:b:xs) (resolvedCallHandle call) (CallState rh call) st

   TailCallState vfv call st ->
     pushFrame gvRef (\a _ xs -> a:xs) (resolvedCallHandle call) (TailCallState vfv call) st

   ReturnState nm vfv pr st ->
     popFrame gvRef (ReturnState nm vfv pr) st

   UnwindCallState vfv ar st ->
     popFrame gvRef (UnwindCallState vfv ar) st

   _ -> return ExecutionFeatureNoChange