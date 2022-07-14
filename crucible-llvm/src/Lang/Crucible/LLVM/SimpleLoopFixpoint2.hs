------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.SimpleLoopFixpoint
-- Description      : Execution feature to compute loop fixpoint
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


module Lang.Crucible.LLVM.SimpleLoopFixpoint2
  ( FixpointEntry(..)
  , simpleLoopFixpoint
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Either
import           Data.Foldable
import qualified Data.IntMap as IntMap
import           Data.IORef
import qualified Data.List as List
import           Data.Maybe
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import qualified System.IO
import           Numeric.Natural

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map (MapF)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC

import qualified What4.Config as W4
import qualified What4.Interface as W4

import qualified Lang.Crucible.Analysis.Fixpoint.Components as C
import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.Panic as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Operations as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator as C

import qualified Lang.Crucible.LLVM.Bytes as C
import qualified Lang.Crucible.LLVM.DataLayout as C
import qualified Lang.Crucible.LLVM.MemModel as C
import qualified Lang.Crucible.LLVM.MemModel.MemLog as C hiding (Mem)
import qualified Lang.Crucible.LLVM.MemModel.Pointer as C
import qualified Lang.Crucible.LLVM.MemModel.Type as C


-- | When live loop-carried dependencies are discovered as we traverse
--   a loop body, new "widening" variables are introduced to stand in
--   for those locations.  When we introduce such a varible, we
--   capture what value the variable had when we entered the loop (the
--   \"header\" value); this is essentially the initial value of the
--   variable.  We also compute what value the variable should take on
--   its next iteration assuming the loop doesn't exit and executes
--   along its backedge.  This \"body\" value will be computed in
--   terms of the the set of all discovered live variables so far.
--   We know we have reached fixpoint when we don't need to introduce
--   and more fresh widening variables, and the body values for each
--   variable are stable across iterations.
data FixpointEntry sym tp = FixpointEntry
  { headerValue :: W4.SymExpr sym tp
  , bodyValue :: W4.SymExpr sym tp
  }

instance OrdF (W4.SymExpr sym) => OrdF (FixpointEntry sym) where
  compareF x y = case compareF (headerValue x) (headerValue y) of
    LTF -> LTF
    EQF -> compareF (bodyValue x) (bodyValue y)
    GTF -> GTF

instance OrdF (FixpointEntry sym) => W4.TestEquality (FixpointEntry sym) where
  testEquality x y = case compareF x y of
    EQF -> Just Refl
    _ -> Nothing

data MemFixpointEntry sym = forall w . (1 <= w) => MemFixpointEntry
  { memFixpointEntrySym :: sym
  , memFixpointEntryJoinVariable :: W4.SymBV sym w
  }

-- | This datatype captures the state machine that progresses as we
--   attempt to compute a loop invariant for a simple structured loop.
data FixpointState p sym ext rtp blocks
    -- | We have not yet encoundered the loop head
  = BeforeFixpoint

    -- | We have encountered the loop head at least once, and are in the process
    --   of converging to an inductive representation of the live variables
    --   in the loop.
  | ComputeFixpoint (FixpointRecord p sym ext rtp blocks)

    -- | We have found an inductively-strong representation of the live variables
    --   of the loop, and have discovered the loop index structure controling the
    --   execution of the loop. We are now executing the loop once more to compute
    --   verification conditions for executions that reamain in the loop.
  | CheckFixpoint (FixpointRecord p sym ext rtp blocks)


type ArrayTp = W4.BaseArrayType (C.EmptyCtx C.::> W4.BaseBVType 64) (W4.BaseBVType 8)

-- | Data about the loop that we incrementally compute as we approach fixpoint.
data FixpointRecord p sym ext rtp blocks = forall args r.
  FixpointRecord
  {
    -- | Block identifier of the head of the loop
    fixpointBlockId :: C.BlockID blocks args

    -- | identifier for the currently-active assumption frame related to this fixpoint computation
  , fixpointAssumptionFrameIdentifier :: C.FrameIdentifier

    -- | Map from introduced widening variables to prestate value before the loop starts,
    --   and to the value computed in a single loop iteration, assuming we return to the
    --   loop header. These variables may appear only in either registers or memory.
  , fixpointSubstitution :: MapF (W4.SymExpr sym) (FixpointEntry sym)

  , fixpointMemSubstitution :: MemorySubstitution sym

    -- | Prestate values of the Crucible registers when the loop header is first encountered.
  , fixpointRegMap :: C.RegMap sym args

  , fixpointInitialSimState :: C.SimState p sym ext rtp (C.CrucibleLang blocks r) ('Just args)

  , fixpointImplicitParams :: [Some (W4.SymExpr sym)]
  }


data MemorySubstitution sym =
  MemSubst
  { -- | Triples are (blockId, offset, size) to
    --    bitvector-typed entries ( bitvector only/not pointers )
    regularMemSubst :: Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType)

    -- | Map from block numbers to SMT Array join variables
  , arrayMemSubst :: Map Natural (W4.SymExpr sym ArrayTp, W4.SymBV sym 64)
  }

fixpointRecord ::
  FixpointState p sym ext rtp blocks ->
  Maybe (FixpointRecord p sym ext rtp blocks)
fixpointRecord BeforeFixpoint = Nothing
fixpointRecord (ComputeFixpoint r) = Just r
fixpointRecord (CheckFixpoint r) = Just r


type FixpointMonad sym =
  StateT (MapF (W4.SymExpr sym) (FixpointEntry sym)) IO


joinRegEntries ::
  (?logMessage :: String -> IO (), C.IsSymInterface sym) =>
  sym ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  FixpointMonad sym (Ctx.Assignment (C.RegEntry sym) ctx)
joinRegEntries sym = Ctx.zipWithM (joinRegEntry sym)

joinRegEntry ::
  (?logMessage :: String -> IO (), C.IsSymInterface sym) =>
  sym ->
  C.RegEntry sym tp ->
  C.RegEntry sym tp ->
  FixpointMonad sym (C.RegEntry sym tp)
joinRegEntry sym left right = case C.regType left of
  C.LLVMPointerRepr w

      -- special handling for "don't care" registers coming from Macaw
    | List.isPrefixOf "cmacaw_reg" (show $ W4.printSymNat $ C.llvmPointerBlock (C.regValue left))
    , List.isPrefixOf "cmacaw_reg" (show $ W4.printSymExpr $ C.llvmPointerOffset (C.regValue left)) -> do
      liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: cmacaw_reg"
      return left

    | C.llvmPointerBlock (C.regValue left) == C.llvmPointerBlock (C.regValue right) -> do
      liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr"
      subst <- get
      if isJust (W4.testEquality (C.llvmPointerOffset (C.regValue left)) (C.llvmPointerOffset (C.regValue right)))
      then do
        liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: left == right"
        return left
      else case MapF.lookup (C.llvmPointerOffset (C.regValue left)) subst of
        Just join_entry -> do
          -- liftIO $ ?logMessage $
          --   "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: Just: "
          --   ++ show (W4.printSymExpr $ bodyValue join_entry)
          --   ++ " -> "
          --   ++ show (W4.printSymExpr $ C.llvmPointerOffset (C.regValue right))
          put $ MapF.insert
            (C.llvmPointerOffset (C.regValue left))
            (join_entry { bodyValue = C.llvmPointerOffset (C.regValue right) })
            subst
          return left
        Nothing -> do
          liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: Nothing"
          join_varaible <- liftIO $ W4.freshConstant sym (userSymbol' "reg_join_var") (W4.BaseBVRepr w)
          let join_entry = FixpointEntry
                { headerValue = C.llvmPointerOffset (C.regValue left)
                , bodyValue = C.llvmPointerOffset (C.regValue right)
                }
          put $ MapF.insert join_varaible join_entry subst
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer (C.llvmPointerBlock (C.regValue left)) join_varaible
    | otherwise ->
      fail $
        "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: unsupported pointer base join: "
        ++ show (C.ppPtr $ C.regValue left)
        ++ " \\/ "
        ++ show (C.ppPtr $ C.regValue right)

  C.BoolRepr
    | List.isPrefixOf "cmacaw" (show $ W4.printSymExpr $ C.regValue left) -> do
      liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: cmacaw_reg"
      return left
    | otherwise -> do
      -- liftIO $ ?logMessage $
      --   "SimpleLoopFixpoint.joinRegEntry: BoolRepr:"
      --   ++ show (W4.printSymExpr $ C.regValue left)
      --   ++ " \\/ "
      --   ++ show (W4.printSymExpr $ C.regValue right)
      join_varaible <- liftIO $ W4.freshConstant sym (userSymbol' "macaw_reg") W4.BaseBoolRepr
      return $ C.RegEntry C.BoolRepr join_varaible

  C.StructRepr field_types -> do
    liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: StructRepr"
    C.RegEntry (C.regType left) <$> fmapFC (C.RV . C.regValue) <$> joinRegEntries sym
      (Ctx.generate (Ctx.size field_types) $ \i ->
        C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue left) Ctx.! i)
      (Ctx.generate (Ctx.size field_types) $ \i ->
        C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue right) Ctx.! i)
  _ -> fail $ "SimpleLoopFixpoint.joinRegEntry: unsupported type: " ++ show (C.regType left)


applySubstitutionRegEntries ::
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  Ctx.Assignment (C.RegEntry sym) ctx
applySubstitutionRegEntries sym substitution = fmapFC (applySubstitutionRegEntry sym substitution)

applySubstitutionRegEntry ::
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  C.RegEntry sym tp ->
  C.RegEntry sym tp
applySubstitutionRegEntry sym substitution entry = case C.regType entry of
  C.LLVMPointerRepr{} ->
    entry
      { C.regValue = C.LLVMPointer
          (C.llvmPointerBlock (C.regValue entry))
          (MapF.findWithDefault
            (C.llvmPointerOffset (C.regValue entry))
            (C.llvmPointerOffset (C.regValue entry))
            substitution)
      }
  C.BoolRepr ->
    entry
  C.StructRepr field_types ->
    entry
      { C.regValue = fmapFC (C.RV . C.regValue) $
          applySubstitutionRegEntries sym substitution $
          Ctx.generate (Ctx.size field_types) $
          \i -> C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue entry) Ctx.! i
      }
  _ -> C.panic "SimpleLoopFixpoint.applySubstitutionRegEntry" ["unsupported type: " ++ show (C.regType entry)]


loadMemJoinVariables ::
  (C.IsSymBackend sym bak, C.HasPtrWidth 64, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  bak ->
  C.MemImpl sym ->
  MemorySubstitution sym ->
  IO (MapF (W4.SymExpr sym) (W4.SymExpr sym))
loadMemJoinVariables bak mem (MemSubst subst smt_array_subst) = do
  let sym = C.backendGetSym bak

  -- read the "regular" memory regions
  regularVars <- mapM
    (\((blk, off, _sz), (MemFixpointEntry { memFixpointEntryJoinVariable = join_varaible }, storeage_type)) -> do
      ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral off)
      val <- C.doLoad bak mem ptr storeage_type (C.LLVMPointerRepr $ W4.bvWidth join_varaible) C.noAlignment
      case W4.asNat (C.llvmPointerBlock val) of
        Just 0 -> return $ MapF.Pair join_varaible $ C.llvmPointerOffset val
        _ -> fail $ "SimpleLoopFixpoint.loadMemJoinVariables: unexpected val:" ++ show (C.ppPtr val))
    (Map.toAscList subst)

  -- read the "SMT array" memory regions
  arrayVars <- mapM
    (\ (blk, (arr_var, _len) ) ->
      do base_ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 0)
         res <- C.asMemAllocationArrayStore sym ?ptrWidth base_ptr (C.memImplHeap mem)
         case res of
           Nothing -> fail $ "Expected SMT array in memory image for block number: " ++ show blk
           Just (_ok, arr, _len2) ->
             -- TODO: we need to assert the load condition...
             -- TODO? Should we assert the lengths match?
             return (MapF.Pair arr_var arr)
    )
    (Map.toAscList smt_array_subst)

  return (MapF.fromList (regularVars ++ arrayVars))


storeMemJoinVariables ::
  (C.IsSymBackend sym bak, C.HasPtrWidth 64, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  bak ->
  C.MemImpl sym ->
  MemorySubstitution sym ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  IO (C.MemImpl sym)
storeMemJoinVariables bak mem (MemSubst mem_subst smt_array_subst) eq_subst = do
  let sym = C.backendGetSym bak

  -- write the "regular" memory regions
  mem1 <- foldlM
     (\mem_acc ((blk, off, _sz), (MemFixpointEntry { memFixpointEntryJoinVariable = join_varaible }, storeage_type)) -> do
       ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral off)
       C.doStore bak mem_acc ptr (C.LLVMPointerRepr $ W4.bvWidth join_varaible) storeage_type C.noAlignment =<<
         C.llvmPointer_bv sym (MapF.findWithDefault join_varaible join_varaible eq_subst))
     mem
     (Map.toAscList mem_subst)

  -- write the "SMT array" memory regions
  mem2 <- foldlM
     (\mem_acc (blk, (arr, len)) ->
        do base_ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 0)
           C.doArrayStore bak mem_acc base_ptr C.noAlignment arr len)
     mem1
     (Map.toAscList smt_array_subst)

  return mem2

dropMemStackFrame :: C.IsSymInterface sym => C.MemImpl sym -> (C.MemImpl sym, C.MemAllocs sym, C.MemWrites sym)
dropMemStackFrame mem = case (C.memImplHeap mem) ^. C.memState of
  (C.StackFrame _ _ _ (a, w) s) -> ((mem { C.memImplHeap = (C.memImplHeap mem) & C.memState .~ s }), a, w)
  _ -> C.panic "SimpleLoopFixpoint.dropMemStackFrame" ["not a stack frame:", show (C.ppMem $ C.memImplHeap mem)]


filterSubstitution ::
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  MapF (W4.SymExpr sym) (FixpointEntry sym)
filterSubstitution sym substitution =
  -- TODO: fixpoint
  let uninterp_constants = foldMapF
        (Set.map (C.mapSome $ W4.varExpr sym) . W4.exprUninterpConstants sym . bodyValue)
        substitution
  in
  MapF.filterWithKey (\variable _entry -> Set.member (C.Some variable) uninterp_constants) substitution

-- find widening variables that are actually the same (up to syntactic equality)
-- and can be substituted for each other
uninterpretedConstantEqualitySubstitution ::
  forall sym .
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  (MapF (W4.SymExpr sym) (FixpointEntry sym), MapF (W4.SymExpr sym) (W4.SymExpr sym))
uninterpretedConstantEqualitySubstitution _sym substitution =
  let reverse_substitution = MapF.foldlWithKey'
        (\accumulator variable entry -> MapF.insert entry variable accumulator)
        MapF.empty
        substitution
      uninterpreted_constant_substitution = fmapF
        (\entry -> fromJust $ MapF.lookup entry reverse_substitution)
        substitution
      normal_substitution = MapF.filterWithKey
        (\variable _entry ->
          Just Refl == W4.testEquality variable (fromJust $ MapF.lookup variable uninterpreted_constant_substitution))
        substitution
  in
  (normal_substitution, uninterpreted_constant_substitution)


userSymbol' :: String -> W4.SolverSymbol
userSymbol' = fromRight (C.panic "SimpleLoopFixpoint.userSymbol'" []) . W4.userSymbol


-- | This execution feature is designed to allow a limited form of
--   verification for programs with unbounded looping structures.
--
--   It is currently highly experimental and has many limititations.
--   Most notibly, it only really works properly for functions
--   consiting of a single, non-nested loop with a single exit point.
--   Moreover, the loop must have an indexing variable that counts up
--   from a starting point by a fixed stride amount.
--
--   Currently, these assumptions about the loop strucutre are not
--   checked.
--
--   The basic use case here is for verifiying functions that loop
--   through an array of data of symbolic length.  This is done by
--   providing a \""fixpoint function\" which describes how the live
--   values in the loop at an arbitrary iteration are used to compute
--   the final values of those variables before execution leaves the
--   loop. The number and order of these variables depends on
--   internal details of the representation, so is relatively fragile.
simpleLoopFixpoint ::
  forall sym ext p rtp blocks init ret .
  (C.IsSymInterface sym, C.IsSyntaxExtension ext, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  C.CFG ext blocks init ret {- ^ The function we want to verify -} ->
  C.GlobalVar C.Mem {- ^ global variable representing memory -} ->
  ([Some (W4.SymExpr sym)] -> MapF (W4.SymExpr sym) (FixpointEntry sym) -> IO (W4.Pred sym)) ->
  IO (C.ExecutionFeature p sym ext rtp)
simpleLoopFixpoint sym cfg@C.CFG{..} mem_var loop_invariant = do
  let ?ptrWidth = knownNat @64

  --verbSetting <- W4.getOptionSetting W4.verbosity $ W4.getConfiguration sym
  --verb <- fromInteger <$> W4.getOpt verbSetting

  -- Doesn't really work if there are nested loops: looop datastructures will
  -- overwrite each other.  Currently no error message.

  -- Really only works for single-exit loops; need a message for that too.

  let flattenWTOComponent = \case
        C.SCC C.SCCData{..} ->  wtoHead : concatMap flattenWTOComponent wtoComps
        C.Vertex v -> [v]
  let loop_map = Map.fromList $ mapMaybe
        (\case
          C.SCC C.SCCData{..} -> Just (wtoHead, wtoHead : concatMap flattenWTOComponent wtoComps)
          C.Vertex{} -> Nothing)
        (C.cfgWeakTopologicalOrdering cfg)


  fixpoint_state_ref <- newIORef @(FixpointState p sym ext rtp blocks) BeforeFixpoint

  putStrLn "Setting up simple loop fixpoints feature."
  putStrLn ("Loop map: " ++ show loop_map)
  putStrLn ("WTO: " ++ show (C.cfgWeakTopologicalOrdering cfg))
  putStrLn (show (C.cfgHandle cfg))
  writeFile "bigcfg.txt" (show (C.ppCFG' True (C.postdomInfo cfg) cfg))

  return $ C.ExecutionFeature $ \exec_state -> do
    let ?logMessage = \msg -> do -- when (verb >= (3 :: Natural)) $ do
          let h = C.printHandle $ C.execStateContext exec_state
          System.IO.hPutStrLn h msg
          System.IO.hFlush h

    fixpoint_state <- readIORef fixpoint_state_ref
    C.withBackend (C.execStateContext exec_state) $ \bak ->
     case exec_state of
      C.RunningState (C.RunBlockStart block_id) sim_state
        | C.SomeHandle cfgHandle == C.frameHandle (sim_state ^. C.stateCrucibleFrame)

        -- make sure the types match
        , Just Refl <- W4.testEquality
            (fmapFC C.blockInputs cfgBlockMap)
            (fmapFC C.blockInputs $ C.frameBlockMap $ sim_state ^. C.stateCrucibleFrame)

          -- loop map is what we computed above, is this state at a loop header
        , Map.member (C.Some block_id) loop_map ->

            advanceFixpointState bak mem_var loop_invariant block_id sim_state fixpoint_state fixpoint_state_ref

        | otherwise -> do
            ?logMessage $ "SimpleLoopFixpoint: RunningState: RunBlockStart: " ++ show block_id ++ " " ++ show (C.frameHandle (sim_state ^. C.stateCrucibleFrame))
            return C.ExecutionFeatureNoChange

      -- TODO: maybe need to rework this, so that we are sure to capture even concrete exits from the loop.
      C.SymbolicBranchState branch_condition true_frame false_frame _target sim_state
          | Just fixpoint_record@FixpointRecord{ fixpointBlockId = fixpoint_block_id } <- fixpointRecord fixpoint_state
          , Just loop_body_some_block_ids <- Map.lookup (C.Some fixpoint_block_id) loop_map
          , JustPausedFrameTgtId true_frame_some_block_id <- pausedFrameTgtId true_frame
          , JustPausedFrameTgtId false_frame_some_block_id <- pausedFrameTgtId false_frame
          , C.SomeHandle cfgHandle == C.frameHandle (sim_state ^. C.stateCrucibleFrame)
          , Just Refl <- W4.testEquality
              (fmapFC C.blockInputs cfgBlockMap)
              (fmapFC C.blockInputs $ C.frameBlockMap $ sim_state ^. C.stateCrucibleFrame)
          , elem true_frame_some_block_id loop_body_some_block_ids /= elem false_frame_some_block_id loop_body_some_block_ids -> do

            (loop_condition, inside_loop_frame, outside_loop_frame) <-
              if elem true_frame_some_block_id loop_body_some_block_ids
              then
                return (branch_condition, true_frame, false_frame)
              else do
                not_branch_condition <- W4.notPred sym branch_condition
                return (not_branch_condition, false_frame, true_frame)

            case fixpoint_state of
              BeforeFixpoint -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint:" ["BeforeFixpoint"]

              ComputeFixpoint _fixpoint_record -> do
                -- continue in the loop
                ?logMessage $ "SimpleLoopFixpoint: SymbolicBranchState: ComputeFixpoint"

                loc <- W4.getCurrentProgramLoc sym
                C.addAssumption bak $ C.BranchCondition loc (C.pausedLoc inside_loop_frame) loop_condition
                
                C.ExecutionFeatureNewState <$>
                  runReaderT
                    (C.resumeFrame (C.forgetPostdomFrame inside_loop_frame) $ sim_state ^. (C.stateTree . C.actContext))
                    sim_state

              CheckFixpoint _fixpoint_record -> do
                ?logMessage $ "SimpleLoopFixpoint: SymbolicBranchState: CheckFixpoint"

                return C.ExecutionFeatureNoChange

      _ -> return C.ExecutionFeatureNoChange


advanceFixpointState ::
  forall sym bak ext p rtp blocks r args .
  (C.IsSymBackend sym bak, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions, ?logMessage :: String -> IO ()) =>
  bak ->
  C.GlobalVar C.Mem ->
  ([Some (W4.SymExpr sym)] -> MapF (W4.SymExpr sym) (FixpointEntry sym) -> IO (W4.Pred sym)) ->
  C.BlockID blocks args ->
  C.SimState p sym ext rtp (C.CrucibleLang blocks r) ('Just args) ->
  FixpointState p sym ext rtp blocks ->
  IORef (FixpointState p sym ext rtp blocks) ->
  IO (C.ExecutionFeatureResult p sym ext rtp)

advanceFixpointState bak mem_var loop_invariant block_id sim_state fixpoint_state fixpoint_state_ref =
  let ?ptrWidth = knownNat @64 in
  let sym = C.backendGetSym bak in
  case fixpoint_state of
    BeforeFixpoint -> do
      ?logMessage $ "SimpleLoopFixpoint: RunningState: BeforeFixpoint -> ComputeFixpoint " ++ show block_id
      assumption_frame_identifier <- C.pushAssumptionFrame bak
      let mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
      let res_mem_impl = mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" $ C.memImplHeap mem_impl }

      ?logMessage $ "SimpleLoopFixpoint: start memory\n" ++ (show (C.ppMem (C.memImplHeap mem_impl)))
          

      writeIORef fixpoint_state_ref $ ComputeFixpoint $
        FixpointRecord
        { fixpointBlockId = block_id
        , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
        , fixpointSubstitution = MapF.empty
        , fixpointRegMap = sim_state ^. (C.stateCrucibleFrame . C.frameRegs)
        , fixpointMemSubstitution = MemSubst Map.empty Map.empty
        , fixpointInitialSimState = sim_state
        , fixpointImplicitParams = []
        }
      return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
        sim_state & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

    ComputeFixpoint fixpoint_record
      | FixpointRecord { fixpointRegMap = reg_map
                       , fixpointInitialSimState = initSimState }
           <- fixpoint_record
      , Just Refl <- W4.testEquality
          (fmapFC C.regType $ C.regMap reg_map)
          (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do


        ?logMessage $ "SimpleLoopFixpoint: RunningState: ComputeFixpoint: " ++ show block_id
        _ <- C.popAssumptionFrameAndObligations bak $ fixpointAssumptionFrameIdentifier fixpoint_record

        loc <- W4.getCurrentProgramLoc sym

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
        let (header_mem_impl, mem_allocs, mem_writes) = dropMemStackFrame body_mem_impl
        when (C.sizeMemAllocs mem_allocs /= 0) $
          fail "SimpleLoopFixpoint: unsupported memory allocation in loop body."

        -- widen the inductive condition
        ((join_reg_map,mem_substitution), join_substitution) <- runStateT
          (do join_reg_map <- joinRegEntries sym
                                (C.regMap reg_map)
                                (C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs))
              mem_substitution <- computeMemSubstitution sym fixpoint_record mem_writes      
              return (join_reg_map, mem_substitution)
          )
          (fixpointSubstitution fixpoint_record)

        -- check if we are done; if we did not introduce any new variables, we don't have to widen any more
        if MapF.keys join_substitution == MapF.keys (fixpointSubstitution fixpoint_record)

          -- we found the fixpoint, get ready to wrap up
          then do
            ?logMessage $
              "SimpleLoopFixpoint: RunningState: ComputeFixpoint -> CheckFixpoint"

            -- we have delayed populating the main substituation map with
            --  memory variables, so we have to do that now

            header_mem_substitution <- loadMemJoinVariables bak header_mem_impl $
              fixpointMemSubstitution fixpoint_record
            body_mem_substitution <- loadMemJoinVariables bak body_mem_impl $
              fixpointMemSubstitution fixpoint_record

            -- try to unify widening variables that have the same values
            let (normal_substitution, equality_substitution) = uninterpretedConstantEqualitySubstitution sym $
                  -- drop variables that don't appear along some back edge (? understand this better)
                  filterSubstitution sym $
                  MapF.union join_substitution $
                  -- this implements zip, because the two maps have the same keys
                  MapF.intersectWithKeyMaybe
                    (\_k x y -> Just $ FixpointEntry{ headerValue = x, bodyValue = y })
                    header_mem_substitution
                    body_mem_substitution
            ?logMessage $ "normal_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList normal_substitution)
            ?logMessage $ "equality_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList equality_substitution)

            -- unify widening variables in the register subst
            let res_reg_map = applySubstitutionRegEntries sym equality_substitution join_reg_map

            -- unify widening variables in the memory subst
            res_mem_impl <- storeMemJoinVariables
              bak
              header_mem_impl
              mem_substitution
              equality_substitution

            -- == compute the list of "implicit parameters" that are relevant ==
            let implicit_params = Set.toList $
                  Set.difference
                    (foldMap
                       (\ (MapF.Pair _ e) ->
                            Set.map (\ (C.Some x) -> C.Some (W4.varExpr sym x))
                              (W4.exprUninterpConstants sym (bodyValue e)))
                       (MapF.toList normal_substitution))
                    (Set.fromList (MapF.keys normal_substitution))

            -- == assert the loop invariant on the initial values ==

            -- build a map where the current value is equal to the initial value
            let init_state_map = MapF.map (\e -> e{ bodyValue = headerValue e }) normal_substitution
            -- construct the loop invariant
            initial_loop_invariant <- loop_invariant implicit_params init_state_map
            -- assert the loop invariant as an obligation
            C.addProofObligation bak
               $ C.LabeledPred initial_loop_invariant
               $ C.SimError loc "initial loop invariant"

            -- == assume the loop invariant on the arbitrary state ==

            -- build a map where the current value is equal to the widening variable
            let hyp_state_map = MapF.mapWithKey (\k e -> e{ bodyValue = k }) normal_substitution
            -- construct the loop invariant to assume at the loop head
            hypothetical_loop_invariant <- loop_invariant implicit_params hyp_state_map
            -- assume the loop invariant
            C.addAssumption bak
              $ C.GenericAssumption loc "loop head invariant"
                hypothetical_loop_invariant

            -- == set up the state with arbitrary values to run the loop body ==
            
            writeIORef fixpoint_state_ref $
              CheckFixpoint
                FixpointRecord
                { fixpointBlockId = block_id
                , fixpointAssumptionFrameIdentifier = undefined --assumption_frame_identifier
                , fixpointSubstitution = normal_substitution
                , fixpointRegMap = C.RegMap res_reg_map
                , fixpointMemSubstitution = mem_substitution
                , fixpointInitialSimState = initSimState
                , fixpointImplicitParams = implicit_params
                }

            -- Continue running from the loop header starting from an arbitrary state satisfying
            -- the loop invariant.
            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              initSimState & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap res_reg_map
                & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

          else do
            -- Otherwise, we are still working on finding all the loop-carried dependencies
            ?logMessage $
              "SimpleLoopFixpoint: RunningState: ComputeFixpoint: -> ComputeFixpoint"
            assumption_frame_identifier <- C.pushAssumptionFrame bak

            -- write any new widening variables into memory state
            res_mem_impl <- storeMemJoinVariables bak
              (header_mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" (C.memImplHeap header_mem_impl) })
              mem_substitution
              MapF.empty

            writeIORef fixpoint_state_ref $ ComputeFixpoint
              FixpointRecord
              { fixpointBlockId = block_id
              , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
              , fixpointSubstitution = join_substitution
              , fixpointRegMap = C.RegMap join_reg_map
              , fixpointMemSubstitution = mem_substitution
              , fixpointInitialSimState = initSimState
              , fixpointImplicitParams = []
              }
            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              initSimState & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap join_reg_map
                & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

      | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: ComputeFixpoint"]

    CheckFixpoint fixpoint_record
      | FixpointRecord { fixpointRegMap = reg_map } <- fixpoint_record
      , Just Refl <- W4.testEquality
          (fmapFC C.regType $ C.regMap reg_map)
          (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do
        ?logMessage $
          "SimpleLoopFixpoint: RunningState: "
          ++ "CheckFixpoint"
          ++ " -> "
          ++ "AfterFixpoint"
          ++ ": "
          ++ show block_id

        loc <- W4.getCurrentProgramLoc sym

        -- == assert the loop invariant and abort ==

        -- should we/do we need to pop this frame?
        -- _ <- C.popAssumptionFrame bak $ fixpointAssumptionFrameIdentifier fixpoint_record

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
        let (header_mem_impl, _mem_allocs, _mem_writes) = dropMemStackFrame body_mem_impl

        body_mem_substitution <- loadMemJoinVariables bak body_mem_impl $ fixpointMemSubstitution fixpoint_record
        let res_substitution = MapF.mapWithKey
              (\variable fixpoint_entry ->
                fixpoint_entry
                  { bodyValue = MapF.findWithDefault (bodyValue fixpoint_entry) variable body_mem_substitution
                  })
              (fixpointSubstitution fixpoint_record)
        -- ?logMessage $ "res_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList res_substitution)

        invariant_pred <- loop_invariant (fixpointImplicitParams fixpoint_record) res_substitution
        C.addProofObligation bak $ C.LabeledPred invariant_pred $ C.SimError loc "loop invariant"
        -- ?logMessage $ "fixpoint_func_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList fixpoint_func_substitution)
        return $ C.ExecutionFeatureModifiedState $ C.AbortState (C.InfeasibleBranch loc) sim_state

      | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: CheckFixpoint"]



computeMemSubstitution ::
  (?logMessage :: String -> IO (), C.IsSymInterface sym) =>
  C.IsSymInterface sym =>
  sym ->
  FixpointRecord p sym ext rtp blocks ->
  C.MemWrites sym ->
  FixpointMonad sym (MemorySubstitution sym)
computeMemSubstitution sym fixpoint_record mem_writes =
 let ?ptrWidth = knownNat @64 in
 do -- widen the memory
    mem_substitution_candidate <- Map.fromList <$> catMaybes <$> case mem_writes of
      C.MemWrites [C.MemWritesChunkIndexed mmm] -> mapM
        (\case

          -- TODO, case for MemArrayStore...
          (C.MemWrite ptr (C.MemArrayStore _arr (Just len)))
            | Just _blk <- W4.asNat (C.llvmPointerBlock ptr)
            , Just Refl <- testEquality (knownNat @64) (W4.bvWidth len)
            -> do -- NB, array store cases are handled separately below
                  return Nothing

          (C.MemWrite ptr (C.MemStore _ storeage_type _))
            | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
            , Just off <- BV.asNatural <$> W4.asBV (C.llvmPointerOffset ptr) -> do
              let sz = C.typeEnd 0 storeage_type
              some_join_variable <- liftIO $ case W4.mkNatRepr $ C.bytesToBits sz of
                C.Some bv_width
                  | Just C.LeqProof <- W4.testLeq (W4.knownNat @1) bv_width -> do
                    join_variable <- W4.freshConstant sym
                      (userSymbol' "mem_join_var")
                      (W4.BaseBVRepr bv_width)
                    return $ MemFixpointEntry
                      { memFixpointEntrySym = sym
                      , memFixpointEntryJoinVariable = join_variable
                      }
                  | otherwise ->
                    C.panic
                      "SimpleLoopFixpoint.simpleLoopFixpoint"
                      ["unexpected storage type " ++ show storeage_type ++ " of size " ++ show sz]
              return $ Just ((blk, off, fromIntegral sz), (some_join_variable, storeage_type))

            | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
            , Just Refl <- W4.testEquality ?ptrWidth (C.ptrWidth ptr) -> do
                liftIO (?logMessage ("Discarding write via symbolic pointer: " ++ (show blk)))
                liftIO (?logMessage (show (W4.printSymExpr (C.llvmPointerOffset ptr))))
                return Nothing
{-
              maybe_ranges <- runMaybeT $
                C.writeRangesMem @_ @64 sym $ C.memImplHeap header_mem_impl
              case maybe_ranges of
                Just ranges -> do
                  sz <- W4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth $ toInteger $ C.typeEnd 0 storeage_type
                  forM_ (Map.findWithDefault [] blk ranges) $ \(prev_off, prev_sz) -> do
                    disjoint_pred <- C.buildDisjointRegionsAssertionWithSub
                      sym
                      ptr
                      sz
                      (C.LLVMPointer (C.llvmPointerBlock ptr) prev_off)
                      prev_sz
                    when (W4.asConstantPred disjoint_pred /= Just True) $
                      fail $
                        "SimpleLoopFixpoint: non-disjoint ranges: off1="
                        ++ show (W4.printSymExpr (C.llvmPointerOffset ptr))
                        ++ ", sz1="
                        ++ show (W4.printSymExpr sz)
                        ++ ", off2="
                        ++ show (W4.printSymExpr prev_off)
                        ++ ", sz2="
                        ++ show (W4.printSymExpr prev_sz)
                  return Nothing
                Nothing -> fail $ "SimpleLoopFixpoint: unsupported symbolic pointers"
-}

          w -> fail $ "SimpleLoopFixpoint: not MemWrite: " ++ show (C.ppWrite w))
        (List.concat $ IntMap.elems mmm)
      _ -> fail $ "SimpleLoopFixpoint: not MemWritesChunkIndexed: " ++ show (C.ppMemWrites mem_writes)

    array_mem_substitution_candidate <- Map.fromList <$> catMaybes <$> case mem_writes of
      C.MemWrites [C.MemWritesChunkIndexed mmm] -> mapM
        (\case

          (C.MemWrite ptr (C.MemArrayStore _arr (Just len)))
            | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
            , Just Refl <- testEquality (knownNat @64) (W4.bvWidth len)
            -> case Map.lookup blk (arrayMemSubst (fixpointMemSubstitution fixpoint_record)) of
                 Just join_var -> return (Just (blk, join_var))
                 Nothing ->
                   do join_var <- liftIO $
                          W4.freshConstant sym
                            (userSymbol' ("smt_array_join_var_" ++ show blk))
                            knownRepr
                      return (Just (blk, (join_var, len)))

          _ -> return Nothing)
        (List.concat $ IntMap.elems mmm)
      _ -> fail $ "SimpleLoopFixpoint: not MemWritesChunkIndexed: " ++ show (C.ppMemWrites mem_writes)

    -- check that the mem substitution always computes the same footprint on every iteration (!?!)
    regular_mem_substitution <- if Map.null (regularMemSubst (fixpointMemSubstitution fixpoint_record))
      then return mem_substitution_candidate
      else if Map.keys mem_substitution_candidate == Map.keys (regularMemSubst (fixpointMemSubstitution fixpoint_record))
        then return $ regularMemSubst (fixpointMemSubstitution fixpoint_record)
        else fail "SimpleLoopFixpoint: unsupported memory writes change"

    -- check that the array mem substitution always computes the same footprint (!?!)
    array_mem_substitution <- if Map.null (arrayMemSubst (fixpointMemSubstitution fixpoint_record))
      then return array_mem_substitution_candidate
      else if Map.keys array_mem_substitution_candidate == Map.keys (arrayMemSubst (fixpointMemSubstitution fixpoint_record))
        then return $ arrayMemSubst (fixpointMemSubstitution fixpoint_record)
        else fail "SimpleLoopFixpoint: unsupported SMT array memory writes change"

    return (MemSubst regular_mem_substitution array_mem_substitution)


data MaybePausedFrameTgtId f where
  JustPausedFrameTgtId :: C.Some (C.BlockID b) -> MaybePausedFrameTgtId (C.CrucibleLang b r)
  NothingPausedFrameTgtId :: MaybePausedFrameTgtId f

pausedFrameTgtId :: C.PausedFrame p sym ext rtp f -> MaybePausedFrameTgtId f
pausedFrameTgtId C.PausedFrame{ resume = resume } = case resume of
  C.ContinueResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  C.CheckMergeResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  _ -> NothingPausedFrameTgtId
