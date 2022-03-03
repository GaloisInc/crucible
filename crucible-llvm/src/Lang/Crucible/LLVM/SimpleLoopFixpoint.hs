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


module Lang.Crucible.LLVM.SimpleLoopFixpoint
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
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
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


data FixpointStatus = BeforeFixpoint | ComputeFixpoint | CheckFixpoint | AfterFixpoint
  deriving (Eq, Ord, Show)

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

instance W4.TestEquality (FixpointEntry sym) => C.EqF (FixpointEntry sym) where
  eqF x y = isJust $ W4.testEquality x y

data MemFixpointEntry sym = forall w . (1 <= w) => MemFixpointEntry
  { memFixpointEntrySym :: sym
  , memFixpointEntryJoinVariable :: W4.SymBV sym w
  }

instance W4.TestEquality (W4.SymExpr sym) => Eq (MemFixpointEntry sym) where
  (MemFixpointEntry _ x_join_variable) == (MemFixpointEntry _ y_join_variable)
    | Just Refl <- W4.testEquality x_join_variable y_join_variable =
      True
    | otherwise = False

data FixpointStuff sym blocks = forall args . FixpointStuff
  { fixpointStatus :: FixpointStatus
  , fixpointBlockId :: C.Some (C.BlockID blocks)
  , fixpointAssumptionFrameIdentifier :: C.FrameIdentifier

    -- map from variables to prestate value before the loop starts, and to the value computed in a single iteration
    -- these variables may appear only in either registers or memory
  , fixpointSubstitution :: MapF (W4.SymExpr sym) (FixpointEntry sym)

    -- prestate values
  , fixpointRegMap :: C.RegMap sym args

    -- triples are (blockId, offset, size) to bitvector-typed entries ( bitvector only (not pointers) )
  , fixpointMemSubstitution :: Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType)

    -- condition which, when true, stays in the loop
    -- updated as you widen the invariant
  , fixpointLoopCondition :: W4.Pred sym

    -- data about the fixed sort of loop index values we are trying to find
  , fixpointLoopIndexBound :: LoopIndexBound sym
  }

type FixpointMonad sym = StateT (MapF (W4.SymExpr sym) (FixpointEntry sym)) IO


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
          liftIO $ ?logMessage $
            "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: Just: "
            ++ show (W4.printSymExpr $ bodyValue join_entry)
            ++ " -> "
            ++ show (W4.printSymExpr $ C.llvmPointerOffset (C.regValue right))
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
      liftIO $ ?logMessage $
        "SimpleLoopFixpoint.joinRegEntry: BoolRepr:"
        ++ show (W4.printSymExpr $ C.regValue left)
        ++ " \\/ "
        ++ show (W4.printSymExpr $ C.regValue right)
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


findLoopIndex ::
  (?logMessage :: String -> IO (), C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  IO (W4.SymBV sym wptr, Natural, Natural)
findLoopIndex sym substitution = do
  candidates <- catMaybes <$> mapM
    (\(MapF.Pair variable FixpointEntry{..}) -> case W4.testEquality (W4.BaseBVRepr ?ptrWidth) (W4.exprType variable) of
      Just Refl -> do
        diff <- liftIO $ W4.bvSub sym bodyValue variable
        case (BV.asNatural <$> W4.asBV headerValue, BV.asNatural <$> W4.asBV diff) of
          (Just start, Just step) -> do
            liftIO $ ?logMessage $
              "SimpleLoopFixpoint.findLoopIndex: " ++ show (W4.printSymExpr variable) ++ "=" ++ show (start, step)
            return $ Just (variable, start, step)
          _ -> return Nothing
      Nothing -> return Nothing)
    (MapF.toList substitution)
  case candidates of
    [candidate] -> return candidate
    _ -> fail "SimpleLoopFixpoint.findLoopIndex: loop index identification failure."

findLoopBound ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  W4.Pred sym ->
  Natural ->
  Natural ->
  IO (W4.SymBV sym wptr)
findLoopBound sym condition _start step =
  case Set.toList $ W4.exprUninterpConstants sym condition of

    -- this is a grungy hack, we are expecting exactly three variables and take the first
    [C.Some loop_stop, _, _]
      | Just Refl <- W4.testEquality (W4.BaseBVRepr ?ptrWidth) (W4.exprType $ W4.varExpr sym loop_stop) ->
        W4.bvMul sym (W4.varExpr sym loop_stop) =<< W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral step)
    _ -> fail "SimpleLoopFixpoint.findLoopBound: loop bound identification failure."


-- index variable information for fixed stride, bounded loops
data LoopIndexBound sym = forall w . 1 <= w => LoopIndexBound
  { index :: W4.SymBV sym w
  , start :: Natural
  , stop :: W4.SymBV sym w
  , step :: Natural
  }

findLoopIndexBound ::
  (?logMessage :: String -> IO (), C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  W4.Pred sym ->
  IO (LoopIndexBound sym)
findLoopIndexBound sym substitution condition = do
  (loop_index, start, step) <- findLoopIndex sym substitution
  stop <- findLoopBound sym condition start step
  return $ LoopIndexBound
    { index = loop_index
    , start = start
    , stop = stop
    , step = step
    }

-- hard-coded here that we are always looking for a loop condition delimited by an unsigned comparison
loopIndexBoundCondition ::
  (C.IsSymInterface sym, 1 <= w) =>
  sym ->
  W4.SymBV sym w ->
  W4.SymBV sym w ->
  IO (W4.Pred sym)
loopIndexBoundCondition = W4.bvUlt

loopIndexStartStepCondition ::
  C.IsSymInterface sym =>
  sym ->
  LoopIndexBound sym ->
  IO (W4.Pred sym)
loopIndexStartStepCondition sym LoopIndexBound{ index = loop_index, start = start, step = step } = do
  start_bv <- W4.bvLit sym (W4.bvWidth loop_index) (BV.mkBV (W4.bvWidth loop_index) $ fromIntegral start)
  step_bv <- W4.bvLit sym (W4.bvWidth loop_index) (BV.mkBV (W4.bvWidth loop_index) $ fromIntegral step)
  W4.bvEq sym start_bv =<< W4.bvUrem sym loop_index step_bv


loadMemJoinVariables ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  C.MemImpl sym ->
  Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType) ->
  IO (MapF (W4.SymExpr sym) (W4.SymExpr sym))
loadMemJoinVariables sym mem subst = MapF.fromList <$> mapM
  (\((blk, off, _sz), (MemFixpointEntry { memFixpointEntryJoinVariable = join_varaible }, storeage_type)) -> do
    ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral off)
    val <- C.doLoad sym mem ptr storeage_type (C.LLVMPointerRepr $ W4.bvWidth join_varaible) C.noAlignment
    case W4.asNat (C.llvmPointerBlock val) of
      Just 0 -> return $ MapF.Pair join_varaible $ C.llvmPointerOffset val
      _ -> fail $ "SimpleLoopFixpoint.loadMemJoinVariables: unexpected val:" ++ show (C.ppPtr val))
  (Map.toAscList subst)

storeMemJoinVariables ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr, C.HasLLVMAnn sym) =>
  sym ->
  C.MemImpl sym ->
  Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType) ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  IO (C.MemImpl sym)
storeMemJoinVariables sym mem mem_subst eq_subst = foldlM
  (\mem_acc ((blk, off, _sz), (MemFixpointEntry { memFixpointEntryJoinVariable = join_varaible }, storeage_type)) -> do
    ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral off)
    C.doStore sym mem_acc ptr (C.LLVMPointerRepr $ W4.bvWidth join_varaible) storeage_type C.noAlignment =<<
      C.llvmPointer_bv sym (MapF.findWithDefault join_varaible join_varaible eq_subst))
  mem
  (Map.toAscList mem_subst)

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


simpleLoopFixpoint ::
  forall sym ext p rtp blocks init ret .
  (C.IsSymInterface sym, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  C.CFG ext blocks init ret ->
  C.GlobalVar C.Mem ->
  (MapF (W4.SymExpr sym) (FixpointEntry sym) -> W4.Pred sym -> IO (MapF (W4.SymExpr sym) (W4.SymExpr sym), W4.Pred sym)) ->
  IO (C.ExecutionFeature p sym ext rtp)
simpleLoopFixpoint sym cfg@C.CFG{..} mem_var fixpoint_func = do
  let ?ptrWidth = knownNat @64

  verbSetting <- W4.getOptionSetting W4.verbosity $ W4.getConfiguration sym
  verb <- fromInteger <$> W4.getOpt verbSetting

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

  fixpoint_stuff_ref <- newIORef @(FixpointStuff sym blocks) $ FixpointStuff
    { fixpointStatus = BeforeFixpoint
    , fixpointBlockId = undefined
    , fixpointAssumptionFrameIdentifier = undefined
    , fixpointSubstitution = undefined
    , fixpointRegMap = undefined
    , fixpointMemSubstitution = undefined
    , fixpointLoopCondition = undefined
    , fixpointLoopIndexBound = undefined
    }

  return $ C.ExecutionFeature $ \exec_state -> do
    let ?logMessage = \msg -> when (verb >= (3 :: Natural)) $ do
          let h = C.printHandle $ C.execStateContext exec_state
          System.IO.hPutStrLn h msg
          System.IO.hFlush h
    fixpoint_stuff <- readIORef fixpoint_stuff_ref
    case exec_state of
      C.RunningState (C.RunBlockStart block_id) sim_state

        | C.SomeHandle cfgHandle == C.frameHandle (sim_state ^. C.stateCrucibleFrame)

        -- make sure the types match
        , Just Refl <- W4.testEquality
            (fmapFC C.blockInputs cfgBlockMap)
            (fmapFC C.blockInputs $ C.frameBlockMap $ sim_state ^. C.stateCrucibleFrame)

          -- loop map is what we computed above, is this state at a loop header
        , Map.member (C.Some block_id) loop_map -> case fixpointStatus fixpoint_stuff of

          BeforeFixpoint -> do
            ?logMessage $ "SimpleLoopFixpoint: RunningState: " ++ show BeforeFixpoint ++ " -> " ++ show ComputeFixpoint
            assumption_frame_identifier <- C.pushAssumptionFrame sym
            let mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
            let res_mem_impl = mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" $ C.memImplHeap mem_impl }
            writeIORef fixpoint_stuff_ref $ FixpointStuff
              { fixpointStatus = ComputeFixpoint
              , fixpointBlockId = C.Some block_id
              , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
              , fixpointSubstitution = MapF.empty
              , fixpointRegMap = sim_state ^. (C.stateCrucibleFrame . C.frameRegs)
              , fixpointMemSubstitution = Map.empty
              , fixpointLoopCondition = undefined
              , fixpointLoopIndexBound = undefined
              }
            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              sim_state & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

          ComputeFixpoint
            | FixpointStuff { fixpointRegMap = reg_map } <- fixpoint_stuff
            , Just Refl <- W4.testEquality
                (fmapFC C.regType $ C.regMap reg_map)
                (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do
              ?logMessage $ "SimpleLoopFixpoint: RunningState: " ++ show ComputeFixpoint ++ ": " ++ show block_id
              _ <- C.popAssumptionFrameAndObligations sym $ fixpointAssumptionFrameIdentifier fixpoint_stuff

              -- widen the inductive condition
              (join_reg_map, join_substitution) <- runStateT
                (joinRegEntries sym
                  (C.regMap reg_map)
                  (C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs))) $
                fixpointSubstitution fixpoint_stuff

              let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
              let (header_mem_impl, mem_allocs, mem_writes) = dropMemStackFrame body_mem_impl
              when (C.sizeMemAllocs mem_allocs /= 0) $
                fail "SimpleLoopFixpoint: unsupported memory allocation in loop body."

              -- widen the memory
              mem_substitution_candidate <- Map.fromList <$> catMaybes <$> case mem_writes of
                C.MemWrites [C.MemWritesChunkIndexed mmm] -> mapM
                  (\case
                    (C.MemWrite ptr (C.MemStore _ storeage_type _))
                      | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
                      , Just off <- BV.asNatural <$> W4.asBV (C.llvmPointerOffset ptr) -> do
                        let sz = C.typeEnd 0 storeage_type
                        some_join_varaible <- liftIO $ case W4.mkNatRepr $ C.bytesToBits sz of
                          C.Some bv_width
                            | Just C.LeqProof <- W4.testLeq (W4.knownNat @1) bv_width -> do
                              join_varaible <- W4.freshConstant sym
                                (userSymbol' "mem_join_var")
                                (W4.BaseBVRepr bv_width)
                              return $ MemFixpointEntry
                                { memFixpointEntrySym = sym
                                , memFixpointEntryJoinVariable = join_varaible
                                }
                            | otherwise ->
                              C.panic
                                "SimpleLoopFixpoint.simpleLoopFixpoint"
                                ["unexpected storage type " ++ show storeage_type ++ " of size " ++ show sz]
                        return $ Just ((blk, off, fromIntegral sz), (some_join_varaible, storeage_type))
                      | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
                      , Just Refl <- W4.testEquality ?ptrWidth (C.ptrWidth ptr) -> do
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
                    _ -> fail $ "SimpleLoopFixpoint: not MemWrite: " ++ show (C.ppMemWrites mem_writes))
                  (List.concat $ IntMap.elems mmm)
                _ -> fail $ "SimpleLoopFixpoint: not MemWritesChunkIndexed: " ++ show (C.ppMemWrites mem_writes)

              -- check that the mem substitution always computes the same footprint on every iteration (!?!)
              mem_substitution <- if Map.null (fixpointMemSubstitution fixpoint_stuff)
                then return mem_substitution_candidate
                else if Map.keys mem_substitution_candidate == Map.keys (fixpointMemSubstitution fixpoint_stuff)
                  then return $ fixpointMemSubstitution fixpoint_stuff
                  else fail "SimpleLoopFixpoint: unsupported memory writes change"

              assumption_frame_identifier <- C.pushAssumptionFrame sym

              -- check if we are done; if we did not introduce any new variables, we don't have to widen any more
              if MapF.keys join_substitution == MapF.keys (fixpointSubstitution fixpoint_stuff)

                -- we found the fixpoint, get ready to wrap up
                then do
                  ?logMessage $
                    "SimpleLoopFixpoint: RunningState: " ++ show ComputeFixpoint ++ " -> " ++ show CheckFixpoint
                  ?logMessage $
                    "SimpleLoopFixpoint: cond: " ++ show (W4.printSymExpr $ fixpointLoopCondition fixpoint_stuff)

                  -- we have delayed populating the main substituation map with
                  --  memory variables, so we have to do that now

                  header_mem_substitution <- loadMemJoinVariables sym header_mem_impl $
                    fixpointMemSubstitution fixpoint_stuff
                  body_mem_substitution <- loadMemJoinVariables sym body_mem_impl $
                    fixpointMemSubstitution fixpoint_stuff

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
                  -- ?logMessage $ "normal_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList normal_substitution)
                  -- ?logMessage $ "equality_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList equality_substitution)

                  -- unify widening variables in the register subst
                  let res_reg_map = applySubstitutionRegEntries sym equality_substitution join_reg_map

                  -- unify widening varialbes in the memory subst
                  res_mem_impl <- storeMemJoinVariables
                    sym
                    (header_mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" (C.memImplHeap header_mem_impl) })
                    mem_substitution
                    equality_substitution

                  -- finally we can determine the loop bounds
                  loop_index_bound <- findLoopIndexBound sym normal_substitution $ fixpointLoopCondition fixpoint_stuff

                  (_ :: ()) <- case loop_index_bound of
                    LoopIndexBound{ index = loop_index, stop = loop_stop } -> do
                      loc <- W4.getCurrentProgramLoc sym
                      index_bound_condition <- loopIndexBoundCondition sym loop_index loop_stop
                      C.addAssumption sym $ C.GenericAssumption loc "" index_bound_condition
                      index_start_step_condition <- loopIndexStartStepCondition sym loop_index_bound
                      C.addAssumption sym $ C.GenericAssumption loc "" index_start_step_condition

                  writeIORef fixpoint_stuff_ref $ FixpointStuff
                    { fixpointStatus = CheckFixpoint
                    , fixpointBlockId = C.Some block_id
                    , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
                    , fixpointSubstitution = normal_substitution
                    , fixpointRegMap = C.RegMap res_reg_map
                    , fixpointMemSubstitution = mem_substitution
                    , fixpointLoopCondition = fixpointLoopCondition fixpoint_stuff
                    , fixpointLoopIndexBound = loop_index_bound
                    }
                  return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                    sim_state & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap res_reg_map
                      & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

                else do
                  ?logMessage $
                    "SimpleLoopFixpoint: RunningState: " ++ show ComputeFixpoint ++ " -> " ++ show ComputeFixpoint

                  -- write any new widening variables into memory state
                  res_mem_impl <- storeMemJoinVariables sym
                    (header_mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" (C.memImplHeap header_mem_impl) })
                    mem_substitution
                    MapF.empty

                  writeIORef fixpoint_stuff_ref $ FixpointStuff
                    { fixpointStatus = ComputeFixpoint
                    , fixpointBlockId = C.Some block_id
                    , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
                    , fixpointSubstitution = join_substitution
                    , fixpointRegMap = C.RegMap join_reg_map
                    , fixpointMemSubstitution = mem_substitution
                    , fixpointLoopCondition = undefined
                    , fixpointLoopIndexBound = undefined
                    }
                  return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                    sim_state & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap join_reg_map
                      & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

            | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: " ++ show ComputeFixpoint]

          CheckFixpoint
            | FixpointStuff { fixpointRegMap = reg_map } <- fixpoint_stuff
            , Just Refl <- W4.testEquality
                (fmapFC C.regType $ C.regMap reg_map)
                (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do
              ?logMessage $
                "SimpleLoopFixpoint: RunningState: "
                ++ show CheckFixpoint
                ++ " -> "
                ++ show AfterFixpoint
                ++ ": "
                ++ show block_id

              loc <- W4.getCurrentProgramLoc sym

              -- assert that the hypothesis we made about the loop termination condition is true
              (_ :: ()) <- case fixpointLoopIndexBound fixpoint_stuff of
                LoopIndexBound{ index = loop_index, stop = loop_stop } -> do
                  -- check the loop index bound condition
                  index_bound_condition <- loopIndexBoundCondition
                    sym
                    (bodyValue $ fromJust $ MapF.lookup loop_index $ fixpointSubstitution fixpoint_stuff)
                    loop_stop
                  C.addProofObligation sym $ C.LabeledPred index_bound_condition $ C.SimError loc ""

              _ <- C.popAssumptionFrame sym $ fixpointAssumptionFrameIdentifier fixpoint_stuff

              let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
              let (header_mem_impl, _mem_allocs, _mem_writes) = dropMemStackFrame body_mem_impl

              body_mem_substitution <- loadMemJoinVariables sym body_mem_impl $ fixpointMemSubstitution fixpoint_stuff
              let res_substitution = MapF.mapWithKey
                    (\variable fixpoint_entry ->
                      fixpoint_entry
                        { bodyValue = MapF.findWithDefault (bodyValue fixpoint_entry) variable body_mem_substitution
                        })
                    (fixpointSubstitution fixpoint_stuff)
              -- ?logMessage $ "res_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList res_substitution)

              -- match things up with the input function that describes the loop body behavior
              (fixpoint_func_substitution, fixpoint_func_condition) <- liftIO $
                fixpoint_func res_substitution $ fixpointLoopCondition fixpoint_stuff

              C.addProofObligation sym $ C.LabeledPred fixpoint_func_condition $ C.SimError loc ""
              -- ?logMessage $ "fixpoint_func_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList fixpoint_func_substitution)

              let res_reg_map = C.RegMap $
                    applySubstitutionRegEntries sym fixpoint_func_substitution (C.regMap reg_map)

              res_mem_impl <- storeMemJoinVariables sym
                header_mem_impl
                (fixpointMemSubstitution fixpoint_stuff)
                fixpoint_func_substitution

              (_ :: ()) <- case fixpointLoopIndexBound fixpoint_stuff of
                LoopIndexBound{ index = loop_index, stop = loop_stop } -> do
                  let loop_index' = MapF.findWithDefault loop_index loop_index fixpoint_func_substitution
                  index_bound_condition <- loopIndexBoundCondition sym loop_index' loop_stop
                  C.addAssumption sym $ C.GenericAssumption loc "" index_bound_condition
                  index_start_step_condition <- loopIndexStartStepCondition sym $ LoopIndexBound
                    { index = loop_index'
                    , start = start (fixpointLoopIndexBound fixpoint_stuff)
                    , stop = loop_stop
                    , step = step (fixpointLoopIndexBound fixpoint_stuff)
                    }
                  C.addAssumption sym $ C.GenericAssumption loc "" index_start_step_condition

              writeIORef fixpoint_stuff_ref $ fixpoint_stuff
                { fixpointStatus = AfterFixpoint
                , fixpointSubstitution = res_substitution
                }
              return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                sim_state & (C.stateCrucibleFrame . C.frameRegs) .~ res_reg_map
                  & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

            | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: " ++ show CheckFixpoint]

          AfterFixpoint -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" [show AfterFixpoint]

        | otherwise -> do
          ?logMessage $ "SimpleLoopFixpoint: RunningState: RunBlockStart: " ++ show block_id
          return C.ExecutionFeatureNoChange

      -- maybe need to rework this, so that we are sure to capture even concrete exits from the loop
      C.SymbolicBranchState branch_condition true_frame false_frame _target sim_state
        | Just loop_body_some_block_ids <- Map.lookup (fixpointBlockId fixpoint_stuff) loop_map
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

          (condition, frame) <- case fixpointStatus fixpoint_stuff of
            BeforeFixpoint -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" [show BeforeFixpoint]
            ComputeFixpoint -> do
              -- continue in the loop
              ?logMessage $ "SimpleLoopFixpoint: SymbolicBranchState: " ++ show ComputeFixpoint
              writeIORef fixpoint_stuff_ref $ fixpoint_stuff { fixpointLoopCondition = loop_condition }
              return (loop_condition, inside_loop_frame)
            CheckFixpoint -> do
              -- continue in the loop
              ?logMessage $ "SimpleLoopFixpoint: SymbolicBranchState: " ++ show CheckFixpoint
              return (loop_condition, inside_loop_frame)
            AfterFixpoint -> do
              -- break out of the loop
              ?logMessage $ "SimpleLoopFixpoint: SymbolicBranchState: " ++ show AfterFixpoint
              not_loop_condition <- W4.notPred sym loop_condition
              return (not_loop_condition, outside_loop_frame)

          loc <- W4.getCurrentProgramLoc sym
          C.addAssumption sym $ C.BranchCondition loc (C.pausedLoc frame) condition
          C.ExecutionFeatureNewState <$>
            runReaderT
              (C.resumeFrame (C.forgetPostdomFrame frame) $ sim_state ^. (C.stateTree . C.actContext))
              sim_state

      _ -> return C.ExecutionFeatureNoChange


data MaybePausedFrameTgtId f where
  JustPausedFrameTgtId :: C.Some (C.BlockID b) -> MaybePausedFrameTgtId (C.CrucibleLang b r)
  NothingPausedFrameTgtId :: MaybePausedFrameTgtId f

pausedFrameTgtId :: C.PausedFrame p sym ext rtp f -> MaybePausedFrameTgtId f
pausedFrameTgtId C.PausedFrame{ resume = resume } = case resume of
  C.ContinueResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  C.CheckMergeResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  _ -> NothingPausedFrameTgtId
