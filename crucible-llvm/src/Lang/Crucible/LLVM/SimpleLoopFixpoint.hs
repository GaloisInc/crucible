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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}


module Lang.Crucible.LLVM.SimpleLoopFixpoint
  ( FixpointEntry(..)
  , FixpointState(..)
  , simpleLoopFixpoint
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Foldable
import qualified Data.IntMap as IntMap
import           Data.IORef
import           Data.Kind
import qualified Data.List as List
import           Data.Maybe
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           GHC.TypeLits
import qualified System.IO

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map (MapF)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
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
  compareF x y = joinOrderingF
    (compareF (headerValue x) (headerValue y))  
    (compareF (bodyValue x) (bodyValue y))
instance OrdF (FixpointEntry sym) => W4.TestEquality (FixpointEntry sym) where
  testEquality x y = orderingF_refl $ compareF x y

data MemLocation sym w = MemLocation
  { memLocationBlock :: Natural
  , memLocationOffset :: W4.SymBV sym w
  , memLocationSize :: W4.SymBV sym w
  }

instance OrdF (W4.SymExpr sym) => Ord (MemLocation sym w) where
  compare x y =
    compare (memLocationBlock x) (memLocationBlock y)
    <> toOrdering (compareF (memLocationOffset x) (memLocationOffset y))
    <> toOrdering (compareF (memLocationSize x) (memLocationSize y))
instance OrdF (W4.SymExpr sym) => Eq (MemLocation sym w) where
  x == y = EQ == compare x y

data MemFixpointEntry sym wptr where
  MemStoreFixpointEntry ::
    (1 <= w) =>
    W4.SymBV sym w {- ^ bitvector join variable -} ->
    C.StorageType ->
    MemFixpointEntry sym wptr
  MemArrayFixpointEntry ::
    W4.SymArray sym (C.SingleCtx (W4.BaseBVType wptr)) (W4.BaseBVType 8) {- ^ array join variable -} ->
    W4.SymBV sym wptr {- ^ length of the allocation -} ->
    MemFixpointEntry sym wptr


-- | This datatype captures the state machine that progresses as we
--   attempt to compute a loop invariant for a simple structured loop.
data FixpointState sym wptr blocks args
    -- | We have not yet encoundered the loop head
  = BeforeFixpoint

    -- | We have encountered the loop head at least once, and are in the process
    --   of converging to an inductive representation of the live variables
    --   in the loop.
  | ComputeFixpoint (FixpointRecord sym wptr blocks args)

    -- | We have found an inductively-strong representation of the live variables
    --   of the loop, and have discovered the loop index structure controling the
    --   execution of the loop. We are now executing the loop once more to compute
    --   verification conditions for executions that reamain in the loop.
  | CheckFixpoint
      (FixpointRecord sym wptr blocks args)
      (W4.SomeSymFn sym) -- ^ function that represents the loop invariant
      (Some (Ctx.Assignment (W4.SymExpr sym))) -- ^ arguments to the loop invariant
      (W4.Pred sym) -- ^ predicate that represents the loop condition

    -- | Finally, we stitch everything we have found together into the rest of the program.
    --   Starting from the loop header one final time, we now force execution to exit the loop
    --   and continue into the rest of the program.
  | AfterFixpoint
      (FixpointRecord sym wptr blocks args)
      (W4.SomeSymFn sym) -- ^ function that represents the loop invariant

-- | Data about the loop that we incrementally compute as we approach fixpoint.
data FixpointRecord sym wptr blocks args = FixpointRecord
  {
    -- | Block identifier of the head of the loop
    fixpointBlockId :: C.BlockID blocks args

    -- | identifier for the currently-active assumption frame related to this fixpoint computation
  , fixpointAssumptionFrameIdentifier :: C.FrameIdentifier

    -- | Map from introduced widening variables to prestate value before the loop starts,
    --   and to the value computed in a single loop iteration, assuming we return to the
    --   loop header. These variables may appear only in either registers or memory.
  , fixpointSubstitution :: MapF (W4.SymExpr sym) (FixpointEntry sym)

    -- | Prestate values of the Crucible registers when the loop header is first encountered.
  , fixpointRegMap :: C.RegMap sym args

    -- | Triples are (blockId, offset, size) to bitvector-typed entries ( bitvector only/not pointers )
  , fixpointMemSubstitution :: Map (MemLocation sym wptr) (MemFixpointEntry sym wptr)

  , fixpointEqualitySubstitution :: MapF (W4.SymExpr sym) (W4.SymExpr sym)

    -- | The loop index variable
  , fixpointIndex :: W4.SymBV sym wptr
  }


fixpointRecord :: FixpointState sym wptr blocks args -> Maybe (FixpointRecord sym wptr blocks args)
fixpointRecord BeforeFixpoint = Nothing
fixpointRecord (ComputeFixpoint r) = Just r
fixpointRecord (CheckFixpoint r _ _ _) = Just r
fixpointRecord (AfterFixpoint r _) = Just r


newtype FixpointMonad sym a =
  FixpointMonad (StateT (MapF (W4.SymExpr sym) (FixpointEntry sym)) IO a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

deriving instance s ~ MapF (W4.SymExpr sym) (FixpointEntry sym) => MonadState s (FixpointMonad sym)

runFixpointMonad ::
  FixpointMonad sym a ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  IO (a, MapF (W4.SymExpr sym) (FixpointEntry sym))
runFixpointMonad (FixpointMonad m) = runStateT m


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
          join_variable <- liftIO $ W4.freshConstant sym (W4.safeSymbol "reg_join_var") (W4.BaseBVRepr w)
          let join_entry = FixpointEntry
                { headerValue = C.llvmPointerOffset (C.regValue left)
                , bodyValue = C.llvmPointerOffset (C.regValue right)
                }
          put $ MapF.insert join_variable join_entry subst
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer (C.llvmPointerBlock (C.regValue left)) join_variable
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
      join_varaible <- liftIO $ W4.freshConstant sym (W4.safeSymbol "macaw_reg") W4.BaseBoolRepr
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


joinMem ::
  forall sym wptr .
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  C.MemImpl sym ->
  C.MemWrites sym ->
  IO (Map (MemLocation sym wptr) (MemFixpointEntry sym wptr))
joinMem sym mem_impl mem_writes = do
  ranges <- maybe (fail "SimpleLoopFixpoint: unsupported symbolic pointers") return =<<
    runMaybeT (C.writeRangesMem @_ @wptr sym $ C.memImplHeap mem_impl)

  mem_subst <- case mem_writes of
    C.MemWrites [C.MemWritesChunkIndexed indexed_writes] -> Map.fromList . catMaybes <$> mapM
      (\case
        C.MemWrite ptr mem_source
          | Just Refl <- W4.testEquality ?ptrWidth (C.ptrWidth ptr)
          , Just blk <- W4.asNat (C.llvmPointerBlock ptr) -> do
            sz <- maybe (fail "SimpleLoopFixpoint: unsupported MemSource") return =<<
              runMaybeT (C.writeSourceSize sym mem_source)
            let mem_loc = MemLocation
                  { memLocationBlock = blk
                  , memLocationOffset = C.llvmPointerOffset ptr
                  , memLocationSize = sz
                  }

            is_loop_local <- and <$> mapM
              (\(prev_off, prev_sz) -> do
                disjoint_pred <- C.buildDisjointRegionsAssertionWithSub
                  sym
                  ptr
                  sz
                  (C.LLVMPointer (C.llvmPointerBlock ptr) prev_off)
                  prev_sz
                return $ W4.asConstantPred disjoint_pred == Just True)
              (Map.findWithDefault [] blk ranges)

            if not is_loop_local then do
              mem_entry <- case mem_source of
                C.MemStore _ storage_type _ ->
                  case W4.mkNatRepr $ C.bytesToBits (C.typeEnd 0 storage_type) of
                    C.Some bv_width
                      | Just C.LeqProof <- W4.testLeq (W4.knownNat @1) bv_width -> do
                        join_variable <- W4.freshConstant sym (W4.safeSymbol "mem_join_var") (W4.BaseBVRepr bv_width)
                        return $ MemStoreFixpointEntry join_variable storage_type
                      | otherwise ->
                        C.panic
                          "SimpleLoopFixpoint.simpleLoopFixpoint"
                          ["unexpected storage type " ++ show storage_type]

                C.MemArrayStore arr _ -> do
                  join_variable <- W4.freshConstant sym (W4.safeSymbol "mem_join_var") (W4.exprType arr)
                  return $ MemArrayFixpointEntry join_variable sz

                _ -> fail "SimpleLoopFixpoint.joinMem: unsupported MemSource"

              return $ Just (mem_loc, mem_entry)

            else
              return Nothing

        _ -> fail $ "SimpleLoopFixpoint: not MemWrite: " ++ show (C.ppMemWrites mem_writes))
      (List.concat $ IntMap.elems indexed_writes)

    C.MemWrites [] -> return Map.empty

    _ -> fail $ "SimpleLoopFixpoint: not MemWritesChunkIndexed: " ++ show (C.ppMemWrites mem_writes)

  checkDisjointRegions sym $ Map.keys mem_subst

  return mem_subst

checkDisjointRegions ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  [MemLocation sym wptr] ->
  IO ()
checkDisjointRegions sym = \case
  hd_mem_loc : tail_mem_locs -> do
    mapM_ (checkDisjointRegions' sym hd_mem_loc) tail_mem_locs
    checkDisjointRegions sym tail_mem_locs
  [] -> return ()

checkDisjointRegions' ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  MemLocation sym wptr ->
  MemLocation sym wptr ->
  IO ()
checkDisjointRegions' sym mem_loc1 mem_loc2 = do
  ptr1 <- memLocationPtr sym mem_loc1
  ptr2 <- memLocationPtr sym mem_loc2
  disjoint_pred <- C.buildDisjointRegionsAssertionWithSub
    sym
    ptr1
    (memLocationSize mem_loc1)
    ptr2
    (memLocationSize mem_loc2)
  when (W4.asConstantPred disjoint_pred /= Just True) $
    fail $
      "SimpleLoopFixpoint: non-disjoint ranges: off1="
      ++ show (W4.printSymExpr $ C.llvmPointerOffset ptr1)
      ++ ", sz1="
      ++ show (W4.printSymExpr $ memLocationSize mem_loc1)
      ++ ", off2="
      ++ show (W4.printSymExpr $ C.llvmPointerOffset ptr2)
      ++ ", sz2="
      ++ show (W4.printSymExpr $ memLocationSize mem_loc2)


loadMemJoinVariables ::
  (C.IsSymBackend sym bak, C.HasPtrWidth wptr, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  bak ->
  C.MemImpl sym ->
  Map (MemLocation sym wptr) (MemFixpointEntry sym wptr) ->
  IO (MapF (W4.SymExpr sym) (W4.SymExpr sym))
loadMemJoinVariables bak mem subst =
  let sym = C.backendGetSym bak in
  MapF.fromList <$> mapM
    (\(mem_loc, mem_entry) -> do
      ptr <- memLocationPtr sym mem_loc
      case mem_entry of
        MemStoreFixpointEntry join_variable storage_type -> do
          val <- C.doLoad bak mem ptr storage_type (C.LLVMPointerRepr $ W4.bvWidth join_variable) C.noAlignment
          case W4.asNat (C.llvmPointerBlock val) of
            Just 0 -> return $ MapF.Pair join_variable $ C.llvmPointerOffset val
            _ -> fail $ "SimpleLoopFixpoint.loadMemJoinVariables: unexpected val:" ++ show (C.ppPtr val)
        MemArrayFixpointEntry join_variable size -> do
          -- TODO: handle arrays
          maybe_allocation_array <- C.asMemAllocationArrayStore sym ?ptrWidth ptr (C.memImplHeap mem)
          case maybe_allocation_array of
            Just (ok, arr, arr_sz) | Just True <- W4.asConstantPred ok -> do
              return $ MapF.Pair join_variable arr
            _ -> fail $ "SimpleLoopFixpoint.loadMemJoinVariables")
    (Map.toAscList subst)

storeMemJoinVariables ::
  (C.IsSymBackend sym bak, C.HasPtrWidth wptr, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  bak ->
  C.MemImpl sym ->
  Map (MemLocation sym wptr) (MemFixpointEntry sym wptr) ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  IO (C.MemImpl sym)
storeMemJoinVariables bak mem mem_subst eq_subst = do
  let sym = C.backendGetSym bak
  foldlM
    (\mem_acc (mem_loc, mem_entry) -> do
      ptr <- memLocationPtr sym mem_loc
      case mem_entry of
        MemStoreFixpointEntry join_variable storage_type -> do
          C.doStore bak mem_acc ptr (C.LLVMPointerRepr $ W4.bvWidth join_variable) storage_type C.noAlignment =<<
            C.llvmPointer_bv sym (findWithDefaultKey eq_subst join_variable)
        MemArrayFixpointEntry join_variable size -> do
          C.doArrayStore bak mem_acc ptr C.noAlignment (findWithDefaultKey eq_subst join_variable) size)
    mem
    (Map.toAscList mem_subst)

memLocationPtr ::
  C.IsSymInterface sym =>
  sym ->
  MemLocation sym wptr ->
  IO (C.LLVMPtr sym wptr)
memLocationPtr sym (MemLocation { memLocationBlock = blk, memLocationOffset = off }) =
  C.LLVMPointer <$> W4.natLit sym blk <*> return off


applySubstitutionMemFixpointEntries  ::
  (C.IsSymInterface sym, Functor f) =>
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  f (MemFixpointEntry sym wptr) ->
  f (MemFixpointEntry sym wptr)
applySubstitutionMemFixpointEntries substitution = fmap $ \case
  MemStoreFixpointEntry join_variable storage_type ->
    MemStoreFixpointEntry (findWithDefaultKey substitution join_variable) storage_type
  MemArrayFixpointEntry join_variable size ->
    MemArrayFixpointEntry (findWithDefaultKey substitution join_variable) size


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

loopIndexLinearSubstitution ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr, MonadIO m) =>
  sym ->
  W4.SymBV sym wptr ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  m (MapF (W4.SymExpr sym) (W4.SymExpr sym))
loopIndexLinearSubstitution sym index_variable =
  MapF.traverseMaybeWithKey
    (\variable entry -> case W4.testEquality (W4.exprType variable) (W4.exprType index_variable) of
      Just Refl -> do
        diff <- liftIO $ W4.bvSub sym (bodyValue entry) variable
        case W4.asBV diff of
          Just{} -> liftIO $ Just <$> (W4.bvAdd sym (headerValue entry) =<< W4.bvMul sym index_variable diff)
          Nothing -> return Nothing
      Nothing -> return Nothing)

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


-- | This execution feature is designed to allow a limited form of
--   verification for programs with unbounded looping structures.
--
--   It is currently highly experimental and has many limitations.
--   Most notably, it only really works properly for functions
--   consisting of a single, non-nested loop with a single exit point.
--   Moreover, the loop must have an indexing variable that counts up
--   from a starting point by a fixed stride amount.
--
--   Currently, these assumptions about the loop structure are not
--   checked.
--
--   The basic use case here is for verifying functions that loop
--   through an array of data of symbolic length.  This is done by
--   providing a \""fixpoint function\" which describes how the live
--   values in the loop at an arbitrary iteration are used to compute
--   the final values of those variables before execution leaves the
--   loop. The number and order of these variables depends on
--   internal details of the representation, so is relatively fragile.
simpleLoopFixpoint ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr, KnownNat wptr, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  C.CFG ext blocks init ret {- ^ The function we want to verify -} ->
  C.GlobalVar C.Mem {- ^ global variable representing memory -} ->
  Maybe (MapF (W4.SymExpr sym) (FixpointEntry sym) -> W4.Pred sym -> IO (MapF (W4.SymExpr sym) (W4.SymExpr sym), Maybe (W4.Pred sym))) ->
  IO (C.ExecutionFeature p sym ext rtp, IORef (C.Some (FixpointState sym wptr blocks)))
simpleLoopFixpoint sym cfg@C.CFG{..} mem_var maybe_fixpoint_func = do
  verbSetting <- W4.getOptionSetting W4.verbosity $ W4.getConfiguration sym
  verb <- fromInteger <$> W4.getOpt verbSetting

  --  let loop_map = Map.fromList $ mapMaybe
  --       (\case
  --         scc@(C.SCC _) -> Just (wtoHead, wtoHead : concatMap flattenWTOComponent wtoComps)
  --         C.Vertex{} -> Nothing)
  --       (C.cfgWeakTopologicalOrdering cfg)

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

  fixpoint_state_ref <- newIORef $ C.Some BeforeFixpoint

  return $ (, fixpoint_state_ref) $ C.ExecutionFeature $ \exec_state -> do
    let ?logMessage = \msg -> when (verb >= (3 :: Natural)) $ do
          let h = C.printHandle $ C.execStateContext exec_state
          System.IO.hPutStrLn h msg
          System.IO.hFlush h
    C.Some fixpoint_state <- readIORef fixpoint_state_ref
    C.withBackend (C.execStateContext exec_state) $ \bak -> case exec_state of

      C.RunningState (C.RunBlockStart block_id) sim_state
        | C.SomeHandle cfgHandle == C.frameHandle (sim_state ^. C.stateCrucibleFrame)
        -- make sure the types match
        , Just Refl <- W4.testEquality
            (fmapFC C.blockInputs cfgBlockMap)
            (fmapFC C.blockInputs $ C.frameBlockMap $ sim_state ^. C.stateCrucibleFrame)
          -- loop map is what we computed above, is this state at a loop header
        , Map.member (C.Some block_id) loop_map ->
            advanceFixpointState bak mem_var maybe_fixpoint_func block_id sim_state fixpoint_state_ref

        | otherwise -> do
            ?logMessage $ "SimpleLoopFixpoint: RunningState: RunBlockStart: " ++ show block_id
            return C.ExecutionFeatureNoChange

      -- TODO: maybe need to rework this, so that we are sure to capture even concrete exits from the loop.
      C.SymbolicBranchState branch_condition true_frame false_frame _target sim_state
        | Just fixpoint_record <- fixpointRecord fixpoint_state
        , Just loop_body_some_block_ids <- Map.lookup (C.Some $ fixpointBlockId fixpoint_record) loop_map
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

          (condition, frame) <- case fixpoint_state of
            BeforeFixpoint -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint:" ["BeforeFixpoint"]

            ComputeFixpoint{} -> do
              -- continue in the loop
              ?logMessage "SimpleLoopFixpoint: SymbolicBranchState: ComputeFixpoint"
              return (loop_condition, inside_loop_frame)

            CheckFixpoint _fixpoint_record some_inv_pred some_uninterpreted_constants _ -> do
              -- continue in the loop
              ?logMessage "SimpleLoopFixpoint: SymbolicBranchState: CheckFixpoint"
              writeIORef fixpoint_state_ref $ C.Some $
                CheckFixpoint fixpoint_record some_inv_pred some_uninterpreted_constants loop_condition
              return (loop_condition, inside_loop_frame)

            AfterFixpoint{} -> do
              -- break out of the loop
              ?logMessage "SimpleLoopFixpoint: SymbolicBranchState: AfterFixpoint"
              not_loop_condition <- W4.notPred sym loop_condition
              return (not_loop_condition, outside_loop_frame)

          loc <- W4.getCurrentProgramLoc sym
          C.addAssumption bak $ C.BranchCondition loc (C.pausedLoc frame) condition
          C.ExecutionFeatureNewState <$>
            runReaderT
              (C.resumeFrame (C.forgetPostdomFrame frame) $ sim_state ^. (C.stateTree . C.actContext))
              sim_state

      _ -> return C.ExecutionFeatureNoChange


advanceFixpointState ::
  (C.IsSymBackend sym bak, C.HasPtrWidth wptr, KnownNat wptr, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions, ?logMessage :: String -> IO ()) =>
  bak ->
  C.GlobalVar C.Mem ->
  Maybe (MapF (W4.SymExpr sym) (FixpointEntry sym) -> W4.Pred sym -> IO (MapF (W4.SymExpr sym) (W4.SymExpr sym), Maybe (W4.Pred sym))) ->
  C.BlockID blocks args ->
  C.SimState p sym ext rtp (C.CrucibleLang blocks r) ('Just args) ->
  IORef (C.Some (FixpointState sym wptr blocks)) ->
  IO (C.ExecutionFeatureResult p sym ext rtp)

advanceFixpointState bak mem_var maybe_fixpoint_func block_id sim_state fixpoint_state_ref = do
  let sym = C.backendGetSym bak
  C.Some fixpoint_state <- readIORef fixpoint_state_ref
  case fixpoint_state of
    BeforeFixpoint -> do
      ?logMessage $ "SimpleLoopFixpoint: RunningState: BeforeFixpoint -> ComputeFixpoint"
      assumption_frame_identifier <- C.pushAssumptionFrame bak
      index_var <- W4.freshConstant sym (W4.safeSymbol "index_var") W4.knownRepr
      let mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
      let res_mem_impl = mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" $ C.memImplHeap mem_impl }
      writeIORef fixpoint_state_ref $ C.Some $ ComputeFixpoint $
        FixpointRecord
        { fixpointBlockId = block_id
        , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
        , fixpointSubstitution = MapF.empty
        , fixpointRegMap = sim_state ^. (C.stateCrucibleFrame . C.frameRegs)
        , fixpointMemSubstitution = Map.empty
        , fixpointEqualitySubstitution = MapF.empty
        , fixpointIndex = index_var
        }
      return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
        sim_state & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

    ComputeFixpoint fixpoint_record
      | Just Refl <- W4.testEquality
          (fmapFC C.regType $ C.regMap $ fixpointRegMap fixpoint_record)
          (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do


        ?logMessage $ "SimpleLoopFixpoint: RunningState: ComputeFixpoint: " ++ show block_id
        proof_goals_and_assumptions_vars <- Set.map (mapSome $ W4.varExpr sym) <$>
          (Set.union <$> C.proofObligationsUninterpConstants bak <*> C.pathConditionUninterpConstants bak)
        (frame_assumptions, _) <- C.popAssumptionFrameAndObligations bak $ fixpointAssumptionFrameIdentifier fixpoint_record
        loop_condition <- C.assumptionsPred sym frame_assumptions

        -- widen the inductive condition
        (join_reg_map, join_substitution) <- runFixpointMonad
          (joinRegEntries sym
            (C.regMap $ fixpointRegMap fixpoint_record)
            (C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs))) $
          fixpointSubstitution fixpoint_record

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
        let (header_mem_impl, mem_allocs, mem_writes) = dropMemStackFrame body_mem_impl
        when (C.sizeMemAllocs mem_allocs /= 0) $
          fail "SimpleLoopFixpoint: unsupported memory allocation in loop body."

        -- widen the memory
        mem_substitution_candidate <- joinMem sym header_mem_impl mem_writes

        -- check that the mem substitution always computes the same footprint on every iteration (!?!)
        mem_substitution <- if Map.null (fixpointMemSubstitution fixpoint_record)
          then return mem_substitution_candidate
          else if Map.keys mem_substitution_candidate == Map.keys (fixpointMemSubstitution fixpoint_record)
            then return $ fixpointMemSubstitution fixpoint_record
            else fail "SimpleLoopFixpoint: unsupported memory writes change"

        assumption_frame_identifier <- C.pushAssumptionFrame bak

        -- check if we are done; if we did not introduce any new variables, we don't have to widen any more
        if MapF.keys join_substitution == MapF.keys (fixpointSubstitution fixpoint_record) && Map.keys mem_substitution == Map.keys (fixpointMemSubstitution fixpoint_record)

          -- we found the fixpoint, get ready to wrap up
          then do
            ?logMessage $
              "SimpleLoopFixpoint: RunningState: ComputeFixpoint -> CheckFixpoint"

            -- we have delayed populating the main substitution map with
            --  memory variables, so we have to do that now

            header_mem_substitution <- loadMemJoinVariables bak header_mem_impl $
              fixpointMemSubstitution fixpoint_record
            body_mem_substitution <- loadMemJoinVariables bak body_mem_impl $
              fixpointMemSubstitution fixpoint_record

            -- drop variables that don't appear along some back edge
            let union_substitution' = filterSubstitution sym $
                  MapF.union join_substitution $
                  -- this implements zip, because the two maps have the same keys
                  MapF.intersectWithKeyMaybe
                    (\_k x y -> Just $ FixpointEntry{ headerValue = x, bodyValue = y })
                    header_mem_substitution
                    body_mem_substitution
            loop_index_linear_substitution <- loopIndexLinearSubstitution sym (fixpointIndex fixpoint_record) union_substitution'

            let union_substitution = MapF.filterWithKey
                  (\variable _entry -> MapF.notMember variable loop_index_linear_substitution)
                  union_substitution'
            -- try to unify widening variables that have the same values
            let (normal_substitution', equality_substitution') = uninterpretedConstantEqualitySubstitution sym union_substitution

            zero_bv <- W4.bvLit sym knownNat $ BV.zero knownNat
            one_bv <- W4.bvLit sym knownNat $ BV.one knownNat
            add_index_one <- W4.bvAdd sym (fixpointIndex fixpoint_record) one_bv
            let normal_substitution = MapF.insert
                  (fixpointIndex fixpoint_record)
                  FixpointEntry
                    { headerValue = zero_bv
                    , bodyValue = add_index_one
                    }
                  normal_substitution'
            let equality_substitution = MapF.union equality_substitution' loop_index_linear_substitution

            ?logMessage $ "loop_index_linear_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList loop_index_linear_substitution)
            ?logMessage $ "normal_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList normal_substitution)
            ?logMessage $ "equality_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList equality_substitution)

            -- unify widening variables in the register subst
            let res_reg_map = applySubstitutionRegEntries sym equality_substitution join_reg_map

            -- unify widening varialbes in the memory subst
            res_mem_impl <- storeMemJoinVariables
              bak
              (header_mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" (C.memImplHeap header_mem_impl) })
              mem_substitution
              equality_substitution

            let body_values_vars = foldMap (viewSome $ Set.map (mapSome $ W4.varExpr sym) . W4.exprUninterpConstants sym . bodyValue) $
                  MapF.elems normal_substitution
            let header_values_vars = foldMap (viewSome $ Set.map (mapSome $ W4.varExpr sym) . W4.exprUninterpConstants sym . headerValue) $
                  MapF.elems normal_substitution
            -- let all_vars = Set.union proof_goals_and_assumptions_vars $ Set.union body_values_vars header_values_vars
            let all_vars' = Set.insert (Some $ fixpointIndex fixpoint_record) proof_goals_and_assumptions_vars
            let all_vars = Set.filter
                  (\(Some variable) -> MapF.notMember variable equality_substitution)
                  all_vars'
            -- let some_uninterpreted_constants = Ctx.fromList $ Set.toList all_vars
            let filtered_vars =  Set.filter
                  (\(Some variable) ->
                    not (List.isPrefixOf "cundefined_" $ show $ W4.printSymExpr variable)
                    && not (List.isPrefixOf "calign_amount" $ show $ W4.printSymExpr variable)
                    && not (List.isPrefixOf "cnoSatisfyingWrite" $ show $ W4.printSymExpr variable))
                  all_vars
            let some_uninterpreted_constants = Ctx.fromList $ Set.toList filtered_vars
            -- let implicit_vars = Set.filter
            --       (\(Some variable) ->
            --         not (List.isPrefixOf "creg_join_var" $ show $ W4.printSymExpr variable)
            --         && not (List.isPrefixOf "cmem_join_var" $ show $ W4.printSymExpr variable)
            --         && not (List.isPrefixOf "cundefined_" $ show $ W4.printSymExpr variable)
            --         && not (List.isPrefixOf "calign_amount" $ show $ W4.printSymExpr variable)
            --         && not (List.isPrefixOf "cnoSatisfyingWrite" $ show $ W4.printSymExpr variable))
            --       all_vars
            some_inv_pred <- case some_uninterpreted_constants of
              Some uninterpreted_constants -> do
                inv_pred <- W4.freshTotalUninterpFn
                  sym
                  (W4.safeSymbol "inv")
                  (fmapFC W4.exprType uninterpreted_constants)
                  W4.BaseBoolRepr

                loc <- W4.getCurrentProgramLoc sym

                header_inv <- W4.applySymFn sym inv_pred $
                  applySubstitutionFC (fmapF headerValue normal_substitution) uninterpreted_constants
                C.addProofObligation bak $ C.LabeledPred header_inv $ C.SimError loc ""

                inv <- W4.applySymFn sym inv_pred uninterpreted_constants
                C.addAssumption bak $ C.GenericAssumption loc "inv" inv

                return $ W4.SomeSymFn inv_pred

            ?logMessage $
              "proof_goals_and_assumptions_vars: "
              ++ show (map (viewSome W4.printSymExpr) $ Set.toList proof_goals_and_assumptions_vars)
            ?logMessage $
              "body_values_vars: " ++ show (map (viewSome W4.printSymExpr) $ Set.toList body_values_vars)
            ?logMessage $
              "header_values_vars: " ++ show (map (viewSome W4.printSymExpr) $ Set.toList header_values_vars)
            ?logMessage $
              "uninterpreted_constants: " ++ show (map (viewSome W4.printSymExpr) $ Set.toList filtered_vars)

            writeIORef fixpoint_state_ref $ C.Some $
              CheckFixpoint
                FixpointRecord
                { fixpointBlockId = block_id
                , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
                , fixpointSubstitution = normal_substitution
                , fixpointRegMap = C.RegMap res_reg_map
                , fixpointMemSubstitution = mem_substitution
                , fixpointEqualitySubstitution = equality_substitution
                , fixpointIndex = fixpointIndex fixpoint_record
                }
                some_inv_pred
                -- implicit_vars
                some_uninterpreted_constants
                loop_condition

            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              sim_state & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap res_reg_map
                & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

          else do
            ?logMessage $
              "SimpleLoopFixpoint: RunningState: ComputeFixpoint: -> ComputeFixpoint"

            -- write any new widening variables into memory state
            res_mem_impl <- storeMemJoinVariables bak
              (header_mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" (C.memImplHeap header_mem_impl) })
              mem_substitution
              MapF.empty

            writeIORef fixpoint_state_ref $ C.Some $ ComputeFixpoint
              FixpointRecord
              { fixpointBlockId = block_id
              , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
              , fixpointSubstitution = join_substitution
              , fixpointRegMap = C.RegMap join_reg_map
              , fixpointMemSubstitution = mem_substitution
              , fixpointEqualitySubstitution = MapF.empty
              , fixpointIndex = fixpointIndex fixpoint_record
              }
            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              sim_state & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap join_reg_map
                & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

      | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: ComputeFixpoint"]

    CheckFixpoint fixpoint_record some_inv_pred some_uninterpreted_constants loop_condition
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

        -- assert that the hypothesis we made about the loop termination condition is true
        (_ :: ()) <- case (some_inv_pred, some_uninterpreted_constants) of
          (W4.SomeSymFn inv_pred, Some uninterpreted_constants)
            | Just Refl <- testEquality (W4.fnArgTypes inv_pred) (fmapFC W4.exprType uninterpreted_constants)
            , Just Refl <- testEquality (W4.fnReturnType inv_pred) W4.BaseBoolRepr -> do
              inv <- W4.applySymFn sym inv_pred $ applySubstitutionFC
                (fmapF bodyValue $ fixpointSubstitution fixpoint_record)
                uninterpreted_constants
              C.addProofObligation bak $ C.LabeledPred inv $ C.SimError loc ""
            | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: CheckFixpoint"]

        _ <- C.popAssumptionFrame bak $ fixpointAssumptionFrameIdentifier fixpoint_record

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
        let (header_mem_impl, _mem_allocs, _mem_writes) = dropMemStackFrame body_mem_impl

        body_mem_substitution <- loadMemJoinVariables bak body_mem_impl $ fixpointMemSubstitution fixpoint_record
        let res_substitution = MapF.mapWithKey
              (\variable fixpoint_entry ->
                fixpoint_entry
                  { bodyValue = MapF.findWithDefault (bodyValue fixpoint_entry) variable body_mem_substitution
                  })
              (fixpointSubstitution fixpoint_record)
        ?logMessage $ "res_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList res_substitution)

        -- match things up with the input function that describes the loop body behavior
        fixpoint_substitution <- case maybe_fixpoint_func of
          Just fixpoint_func -> do
            (fixpoint_func_substitution, maybe_fixpoint_func_condition) <- fixpoint_func res_substitution loop_condition

            _ <- case maybe_fixpoint_func_condition of
              Just fixpoint_func_condition ->
                C.addProofObligation bak $ C.LabeledPred fixpoint_func_condition $ C.SimError loc ""
              Nothing -> return ()

            ?logMessage $ "fixpoint_func_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList fixpoint_func_substitution)

            return fixpoint_func_substitution

          Nothing -> return MapF.empty

        let res_reg_map = C.RegMap $ applySubstitutionRegEntries sym fixpoint_substitution (C.regMap reg_map)

        res_mem_impl <- storeMemJoinVariables bak
          header_mem_impl
          (fixpointMemSubstitution fixpoint_record)
          (applySubstitutionF fixpoint_substitution $ fixpointEqualitySubstitution fixpoint_record)

        (_ :: ()) <- case (some_inv_pred, some_uninterpreted_constants) of
          (W4.SomeSymFn inv_pred, Some uninterpreted_constants)
            | Just Refl <- testEquality (W4.fnArgTypes inv_pred) (fmapFC W4.exprType uninterpreted_constants)
            , Just Refl <- testEquality (W4.fnReturnType inv_pred) W4.BaseBoolRepr -> do
              inv <- W4.applySymFn sym inv_pred $ applySubstitutionFC fixpoint_substitution uninterpreted_constants
              C.addAssumption bak $ C.GenericAssumption loc "" inv
            | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: CheckFixpoint"]

        writeIORef fixpoint_state_ref $ C.Some $
          AfterFixpoint
            fixpoint_record{ fixpointSubstitution = res_substitution }
            some_inv_pred

        return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
          sim_state & (C.stateCrucibleFrame . C.frameRegs) .~ res_reg_map
            & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

      | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: CheckFixpoint"]

    AfterFixpoint{} -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["AfterFixpoint"]


data MaybePausedFrameTgtId f where
  JustPausedFrameTgtId :: C.Some (C.BlockID b) -> MaybePausedFrameTgtId (C.CrucibleLang b r)
  NothingPausedFrameTgtId :: MaybePausedFrameTgtId f

pausedFrameTgtId :: C.PausedFrame p sym ext rtp f -> MaybePausedFrameTgtId f
pausedFrameTgtId C.PausedFrame{ resume = resume } = case resume of
  C.ContinueResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  C.CheckMergeResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  _ -> NothingPausedFrameTgtId


applySubstitutionF :: (OrdF k, FunctorF f) => MapF k k -> f k -> f k
applySubstitutionF substitution = fmapF $ findWithDefaultKey substitution

applySubstitutionFC :: (OrdF k, FunctorFC f) => MapF k k -> f k l -> f k l
applySubstitutionFC substitution = fmapFC $ findWithDefaultKey substitution

findWithDefaultKey :: forall a (k :: a -> Type) tp . OrdF k => MapF k k -> k tp -> k tp
findWithDefaultKey substitution key = MapF.findWithDefault key key substitution
