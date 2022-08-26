------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.SimpleLoopInvariant
-- Description      : Execution feature to perform verification of simply
--                    structured loops via invariants.
-- Copyright        : (c) Galois, Inc 2022
-- License          : BSD3
-- Stability        : provisional
--
-- 
-- This module provides an execution feature that can be installed
-- into the Crucible simulator which facilitates reasoning about
-- certain kinds of loops by using loop invariants instead of
-- requiring that loops symbolically terminate. In order for this
-- feature to work, the loop in question needs to be
-- single-entry/single-exit, and needs to have a constant memory
-- footprint on each loop iteration (except that memory regions backed
-- by SMT arrays are treated as a whole, so loops can write into
-- different regions of an SMT-array memory region on different
-- iterations). In addition, loop-involved memory writes must be
-- sufficiently concrete that we can determine their region values,
-- and writes to the same region value must have concrete distances
-- from each other, so we can determine if/when they alias.
--
-- To set up a loop invariant for a loop, you must specify which CFG the
-- loop is in, indicate which loop (of potentially several) in the CFG
-- is the one of interest, and give a function that is used to construct
-- the statement of the loop invariant. When given a CFG, the execution
-- feature computes a weak topological ordering to find the loops in
-- the program; the number given by the user selects which of these to
-- install the invariant for.
--
-- At runtime, we will interrupt execution when the loop head is
-- reached; at this point we will record the values of the memory and
-- the incoming local variables. Then, we will begin a series of
-- "hypothetical" executions of the loop body and track how the memory
-- and local variables are modified by the loop body. On each
-- iteration where we find a difference, we replace the local or
-- memory region with a fresh "join variable" which represents the
-- unknown value of a loop-carried dependency. We continue this process
-- until we reach a fixpoint; then we will have captured all the locations
-- that are potentially of interest for the loop invariant.
-- 
-- Once we have found all the loop-carried dependencies, we assert
-- that the loop invariant holds on the initial values upon entry to the
-- loop. Then, we set up another execution starting from the loop head
-- where we first assume the loop invariant over the join variables
-- invented earlier, and begin execution again.  In this mode, when we
-- reach the loop head once more, we assert the loop invariant on the
-- computed values and abort execution along that path. Paths exiting
-- the loop continue as normal.
--
-- Provided the user suppiles an appropriate loop invarant function
-- and can discharge all the generated proof obligations, this procedure
-- should result in a sound proof of partial correctness for the function
-- in question.
--
-- This whole procedure has some relatively fragile elements that are
-- worth calling out.  First, specifying which loop you want to reason
-- about may require some trial-and-error, the WTO ordering might not
-- directly correspond to what is seen in the source code. The most
-- reliable way to select the right loop is to ensure there is only
-- one loop of interest in a given function, and use loop index 0.
-- The other fragility has to do with the discovery of loop-carried
-- dependencies. The number and order of values that are supplied to
-- the loop invariant depend on the internal details of the compiler
-- and simulator, so the user may have to spend some time and effort
-- to discover what the values appearing in the invariant correspond
-- to. This process may well be quite sensitive to changes in the
-- source code.
--
-- Limitiations: currently, this feature is restricted to 64-bit code.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


module Lang.Crucible.LLVM.SimpleLoopInvariant
  ( InvariantEntry(..)
  , InvariantPhase(..)
  , simpleLoopInvariant
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
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
import           Prettyprinter (pretty)

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
import qualified What4.ProgramLoc as W4

import qualified Lang.Crucible.Analysis.Fixpoint.Components as C
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


-- | A datatype describing the reason we are building an instance
--   of the loop invariant.
data InvariantPhase
  = InitialInvariant
  | HypotheticalInvariant
  | InductiveInvariant
 deriving (Eq, Ord, Show)

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
--   any more fresh widening variables, and the body values for each
--   variable are stable across iterations.
data InvariantEntry sym tp =
  InvariantEntry
  { headerValue :: W4.SymExpr sym tp
  , bodyValue :: W4.SymExpr sym tp
  }

instance OrdF (W4.SymExpr sym) => OrdF (InvariantEntry sym) where
  compareF x y = case compareF (headerValue x) (headerValue y) of
    LTF -> LTF
    EQF -> compareF (bodyValue x) (bodyValue y)
    GTF -> GTF

instance OrdF (InvariantEntry sym) => W4.TestEquality (InvariantEntry sym) where
  testEquality x y = orderingF_refl (compareF x y)

-- | This datatype captures the state machine that progresses as we
--   attempt to compute a loop invariant for a simple structured loop.
data FixpointState p sym ext rtp blocks
    -- | We have not yet encoundered the loop head
  = BeforeFixpoint

    -- | We have encountered the loop head at least once, and are in the process
    --   of converging to an inductive representation of the live variables
    --   in the loop.
  | ComputeFixpoint C.FrameIdentifier (FixpointRecord p sym ext rtp blocks)

    -- | We have found an inductively-strong representation of the live variables
    --   of the loop. We are now executing the from the loop head one final time
    --   to produce the proof obligations arising from the body of the loop,
    --   the main inductive loop invariant obligation, and any obligations arising
    --   from code following the loop exit.
    | CheckFixpoint (FixpointRecord p sym ext rtp blocks)


-- | Data about the loop that we incrementally compute as we approach fixpoint.
data FixpointRecord p sym ext rtp blocks = forall args r.
  FixpointRecord
  {
    -- | Block identifier of the head of the loop
    fixpointBlockId :: C.BlockID blocks args

    -- | Map from introduced widening variables to prestate value before the loop starts,
    --   and to the value computed in a single loop iteration, assuming we return to the
    --   loop header. These variables may appear only in either registers or memory.
  , fixpointSubstitution :: VariableSubst sym

    -- | The memory subsitution describes where the loop-carried dependencies live in the
    --   memory.
  , fixpointMemSubstitution :: MemorySubstitution sym

    -- | Prestate values of the Crucible registers when the loop header is first encountered.
  , fixpointRegMap :: C.RegMap sym args

    -- | The sim state of the simulator when we first encounter the loop header.
  , fixpointInitialSimState :: C.SimState p sym ext rtp (C.CrucibleLang blocks r) ('Just args)

    -- | External constants appearing in the expressions computed by the loop. These will be passed
    --   into the loop invariant as additional parameters.
  , fixpointImplicitParams :: [Some (W4.SymExpr sym)]

    -- | A special memory region number that does not correspond to any valid block.
    --   This is intended to model values the block portion of bitvector values that
    --   get clobbered by the loop body, but do not represent loop-carried dependencies.
  , fixpointHavocBlock :: W4.SymNat sym
  }

-- | A variable substitution is used to track metadata regarding the discovered
--   loop-carried dependencies of a loop.
data VariableSubst sym =
  VarSubst
  { varSubst :: MapF (W4.SymExpr sym) (InvariantEntry sym)
    -- ^ The @varSubst@ associates to each "join variable" an @InvariantEntry@,
    --   that descibes the initial value the variable had, and the value computed
    --   for it after a loop iteration.

  , varHavoc :: MapF (W4.SymExpr sym) (Const ())
    -- ^ The @varHavoc@ map is essentially just a set of "join variables" for which
    --   we were not able to compute a coherent value across the loop boundary.
    --   Such variables are considered to be "junk" at the beginning of the loop,
    --   and do not participate in the loop invariant. This usually arises from
    --   temporary scratch space used in the loop body.
  }


-- | A memory region is used to describe a contiguous sequence of bytes
--   which is of known size, and which is at a known, concrete, offset
--   from a "master" offset. In a given regualar memory block, these
--   regions are required to be disjoint.
data MemoryRegion sym =
  forall w. (1 <= w) =>
  MemoryRegion
  { regionOffset  :: BV.BV 64 -- ^ Offset of the region, from the base pointer
  , regionSize    :: C.Bytes  -- ^ Length of the memory region, in bytes
  , regionStorage :: C.StorageType -- ^ The storage type used to write to this region
  , regionJoinVar :: W4.SymBV sym w -- ^ The join variable representing this region
  }

-- | Memory block data are used to describe where in memory
--   loop-carried dependencies are.  They may either be
--   "regular" blocks or "array" blocks. A regular block
--   consists of a collection of regions of known size, each
--   of which is at some concretely-known offset from a single
--   master offset value inside the LLVM memory region.
--   An array block consists of an entire LLVM memory region
--   that is backed by an SMT array.
data MemoryBlockData sym where
  RegularBlock ::
    W4.SymBV sym 64
      {- ^ A potentially symbolic base pointer/offset. All the
           offsets in this region are required to be at a concrete
           distance from this base pointer. -} ->
    Map Natural (MemoryRegion sym)
      {- ^ mapping from offset values to regions -} ->
    MemoryBlockData sym

  ArrayBlock   ::
    W4.SymExpr sym ArrayTp {- ^ array join variable -} ->
    W4.SymBV sym 64 {- ^ length of the allocation -} ->
    MemoryBlockData sym

type ArrayTp = W4.BaseArrayType (C.EmptyCtx C.::> W4.BaseBVType 64) (W4.BaseBVType 8)

-- | A memory substitution gives memory block data for
--   concrete memory region numbers of writes occurring
--   in the loop body. This is used to determine where
--   in memory the relevant values are that need to be
--   passed to the loop invariant.
newtype MemorySubstitution sym =
  MemSubst
  { memSubst :: Map Natural (MemoryBlockData sym)
      {- ^ Mapping from block numbers to block data -}
  }


fixpointRecord ::
  FixpointState p sym ext rtp blocks ->
  Maybe (FixpointRecord p sym ext rtp blocks)
fixpointRecord BeforeFixpoint = Nothing
fixpointRecord (ComputeFixpoint _ r) = Just r
fixpointRecord (CheckFixpoint r) = Just r


-- The fixpoint monad is used to ease the process of computing variable widenings
-- and such.  The included "SymNat" is a memory region number guaranteed not
-- to be a valid memory region; it is used to implement "havoc" registers that
-- we expect to be junk/scratch space across the loop boundary.
-- The state component tracks the variable substitution we are computing.
newtype FixpointMonad sym a =
  FixpointMonad (ReaderT (W4.SymNat sym) (StateT (VariableSubst sym) IO) a)
 deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

deriving instance MonadReader (W4.SymNat sym) (FixpointMonad sym)
deriving instance MonadState (VariableSubst sym) (FixpointMonad sym)

runFixpointMonad ::
  W4.SymNat sym ->
  VariableSubst sym ->
  FixpointMonad sym a ->
  IO (a, VariableSubst sym)
runFixpointMonad havoc_blk subst (FixpointMonad m) =
  runStateT (runReaderT m havoc_blk) subst

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
joinRegEntry sym left right = do
 subst <- get
 case C.regType left of
  C.LLVMPointerRepr w

      -- TODO! This is a "particularly guesome hack" it would be nice to find some better
      --  way to handle this situation.
      -- special handling for "don't care" registers coming from Macaw
    | List.isPrefixOf "cmacaw_reg" (show $ W4.printSymNat $ C.llvmPointerBlock (C.regValue left))
    , List.isPrefixOf "cmacaw_reg" (show $ W4.printSymExpr $ C.llvmPointerOffset (C.regValue left)) -> do
      -- liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: cmacaw_reg"
      return left

    | C.llvmPointerBlock (C.regValue left) == C.llvmPointerBlock (C.regValue right)
    , Nothing <- MapF.lookup (C.llvmPointerOffset (C.regValue left)) (varHavoc subst) -> do
      -- liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: LLVMPointerRepr"
      if isJust (W4.testEquality (C.llvmPointerOffset (C.regValue left)) (C.llvmPointerOffset (C.regValue right)))
      then do
        -- liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: LLVMPointerRepr: left == right"
        return left
      else case MapF.lookup (C.llvmPointerOffset (C.regValue left)) (varSubst subst) of
        Just join_entry -> do
          -- liftIO $ ?logMessage $
          --   "SimpleLoopInvariant.joinRegEntry: LLVMPointerRepr: Just: "
          --   ++ show (W4.printSymExpr $ bodyValue join_entry)
          --   ++ " -> "
          --   ++ show (W4.printSymExpr $ C.llvmPointerOffset (C.regValue right))
          put $ subst{ varSubst =
            MapF.insert
              (C.llvmPointerOffset (C.regValue left))
              (join_entry { bodyValue = C.llvmPointerOffset (C.regValue right) })
              (varSubst subst) }
          return left
        Nothing -> do
          liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: LLVMPointerRepr: Nothing"
          join_variable <- liftIO $ W4.freshConstant sym
                             (W4.safeSymbol "reg_join_var") (W4.BaseBVRepr w)
          let join_entry = InvariantEntry
                { headerValue = C.llvmPointerOffset (C.regValue left)
                , bodyValue = C.llvmPointerOffset (C.regValue right)
                }
          put $ subst{ varSubst = MapF.insert join_variable join_entry (varSubst subst) }
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer (C.llvmPointerBlock (C.regValue left)) join_variable

    | otherwise -> do
      liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: LLVMPointerRepr, unequal blocks!"
      havoc_blk <- ask
      case MapF.lookup (C.llvmPointerOffset (C.regValue left)) (varSubst subst) of
        Just _ -> do
          -- widening varible already present in the var substitition.
          -- we need to remove it, and add it to the havoc map instead
          put subst { varSubst = MapF.delete (C.llvmPointerOffset (C.regValue left)) (varSubst subst)
                    , varHavoc = MapF.insert (C.llvmPointerOffset (C.regValue left)) (Const ()) (varHavoc subst)
                    }
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer havoc_blk (C.llvmPointerOffset (C.regValue left))

        Nothing -> do
          havoc_var <- liftIO $ W4.freshConstant sym (W4.safeSymbol "havoc_var") (W4.BaseBVRepr w)
          put subst{ varHavoc = MapF.insert havoc_var (Const ()) (varHavoc subst) }
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer havoc_blk havoc_var

  C.BoolRepr
    | List.isPrefixOf "cmacaw" (show $ W4.printSymExpr $ C.regValue left) -> do
      liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: cmacaw_reg"
      return left
    | otherwise -> do
      -- liftIO $ ?logMessage $
      --   "SimpleLoopInvariant.joinRegEntry: BoolRepr:"
      --   ++ show (W4.printSymExpr $ C.regValue left)
      --   ++ " \\/ "
      --   ++ show (W4.printSymExpr $ C.regValue right)
      join_varaible <- liftIO $ W4.freshConstant sym (W4.safeSymbol "reg_join_var") W4.BaseBoolRepr
      return $ C.RegEntry C.BoolRepr join_varaible

  C.StructRepr field_types -> do
    -- liftIO $ ?logMessage "SimpleLoopInvariant.joinRegEntry: StructRepr"
    C.RegEntry (C.regType left) <$> fmapFC (C.RV . C.regValue) <$> joinRegEntries sym
      (Ctx.generate (Ctx.size field_types) $ \i ->
        C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue left) Ctx.! i)
      (Ctx.generate (Ctx.size field_types) $ \i ->
        C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue right) Ctx.! i)
  _ -> fail $ "SimpleLoopInvariant.joinRegEntry: unsupported type: " ++ show (C.regType left)


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
  (MapF (W4.SymExpr sym) (W4.SymExpr sym)) ->
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
  _ -> error $ unlines [ "SimpleLoopInvariant.applySubstitutionRegEntry"
                       , "unsupported type: " ++ show (C.regType entry)
                       ]


loadMemJoinVariables ::
  (C.IsSymBackend sym bak, C.HasPtrWidth 64, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  bak ->
  C.MemImpl sym ->
  MemorySubstitution sym ->
  IO (MapF (W4.SymExpr sym) (W4.SymExpr sym))
loadMemJoinVariables bak mem (MemSubst subst) = do
  let sym = C.backendGetSym bak

  vars <- forM (Map.toAscList subst) $ \ (blk, blkData) ->
            case blkData of
              ArrayBlock arr_var _sz ->
                do base_ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 0)
                   res <- C.asMemAllocationArrayStore sym ?ptrWidth base_ptr (C.memImplHeap mem)
                   case res of
                     Nothing -> fail $ "Expected SMT array in memory image for block number: " ++ show blk
                     Just (_ok, arr, _len2) ->
                       -- TODO: we need to assert the load condition...
                       -- TODO? Should we assert the lengths match?

                       return [MapF.Pair arr_var arr]

              RegularBlock basePtr offsetMap ->
                forM (Map.toAscList offsetMap) $
                  \ (_off , MemoryRegion{ regionJoinVar = join_var, regionStorage = storage_type, regionOffset = offBV }) ->
                    do blk' <- W4.natLit sym blk
                       off' <- W4.bvAdd sym basePtr =<< W4.bvLit sym ?ptrWidth offBV
                       let ptr = C.LLVMPointer blk' off'
                       val <- safeBVLoad sym mem ptr storage_type join_var C.noAlignment
                       return (MapF.Pair join_var val)

  return (MapF.fromList (concat vars))


safeBVLoad ::
  ( C.IsSymInterface sym, C.HasPtrWidth wptr, C.HasLLVMAnn sym
  , ?memOpts :: C.MemOptions, 1 <= w ) =>
  sym ->
  C.MemImpl sym ->
  C.LLVMPtr sym wptr {- ^ pointer to load from      -} ->
  C.StorageType      {- ^ type of value to load     -} ->
  W4.SymBV sym w     {- ^ default value to return -} ->
  C.Alignment        {- ^ assumed pointer alignment -} ->
  IO (C.RegValue sym (C.BVType w))
safeBVLoad sym mem ptr st def align =
  do let w = W4.bvWidth def
     pval <- C.loadRaw sym mem ptr st align
     case pval of
       C.Err _ -> return def
       C.NoErr p v ->
         do v' <- C.unpackMemValue sym (C.LLVMPointerRepr w) v
            p0 <- W4.natEq sym (C.llvmPointerBlock v') =<< W4.natLit sym 0
            p' <- W4.andPred sym p p0
            W4.bvIte sym p' (C.llvmPointerOffset v') def

storeMemJoinVariables ::
  (C.IsSymBackend sym bak, C.HasPtrWidth 64, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  bak ->
  C.MemImpl sym ->
  MemorySubstitution sym ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  IO (C.MemImpl sym)
storeMemJoinVariables bak mem (MemSubst mem_subst) eq_subst =
  foldlM
     (\mem_acc (blk, blk_data) ->
        case blk_data of
          RegularBlock basePtr off_map ->
            foldlM (writeMemRegion blk basePtr) mem_acc (Map.toAscList off_map)
          ArrayBlock arr len ->
            do base_ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 0)
               let arr' = MapF.findWithDefault arr arr eq_subst
               C.doArrayStore bak mem_acc base_ptr C.noAlignment arr' len)
     mem
     (Map.toAscList mem_subst)

 where
  sym = C.backendGetSym bak

  writeMemRegion blk basePtr mem_acc (_off, MemoryRegion{ regionJoinVar = join_var, regionStorage = storage_type, regionOffset = offBV }) =
    do blk' <- W4.natLit sym blk
       off' <- W4.bvAdd sym basePtr =<< W4.bvLit sym ?ptrWidth offBV
       let ptr = C.LLVMPointer blk' off'
       C.doStore bak mem_acc ptr (C.LLVMPointerRepr $ W4.bvWidth join_var) storage_type C.noAlignment =<<
         C.llvmPointer_bv sym (MapF.findWithDefault join_var join_var eq_subst)



dropMemStackFrame :: C.IsSymInterface sym => C.MemImpl sym -> (C.MemImpl sym, C.MemAllocs sym, C.MemWrites sym)
dropMemStackFrame mem = case (C.memImplHeap mem) ^. C.memState of
  (C.StackFrame _ _ _ (a, w) s) -> ((mem { C.memImplHeap = (C.memImplHeap mem) & C.memState .~ s }), a, w)
  _ -> C.panic "SimpleLoopInvariant.dropMemStackFrame" ["not a stack frame:", show (C.ppMem $ C.memImplHeap mem)]


filterSubstitution ::
  C.IsSymInterface sym =>
  sym ->
  VariableSubst sym ->
  VariableSubst sym
filterSubstitution sym (VarSubst substitution havoc) =
  -- TODO: fixpoint
  let uninterp_constants = foldMapF
        (Set.map (C.mapSome $ W4.varExpr sym) . W4.exprUninterpConstants sym . bodyValue)
        substitution
  in
  VarSubst
    (MapF.filterWithKey (\variable _entry -> Set.member (C.Some variable) uninterp_constants) substitution)
    havoc

-- find widening variables that are actually the same (up to syntactic equality)
-- and can be substituted for each other
uninterpretedConstantEqualitySubstitution ::
  forall sym .
  C.IsSymInterface sym =>
  sym ->
  VariableSubst sym ->
  (VariableSubst sym, MapF (W4.SymExpr sym) (W4.SymExpr sym))
uninterpretedConstantEqualitySubstitution _sym (VarSubst substitution havoc) =
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
  (VarSubst normal_substitution havoc, uninterpreted_constant_substitution)


-- | Given the WTO analysis results, find the nth loop.
--   Return the identifier of the loop header, and a list of all the blocks
--   that are part of the loop body. It is at this point that we check
--   that the loop has the necessary properties; there must be a single
--   entry point to the loop, and it must have a single back-edge. Otherwise,
--   the analysis will not work correctly.
computeLoopBlocks :: forall ext blocks init ret k. (k ~ C.Some (C.BlockID blocks)) =>
  C.CFG ext blocks init ret ->
  Integer ->
  IO (k, [k])
computeLoopBlocks cfg loopNum =
  case List.genericDrop loopNum (Map.toList loop_map) of
    [] -> fail ("Did not find " ++ show loopNum ++ " loop headers")
    (p:_) -> do checkSingleEntry p
                checkSingleBackedge p
                return p

 where
  -- There should be exactly one block which is not part of the loop body that
  -- can jump to @hd@.
  checkSingleEntry :: (k,[k]) -> IO ()
  checkSingleEntry (hd, body) =
    case filter (\x -> not (elem x body) && elem hd (C.cfgSuccessors cfg x)) allReachable of
      [_] -> return ()
      _   -> fail "SimpleLoopInvariant feature requires a single-entry loop!"

  -- There should be exactly on block in the loop body which can jump to @hd@.
  checkSingleBackedge :: (k,[k]) -> IO ()
  checkSingleBackedge (hd, body) =
    case filter (\x -> elem hd (C.cfgSuccessors cfg x)) body of
      [_] -> return ()
      _   -> fail "SimpleLoopInvariant feature requires a loop with a single backedge!"

  flattenWTOComponent = \case
    C.SCC C.SCCData{..} ->  wtoHead : concatMap flattenWTOComponent wtoComps
    C.Vertex v -> [v]

  loop_map = Map.fromList $ mapMaybe
    (\case
      C.SCC C.SCCData{..} -> Just (wtoHead, wtoHead : concatMap flattenWTOComponent wtoComps)
      C.Vertex{} -> Nothing)
    wto

  allReachable = concatMap flattenWTOComponent wto

  wto = C.cfgWeakTopologicalOrdering cfg


-- | This execution feature is designed to allow a limited form of
--   verification for programs with unbounded looping structures.
--
--   It is currently highly experimental and has many limititations.
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
--   providing a \"fixpoint function\" which describes how the live
--   values in the loop at an arbitrary iteration are used to compute
--   the final values of those variables before execution leaves the
--   loop. The number and order of these variables depends on
--   internal details of the representation, so is relatively fragile.
simpleLoopInvariant ::
  forall sym ext p rtp blocks init ret .
  (C.IsSymInterface sym, C.IsSyntaxExtension ext, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  Integer {- ^ which of the discovered loop heads to install a loop invariant onto -}  -> 
  C.CFG ext blocks init ret {- ^ The function we want to verify -} ->
  C.GlobalVar C.Mem {- ^ global variable representing memory -} ->
  (InvariantPhase -> [Some (W4.SymExpr sym)] -> MapF (W4.SymExpr sym) (InvariantEntry sym) -> IO (W4.Pred sym)) ->
  IO (C.ExecutionFeature p sym ext rtp)
simpleLoopInvariant sym loopNum cfg@C.CFG{..} mem_var loop_invariant = do
  -- TODO, can we lift this restriction to 64-bits? I don't think there
  -- is anything fundamental about it.
  let ?ptrWidth = knownNat @64

  verbSetting <- W4.getOptionSetting W4.verbosity $ W4.getConfiguration sym
  verb <- fromInteger <$> W4.getOpt verbSetting

  (loop_header, loop_body_blocks) <- computeLoopBlocks cfg loopNum

  fixpoint_state_ref <- newIORef @(FixpointState p sym ext rtp blocks) BeforeFixpoint

  --putStrLn "Setting up simple loop fixpoints feature."
  --putStrLn ("WTO: " ++ show (C.cfgWeakTopologicalOrdering cfg))

  return $ C.ExecutionFeature $ \exec_state -> do
    let ?logMessage = \msg -> when (verb >= (3 :: Natural)) $ do
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

          -- is this state at thea loop header?
        , C.Some block_id == loop_header ->

            advanceFixpointState bak mem_var loop_invariant block_id sim_state fixpoint_state fixpoint_state_ref

        | otherwise -> do
            ?logMessage $ "SimpleLoopInvariant: RunningState: RunBlockStart: " ++ show block_id ++ " " ++ show (C.frameHandle (sim_state ^. C.stateCrucibleFrame))
            return C.ExecutionFeatureNoChange

      C.SymbolicBranchState branch_condition true_frame false_frame _target sim_state
          | Just _fixpointRecord <- fixpointRecord fixpoint_state
          , JustPausedFrameTgtId true_frame_some_block_id <- pausedFrameTgtId true_frame
          , JustPausedFrameTgtId false_frame_some_block_id <- pausedFrameTgtId false_frame
          , C.SomeHandle cfgHandle == C.frameHandle (sim_state ^. C.stateCrucibleFrame)
          , Just Refl <- W4.testEquality
              (fmapFC C.blockInputs cfgBlockMap)
              (fmapFC C.blockInputs $ C.frameBlockMap $ sim_state ^. C.stateCrucibleFrame)
          , elem true_frame_some_block_id loop_body_blocks /=
              elem false_frame_some_block_id loop_body_blocks -> do

            (loop_condition, inside_loop_frame) <-
              if elem true_frame_some_block_id loop_body_blocks
              then
                return (branch_condition, true_frame)
              else do
                not_branch_condition <- W4.notPred sym branch_condition
                return (not_branch_condition, false_frame)

            case fixpoint_state of
              BeforeFixpoint -> C.panic "SimpleLoopInvariant.simpleLoopInvariant:" ["BeforeFixpoint"]

              ComputeFixpoint _assumeIdent _fixpoint_record -> do
                -- continue in the loop
                ?logMessage $ "SimpleLoopInvariant: SymbolicBranchState: ComputeFixpoint"

                loc <- W4.getCurrentProgramLoc sym
                C.addAssumption bak $ C.BranchCondition loc (C.pausedLoc inside_loop_frame) loop_condition

                C.ExecutionFeatureNewState <$>
                  runReaderT
                    (C.resumeFrame (C.forgetPostdomFrame inside_loop_frame) $ sim_state ^. (C.stateTree . C.actContext))
                    sim_state

              CheckFixpoint _fixpoint_record -> do
                ?logMessage $ "SimpleLoopInvariant: SymbolicBranchState: CheckFixpoint"

                return C.ExecutionFeatureNoChange

      _ -> return C.ExecutionFeatureNoChange


advanceFixpointState ::
  forall sym bak ext p rtp blocks r args .
  (C.IsSymBackend sym bak, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions, ?logMessage :: String -> IO ()) =>
  bak ->
  C.GlobalVar C.Mem ->
  (InvariantPhase -> [Some (W4.SymExpr sym)] -> MapF (W4.SymExpr sym) (InvariantEntry sym) -> IO (W4.Pred sym)) ->
  C.BlockID blocks args ->
  C.SimState p sym ext rtp (C.CrucibleLang blocks r) ('Just args) ->
  FixpointState p sym ext rtp blocks ->
  IORef (FixpointState p sym ext rtp blocks) ->
  IO (C.ExecutionFeatureResult p sym ext rtp)

advanceFixpointState bak mem_var loop_invariant block_id sim_state fixpoint_state fixpoint_state_ref = do
  let ?ptrWidth = knownNat @64
  let sym = C.backendGetSym bak
  loc <- W4.getCurrentProgramLoc sym
  case fixpoint_state of
    BeforeFixpoint -> do
      ?logMessage $ "SimpleLoopInvariant: RunningState: BeforeFixpoint -> ComputeFixpoint " ++ show block_id ++ " " ++ show (pretty (W4.plSourceLoc loc))
      assumption_frame_identifier <- C.pushAssumptionFrame bak
      let mem_impl = case C.lookupGlobal mem_var (sim_state ^. C.stateGlobals) of
                       Just m -> m
                       Nothing -> C.panic "SimpleLoopInvariant.advanceFixpointState"
                                          ["LLVM Memory variable not found!"]
      let res_mem_impl = mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" $ C.memImplHeap mem_impl }

--      ?logMessage $ "SimpleLoopInvariant: start memory\n" ++ (show (C.ppMem (C.memImplHeap mem_impl)))

      -- Get a fresh block value that doesn't correspond to any valid memory region
      havoc_blk <- W4.natLit sym =<< C.nextBlock (C.memImplBlockSource mem_impl)

      writeIORef fixpoint_state_ref $ ComputeFixpoint assumption_frame_identifier $
        FixpointRecord
        { fixpointBlockId = block_id
        , fixpointSubstitution = VarSubst MapF.empty MapF.empty
        , fixpointRegMap = sim_state ^. (C.stateCrucibleFrame . C.frameRegs)
        , fixpointMemSubstitution = MemSubst mempty
        , fixpointInitialSimState = sim_state
        , fixpointImplicitParams = []
        , fixpointHavocBlock = havoc_blk
        }
      return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
        sim_state & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

    ComputeFixpoint assumeFrame fixpoint_record
      | FixpointRecord { fixpointRegMap = reg_map
                       , fixpointInitialSimState = initSimState
                       , fixpointHavocBlock = havoc_blk
                       }
           <- fixpoint_record
      , Just Refl <- W4.testEquality
          (fmapFC C.regType $ C.regMap reg_map)
          (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do


        ?logMessage $ "SimpleLoopInvariant: RunningState: ComputeFixpoint: " ++ show block_id
        _ <- C.popAssumptionFrameAndObligations bak assumeFrame

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
        let (header_mem_impl, mem_allocs, mem_writes) = dropMemStackFrame body_mem_impl
        when (C.sizeMemAllocs mem_allocs /= 0) $
          fail "SimpleLoopInvariant: unsupported memory allocation in loop body."

        -- widen the inductive condition
        ((join_reg_map,mem_substitution), join_substitution) <-
            runFixpointMonad havoc_blk (fixpointSubstitution fixpoint_record) $
               do join_reg_map <- joinRegEntries sym
                                    (C.regMap reg_map)
                                    (C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs))
                  mem_substitution <- computeMemSubstitution sym fixpoint_record mem_writes
                  return (join_reg_map, mem_substitution)

        -- check if we are done; if we did not introduce any new variables, we don't have to widen any more
        if MapF.keys (varSubst join_substitution) ==
           MapF.keys (varSubst (fixpointSubstitution fixpoint_record))

          -- we found the fixpoint, get ready to wrap up
          then do
            ?logMessage $
              "SimpleLoopInvariant: RunningState: ComputeFixpoint -> CheckFixpoint "
              ++ " " ++ show (pretty (W4.plSourceLoc loc))
            -- we have delayed populating the main substitution map with
            --  memory variables, so we have to do that now

            header_mem_substitution <- loadMemJoinVariables bak header_mem_impl $
              fixpointMemSubstitution fixpoint_record
            body_mem_substitution <- loadMemJoinVariables bak body_mem_impl $
              fixpointMemSubstitution fixpoint_record

            -- try to unify widening variables that have the same values
            let (normal_substitution, equality_substitution) =
                  uninterpretedConstantEqualitySubstitution sym $
                  -- drop variables that don't appear along some back edge (? understand this better)
                  filterSubstitution sym $
                  join_substitution
                  { varSubst = 
                    MapF.union (varSubst join_substitution) $
                    -- this implements zip, because the two maps have the same keys
                    MapF.intersectWithKeyMaybe
                      (\_k x y -> Just $ InvariantEntry{ headerValue = x, bodyValue = y })
                      header_mem_substitution
                      body_mem_substitution
                  }
--            ?logMessage $ "normal_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList (varSubst normal_substitution))
--            ?logMessage $ "equality_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList equality_substitution)
--            ?logMessage $ "havoc variables: " ++ show (map (\(MapF.Pair x _) -> W4.printSymExpr x) $ MapF.toList (varHavoc normal_substitution))

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
                            -- filter out the special "noSatisfyingWrite" boolean constants
                            -- that are generated as part of the LLVM memory model
                            Set.filter ( \ (C.Some x) ->
                                           not (List.isPrefixOf "cnoSatisfyingWrite"
                                                (show $ W4.printSymExpr x))) $
                            Set.map (\ (C.Some x) -> C.Some (W4.varExpr sym x)) $
                              (W4.exprUninterpConstants sym (bodyValue e)))
                       (MapF.toList (varSubst normal_substitution)))
                    (Set.fromList (MapF.keys (varSubst normal_substitution)))

            ?logMessage $ unlines $
              ["Implicit parameters!"] ++
              map (\ (C.Some x) -> show (W4.printSymExpr x)) implicit_params

            -- == assert the loop invariant on the initial values ==

            -- build a map where the current value is equal to the initial value
            let init_state_map = MapF.map (\e -> e{ bodyValue = headerValue e })
                                          (varSubst normal_substitution)
            -- construct the loop invariant
            initial_loop_invariant <- loop_invariant InitialInvariant implicit_params init_state_map
            -- assert the loop invariant as an obligation
            C.addProofObligation bak
               $ C.LabeledPred initial_loop_invariant
               $ C.SimError loc "initial loop invariant"

            -- == assume the loop invariant on the arbitrary state ==

            -- build a map where the current value is equal to the widening variable
            let hyp_state_map = MapF.mapWithKey (\k e -> e{ bodyValue = k })
                                                (varSubst normal_substitution)
            -- construct the loop invariant to assume at the loop head
            hypothetical_loop_invariant <- loop_invariant HypotheticalInvariant implicit_params hyp_state_map
            -- assume the loop invariant
            C.addAssumption bak
              $ C.GenericAssumption loc "loop head invariant"
                hypothetical_loop_invariant

            -- == set up the state with arbitrary values to run the loop body ==

            writeIORef fixpoint_state_ref $
              CheckFixpoint
                FixpointRecord
                { fixpointBlockId = block_id
                , fixpointSubstitution = normal_substitution
                , fixpointRegMap = C.RegMap res_reg_map
                , fixpointMemSubstitution = mem_substitution
                , fixpointInitialSimState = initSimState
                , fixpointImplicitParams = implicit_params
                , fixpointHavocBlock = havoc_blk
                }

            -- Continue running from the loop header starting from an arbitrary state satisfying
            -- the loop invariant.
            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              initSimState & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap res_reg_map
                & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

          else do
            -- Otherwise, we are still working on finding all the loop-carried dependencies
            ?logMessage $
              "SimpleLoopInvariant: RunningState: ComputeFixpoint: -> ComputeFixpoint"
            assumption_frame_identifier <- C.pushAssumptionFrame bak

            -- write any new widening variables into memory state
            res_mem_impl <- storeMemJoinVariables bak
              (header_mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" (C.memImplHeap header_mem_impl) })
              mem_substitution
              MapF.empty

            writeIORef fixpoint_state_ref $
              ComputeFixpoint assumption_frame_identifier $
              FixpointRecord
              { fixpointBlockId = block_id
              , fixpointSubstitution = join_substitution
              , fixpointRegMap = C.RegMap join_reg_map
              , fixpointMemSubstitution = mem_substitution
              , fixpointInitialSimState = initSimState
              , fixpointImplicitParams = []
              , fixpointHavocBlock = havoc_blk
              }
            return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
              initSimState & (C.stateCrucibleFrame . C.frameRegs) .~ C.RegMap join_reg_map
                & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

      | otherwise -> C.panic "SimpleLoopInvariant.simpleLoopInvariant" ["type mismatch: ComputeFixpoint"]

    CheckFixpoint fixpoint_record
      | FixpointRecord { fixpointRegMap = reg_map } <- fixpoint_record
      , Just Refl <- W4.testEquality
          (fmapFC C.regType $ C.regMap reg_map)
          (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do
        ?logMessage $
          "SimpleLoopInvariant: RunningState: "
          ++ "CheckFixpoint"
          ++ " -> "
          ++ "AfterFixpoint"
          ++ ": "
          ++ show block_id
          ++ " " ++ show (pretty (W4.plSourceLoc loc))

        -- == assert the loop invariant and abort ==

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)

        body_mem_substitution <- loadMemJoinVariables bak body_mem_impl $ fixpointMemSubstitution fixpoint_record
        let res_substitution = MapF.mapWithKey
              (\variable fixpoint_entry ->
                fixpoint_entry
                  { bodyValue = MapF.findWithDefault (bodyValue fixpoint_entry) variable body_mem_substitution
                  })
              (varSubst (fixpointSubstitution fixpoint_record))
        -- ?logMessage $ "res_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList res_substitution)

        invariant_pred <- loop_invariant InductiveInvariant (fixpointImplicitParams fixpoint_record) res_substitution
        C.addProofObligation bak $ C.LabeledPred invariant_pred $ C.SimError loc "loop invariant"
        -- ?logMessage $ "fixpoint_func_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList fixpoint_func_substitution)
        return $ C.ExecutionFeatureModifiedState $ C.AbortState (C.InfeasibleBranch loc) sim_state

      | otherwise -> C.panic "SimpleLoopInvariant.simpleLoopInvariant" ["type mismatch: CheckFixpoint"]



constructMemSubstitutionCandidate :: forall sym.
  (?logMessage :: String -> IO (), C.IsSymInterface sym) =>
  C.IsSymInterface sym =>
  sym ->
  C.MemWrites sym ->
  IO (MemorySubstitution sym)
constructMemSubstitutionCandidate sym mem_writes =
  case mem_writes of
    C.MemWrites [C.MemWritesChunkIndexed mmm] ->
      MemSubst <$> foldlM handleMemWrite mempty (List.concat $ IntMap.elems mmm)

    -- no writes occured in the body of the loop
    C.MemWrites [] ->
      return (MemSubst mempty)

    _ -> fail $ "SimpleLoopInvariant: not MemWritesChunkIndexed: " ++
                show (C.ppMemWrites mem_writes)

 where
   updateOffsetMap ::
     Natural ->
     W4.SymBV sym 64 ->
     C.LLVMPtr sym 64 ->
     C.StorageType ->
     Map Natural (MemoryRegion sym) ->
     IO (Map Natural (MemoryRegion sym))
   updateOffsetMap blk basePtr ptr storage_type off_map =
     do diff <- W4.bvSub sym (C.llvmPointerOffset ptr) basePtr
        case W4.asBV diff of
          Nothing ->
            fail $ unlines
              [ "SimpleLoopInvariant: incompatible base pointers for writes to a memory region " ++ show blk
              , show (W4.printSymExpr basePtr)
              , show (W4.printSymExpr (C.llvmPointerOffset ptr))
              ]
          Just off ->
            do let sz = C.typeEnd 0 storage_type
               case Map.lookup (BV.asNatural off) off_map of
                 Just rgn
                   | regionSize rgn == sz -> return off_map
                   | otherwise ->
                       fail $ unlines
                         [ "Memory region written at incompatible storage types"
                         , show (regionStorage rgn) ++ " vs" ++ show storage_type
                         , show (C.ppPtr ptr)
                         ]
                 Nothing ->
                   case W4.mkNatRepr $ C.bytesToBits sz of
                     C.Some bv_width
                       | Just C.LeqProof <- W4.testLeq (W4.knownNat @1) bv_width -> do
                         join_var <- W4.freshConstant sym
                           (W4.safeSymbol ("mem_join_var_" ++ show blk ++ "_" ++ show (BV.asNatural off)))
                           (W4.BaseBVRepr bv_width)
                         let rgn = MemoryRegion
                                   { regionOffset  = off
                                   , regionSize    = sz
                                   , regionStorage = storage_type
                                   , regionJoinVar = join_var
                                   }
                         return (Map.insert (BV.asNatural off) rgn off_map)

                       | otherwise ->
                         C.panic
                           "SimpleLoopInvariant.simpleLoopInvariant"
                           ["unexpected storage type " ++ show storage_type ++ " of size " ++ show sz]


   handleMemWrite mem_subst wr =
     case wr of
       C.MemWrite ptr (C.MemArrayStore _arr (Just len))
         | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
         , Just Refl <- testEquality (knownNat @64) (W4.bvWidth len)
         -> case Map.lookup blk mem_subst of
              Just (ArrayBlock _ _) -> return mem_subst
              Just (RegularBlock _ _) ->
                fail $
                  "SimpleLoopInvariant: incompatible writes detected for block " ++ show blk
              Nothing ->
                do join_var <- liftIO $
                       W4.freshConstant sym
                         (W4.safeSymbol ("smt_array_join_var_" ++ show blk))
                         knownRepr
                   return (Map.insert blk (ArrayBlock join_var len) mem_subst)

       C.MemWrite ptr (C.MemStore _val storage_type _align)
        | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
        , Just Refl <- testEquality (knownNat @64) (W4.bvWidth (C.llvmPointerOffset ptr))
        -> do (basePtr, off_map) <-
                case Map.lookup blk mem_subst of
                  Just (ArrayBlock _ _) ->
                     fail $
                       "SimpleLoopInvariant: incompatible writes detected for block " ++
                       show blk
                  Just (RegularBlock basePtr off_map) -> return (basePtr, off_map)
                  Nothing -> return (C.llvmPointerOffset ptr, mempty)

              off_map' <- updateOffsetMap blk basePtr ptr storage_type off_map
              return (Map.insert blk (RegularBlock basePtr off_map') mem_subst)

       w -> fail $ unlines $
              [ "SimpleLoopInvariant: unable to handle memory write of the form:"
              , show (C.ppWrite w)
              ]

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
    mem_subst_candidate <- liftIO $ constructMemSubstitutionCandidate sym mem_writes

    -- Check the candidate and raise errors if we cannot handle the resulting widening
    res <- liftIO $ runExceptT $
             checkMemSubst sym (fixpointMemSubstitution fixpoint_record)
                               mem_subst_candidate

    case res of
      Left msg -> fail $ unlines $
        [ "SimpleLoopInvariant: failure constructing memory footprint for loop invariant"
        , msg
        ]
      Right x  -> return x


-- | This function checks that the computed candidate memory substitution is an acceptable
--   refinement of the original. For the moment, this is a very restrictive test; either
--   we have started with an empty substitution (e.g., on the first iteration), or we have
--   computed a substitution that is exactly compatible with the one we started with.
--
--   At some point, it may be necessary or desirable to allow more.
--
--   Note:, for this check we do not need to compare the identities of the actual join variables
--   found in the substitution, just that the memory regions (positions and sizes) are equal.
checkMemSubst :: forall sym.
  W4.IsSymExprBuilder sym =>
  sym ->
  MemorySubstitution sym ->
  MemorySubstitution sym ->
  ExceptT String IO (MemorySubstitution sym)
checkMemSubst sym orig candidate =
  if Map.null (memSubst orig)
    then return candidate
    else do checkCandidateEqual
            return orig

 where
   checkEqualMaps str f m1 m2 =
     do unless (Map.keysSet m1 == Map.keysSet m2)
               (throwError ("Key sets differ when checking " ++ str))
        forM_ (Map.assocs m1) $ \ (k,e1) ->
               case Map.lookup k m2 of
                 Just e2 -> f k e1 e2
                 Nothing -> throwError ("Key sets differ when checking " ++ str)

   checkCandidateEqual =
     checkEqualMaps "memory substitution" checkMBD
       (memSubst orig) (memSubst candidate)

   checkBVEq :: (1 <= w) => W4.SymBV sym w -> W4.SymBV sym w -> IO Bool
   checkBVEq x y =
      do diff <- W4.bvSub sym x y
         case BV.asUnsigned <$> W4.asBV diff of
           Just 0 -> return True
           _      -> return False

   checkMBD n (RegularBlock b1 rmap1) (RegularBlock b2 rmap2) =
      do ok <- liftIO $ checkBVEq b1 b2
         unless ok $ throwError $
               unlines  ["base pointers differ for region " ++ show n
                        , show (W4.printSymExpr b1)
                        , show (W4.printSymExpr b2)
                        ]
         checkEqualMaps ("region map for " ++ show n) (checkMemRegion n) rmap1 rmap2
   checkMBD n (ArrayBlock _a1 l1) (ArrayBlock _a2 l2) =
      do ok <- liftIO $ checkBVEq l1 l2
         unless ok $ throwError $
             unlines [ "array lengths differ for region " ++ show n
                     , show (W4.printSymExpr l1)
                     , show (W4.printSymExpr l2)
                     ]
   checkMBD n _ _ =
      throwError ("Regular block incompatible with array block in region " ++ show n)

   checkMemRegion :: Natural -> Natural -> MemoryRegion sym -> MemoryRegion sym -> ExceptT String IO ()
   checkMemRegion n o r1 r2 =
     do unless (regionOffset r1 == regionOffset r2)
               (throwError ("region offsets differ in region " ++ show n ++ " at " ++ show o))
        unless (regionSize r1 == regionSize r2)
               (throwError ("region sizes differ in region " ++ show n ++ " at " ++ show o))
        unless (regionStorage r1 == regionStorage r2)
               (throwError ("region storage types differ in region " ++ show n ++ " at " ++ show o))

data MaybePausedFrameTgtId f where
  JustPausedFrameTgtId :: C.Some (C.BlockID b) -> MaybePausedFrameTgtId (C.CrucibleLang b r)
  NothingPausedFrameTgtId :: MaybePausedFrameTgtId f

pausedFrameTgtId :: C.PausedFrame p sym ext rtp f -> MaybePausedFrameTgtId f
pausedFrameTgtId C.PausedFrame{ resume = resume } = case resume of
  C.ContinueResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  C.CheckMergeResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  _ -> NothingPausedFrameTgtId
