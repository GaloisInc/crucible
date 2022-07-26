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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


module Lang.Crucible.LLVM.SimpleLoopFixpoint2
  ( FixpointEntry(..)
  , InvariantPhase(..)
  , simpleLoopFixpoint
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
--import           Control.Monad.Trans.Maybe
import           Control.Monad.Except
--import           Data.Either
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

--import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4

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


-- | A datatype describing the reason we are building an instance
--   of the loop invariant.
data InvariantPhase
  = InitialInvariant
  | HypotheticalInvariant
  | InductiveInvariant

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
data FixpointEntry sym tp =
  FixpointEntry
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
  , fixpointSubstitution :: VariableSubst sym

  , fixpointMemSubstitution :: MemorySubstitution sym

    -- | Prestate values of the Crucible registers when the loop header is first encountered.
  , fixpointRegMap :: C.RegMap sym args

  , fixpointInitialSimState :: C.SimState p sym ext rtp (C.CrucibleLang blocks r) ('Just args)

  , fixpointImplicitParams :: [Some (W4.SymExpr sym)]

    -- | A special memory region number that does not correspond to any valid block.
    --   This is intended to model values the block portion of bitvector values that
    --   get clobbered by the loop body, but do not represent loop-carried dependencies.
  , fixpointHavocBlock :: W4.SymNat sym
  }

data MemoryRegion sym =
  forall w. (1 <= w) =>
  MemoryRegion
  { regionOffset  :: BV.BV 64 -- ^ Offset of the region, from the base pointer
  , regionSize    :: C.Bytes  -- ^ Length of the memory region, in bytes
  , regionStorage :: C.StorageType
  , regionJoinVar :: W4.SymBV sym w
  }

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

data VariableSubst sym =
  VarSubst
  { varSubst :: MapF (W4.SymExpr sym) (FixpointEntry sym)
  , varHavoc :: MapF (W4.SymExpr sym) (Const ())
  }

data MemorySubstitution sym =
  MemSubst
  { memSubst :: Map Natural (MemoryBlockData sym)
      {- ^ Mapping from block numbers to block data -}
  }

fixpointRecord ::
  FixpointState p sym ext rtp blocks ->
  Maybe (FixpointRecord p sym ext rtp blocks)
fixpointRecord BeforeFixpoint = Nothing
fixpointRecord (ComputeFixpoint r) = Just r
fixpointRecord (CheckFixpoint r) = Just r


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

      -- special handling for "don't care" registers coming from Macaw
    | List.isPrefixOf "cmacaw_reg" (show $ W4.printSymNat $ C.llvmPointerBlock (C.regValue left))
    , List.isPrefixOf "cmacaw_reg" (show $ W4.printSymExpr $ C.llvmPointerOffset (C.regValue left)) -> do
      liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: cmacaw_reg"
      return left

    | C.llvmPointerBlock (C.regValue left) == C.llvmPointerBlock (C.regValue right)
    , Nothing <- MapF.lookup (C.llvmPointerOffset (C.regValue left)) (varHavoc subst) -> do
      liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr"
      if isJust (W4.testEquality (C.llvmPointerOffset (C.regValue left)) (C.llvmPointerOffset (C.regValue right)))
      then do
        liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: left == right"
        return left
      else case MapF.lookup (C.llvmPointerOffset (C.regValue left)) (varSubst subst) of
        Just join_entry -> do
          -- liftIO $ ?logMessage $
          --   "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: Just: "
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
          liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: Nothing"
          join_varaible <- liftIO $ W4.freshConstant sym
                             (W4.safeSymbol "reg_join_var") (W4.BaseBVRepr w)
          let join_entry = FixpointEntry
                { headerValue = C.llvmPointerOffset (C.regValue left)
                , bodyValue = C.llvmPointerOffset (C.regValue right)
                }
          put $ subst{ varSubst = MapF.insert join_varaible join_entry (varSubst subst) }
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer (C.llvmPointerBlock (C.regValue left)) join_varaible

    | otherwise -> do
      liftIO $ ?logMessage "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr, unequal blocks!"
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

      {- block indexes might be different...
      fail $
        "SimpleLoopFixpoint.joinRegEntry: LLVMPointerRepr: unsupported pointer base join: "
        ++ show (C.ppPtr $ C.regValue left)
        ++ " \\/ "
        ++ show (C.ppPtr $ C.regValue right)
       -}

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
  _ -> C.panic "SimpleLoopFixpoint.applySubstitutionRegEntry" ["unsupported type: " ++ show (C.regType entry)]


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
  _ -> C.panic "SimpleLoopFixpoint.dropMemStackFrame" ["not a stack frame:", show (C.ppMem $ C.memImplHeap mem)]


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


computeLoopMap :: (k ~ C.Some (C.BlockID blocks)) => Integer -> [C.WTOComponent k] -> IO (Map k [k])
computeLoopMap loopNum wto =
  case List.genericDrop loopNum (Map.toList loop_map) of
    [] -> fail ("Did not find " ++ show loopNum ++ " loop headers")
    (p:_) -> return (Map.fromList [p])

  --return loop_map
  -- Doesn't really work if there are nested loops: loop datastructures will
  -- overwrite each other.  Currently no error message.

  -- Really only works for single-exit loops; need a message for that too.

 where
  flattenWTOComponent = \case
    C.SCC C.SCCData{..} ->  wtoHead : concatMap flattenWTOComponent wtoComps
    C.Vertex v -> [v]

  loop_map = Map.fromList $ mapMaybe
    (\case
      C.SCC C.SCCData{..} -> Just (wtoHead, wtoHead : concatMap flattenWTOComponent wtoComps)
      C.Vertex{} -> Nothing)
    wto


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
  Integer {- ^ which of the discovered loop heads to install a loop invariant onto -}  -> 
  C.CFG ext blocks init ret {- ^ The function we want to verify -} ->
  C.GlobalVar C.Mem {- ^ global variable representing memory -} ->
  (InvariantPhase -> [Some (W4.SymExpr sym)] -> MapF (W4.SymExpr sym) (FixpointEntry sym) -> IO (W4.Pred sym)) ->
  IO (C.ExecutionFeature p sym ext rtp)
simpleLoopFixpoint sym loopNum cfg@C.CFG{..} mem_var loop_invariant = do
  let ?ptrWidth = knownNat @64

  --verbSetting <- W4.getOptionSetting W4.verbosity $ W4.getConfiguration sym
  --verb <- fromInteger <$> W4.getOpt verbSetting

  loop_map <- computeLoopMap loopNum (C.cfgWeakTopologicalOrdering cfg)

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
          | Just FixpointRecord{ fixpointBlockId = fixpoint_block_id } <- fixpointRecord fixpoint_state
          , Just loop_body_some_block_ids <- Map.lookup (C.Some fixpoint_block_id) loop_map
          , JustPausedFrameTgtId true_frame_some_block_id <- pausedFrameTgtId true_frame
          , JustPausedFrameTgtId false_frame_some_block_id <- pausedFrameTgtId false_frame
          , C.SomeHandle cfgHandle == C.frameHandle (sim_state ^. C.stateCrucibleFrame)
          , Just Refl <- W4.testEquality
              (fmapFC C.blockInputs cfgBlockMap)
              (fmapFC C.blockInputs $ C.frameBlockMap $ sim_state ^. C.stateCrucibleFrame)
          , elem true_frame_some_block_id loop_body_some_block_ids /= elem false_frame_some_block_id loop_body_some_block_ids -> do

            (loop_condition, inside_loop_frame, _outside_loop_frame) <-
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
  (InvariantPhase -> [Some (W4.SymExpr sym)] -> MapF (W4.SymExpr sym) (FixpointEntry sym) -> IO (W4.Pred sym)) ->
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
      ?logMessage $ "SimpleLoopFixpoint: RunningState: BeforeFixpoint -> ComputeFixpoint " ++ show block_id ++ " " ++ show (pretty (W4.plSourceLoc loc))
      assumption_frame_identifier <- C.pushAssumptionFrame bak
      let mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
      let res_mem_impl = mem_impl { C.memImplHeap = C.pushStackFrameMem "fix" $ C.memImplHeap mem_impl }

--      ?logMessage $ "SimpleLoopFixpoint: start memory\n" ++ (show (C.ppMem (C.memImplHeap mem_impl)))

      -- Get a fresh block value that doesn't correspond to any valid memory region
      havoc_blk <- W4.natLit sym =<< C.nextBlock (C.memImplBlockSource mem_impl)

      writeIORef fixpoint_state_ref $ ComputeFixpoint $
        FixpointRecord
        { fixpointBlockId = block_id
        , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
        , fixpointSubstitution = VarSubst MapF.empty MapF.empty
        , fixpointRegMap = sim_state ^. (C.stateCrucibleFrame . C.frameRegs)
        , fixpointMemSubstitution = MemSubst mempty
        , fixpointInitialSimState = sim_state
        , fixpointImplicitParams = []
        , fixpointHavocBlock = havoc_blk
        }
      return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
        sim_state & C.stateGlobals %~ C.insertGlobal mem_var res_mem_impl

    ComputeFixpoint fixpoint_record
      | FixpointRecord { fixpointRegMap = reg_map
                       , fixpointInitialSimState = initSimState
                       , fixpointHavocBlock = havoc_blk
                       }
           <- fixpoint_record
      , Just Refl <- W4.testEquality
          (fmapFC C.regType $ C.regMap reg_map)
          (fmapFC C.regType $ C.regMap $ sim_state ^. (C.stateCrucibleFrame . C.frameRegs)) -> do


        ?logMessage $ "SimpleLoopFixpoint: RunningState: ComputeFixpoint: " ++ show block_id
        _ <- C.popAssumptionFrameAndObligations bak $
              fixpointAssumptionFrameIdentifier fixpoint_record

        let body_mem_impl = fromJust $ C.lookupGlobal mem_var (sim_state ^. C.stateGlobals)
        let (header_mem_impl, mem_allocs, mem_writes) = dropMemStackFrame body_mem_impl
        when (C.sizeMemAllocs mem_allocs /= 0) $
          fail "SimpleLoopFixpoint: unsupported memory allocation in loop body."

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
              "SimpleLoopFixpoint: RunningState: ComputeFixpoint -> CheckFixpoint "
              ++ " " ++ show (pretty (W4.plSourceLoc loc))
            -- we have delayed populating the main substituation map with
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
                      (\_k x y -> Just $ FixpointEntry{ headerValue = x, bodyValue = y })
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
                , fixpointAssumptionFrameIdentifier = undefined --assumption_frame_identifier
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
              , fixpointHavocBlock = havoc_blk
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

      | otherwise -> C.panic "SimpleLoopFixpoint.simpleLoopFixpoint" ["type mismatch: CheckFixpoint"]



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

    _ -> fail $ "SimpleLoopFixpoint: not MemWritesChunkIndexed: " ++
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
              [ "SimpleLoopFixpoint: incompatible base pointers for writes to a memory region " ++ show blk
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
                           "SimpleLoopFixpoint.simpleLoopFixpoint"
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
                  "SimpleLoopFixpoint: incompatible writes detected for block " ++ show blk
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
                       "SimpleLoopFixpoint: incompatible writes detected for block " ++
                       show blk
                  Just (RegularBlock basePtr off_map) -> return (basePtr, off_map)
                  Nothing -> return (C.llvmPointerOffset ptr, mempty)

              off_map' <- updateOffsetMap blk basePtr ptr storage_type off_map
              return (Map.insert blk (RegularBlock basePtr off_map') mem_subst)

       w -> fail $ unlines $
              [ "SimpleLoopFixpoint: unable to handle memory write of the form:"
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
        ["SimpleLoopFixpoint: failure constructing memory footprint for loop invariant"]
        ++ msg
      Right x  -> return x


-- | This function checks that the computed candidate memory substitution is an acceptable
--   refinement of the original. For the moment, this is a very restrictive test; either
--   we have started with an empty substitution (e.g., on the first iteration), or we have
--   computed a substitution that is exactly compatible with the one we started with.
--
--   At some point, it may be necessary or desirable to allow more.

checkMemSubst ::
  sym ->
  MemorySubstitution sym ->
  MemorySubstitution sym ->
  ExceptT [String] IO (MemorySubstitution sym)
checkMemSubst _sym orig candidate =
  -- TODO!! Actually perform the necessary checks here
  if Map.null (memSubst orig)
    then return candidate
    else return orig

--  throwError ["TODO3!"]
{- TODO!!
  do -- check that the mem substitution always computes the same
     -- footprint on every iteration (!?!)
     regular_mem_substitution <- if Map.null (regularMemSubst orig)
       then return (regularMemSubst candidate)
       else if Map.keys (regularMemSubst candidate) == Map.keys (regularMemSubst orig)
         then return (regularMemSubst orig)
         else throwError ["SimpleLoopFixpoint: unsupported memory writes change"]

     -- check that the array mem substitution always computes the same footprint (!?!)
     array_mem_substitution <- if Map.null (arrayMemSubst orig)
       then return (arrayMemSubst candidate)
       else if Map.keys (arrayMemSubst candidate) == Map.keys (arrayMemSubst orig)
         then return $ arrayMemSubst orig
         else throwError $ ["SimpleLoopFixpoint: unsupported SMT array memory writes change"]

     return (MemSubst regular_mem_substitution array_mem_substitution)
-}


data MaybePausedFrameTgtId f where
  JustPausedFrameTgtId :: C.Some (C.BlockID b) -> MaybePausedFrameTgtId (C.CrucibleLang b r)
  NothingPausedFrameTgtId :: MaybePausedFrameTgtId f

pausedFrameTgtId :: C.PausedFrame p sym ext rtp f -> MaybePausedFrameTgtId f
pausedFrameTgtId C.PausedFrame{ resume = resume } = case resume of
  C.ContinueResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  C.CheckMergeResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  _ -> NothingPausedFrameTgtId
