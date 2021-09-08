------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.SimpleLoopFixpoint
-- Description      : Execution feature to observe argument buffer sizes
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Stability        : provisional
------------------------------------------------------------------------

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language ImplicitParams #-}
{-# Language ViewPatterns #-}
{-# Language PatternSynonyms #-}
{-# Language BangPatterns #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}


module Lang.Crucible.LLVM.SimpleLoopFixpoint
  ( FixpointEntry(..)
  , simpleLoopFixpoint
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Either
import           Data.Foldable
import qualified Data.IntMap as IntMap
import           Data.IntMap (IntMap)
import           Data.IORef
import qualified Data.List as List
import           Data.Maybe
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Numeric.Natural

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map (MapF)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC

import qualified What4.Interface as W4

import qualified Lang.Crucible.Analysis.Fixpoint.Components as C
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.Operations as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.RegValue as C
import qualified Lang.Crucible.Simulator as C

import qualified Lang.Crucible.LLVM.Bytes as C
import qualified Lang.Crucible.LLVM.DataLayout as C
import qualified Lang.Crucible.LLVM.Extension as C
import qualified Lang.Crucible.LLVM.MemModel as C
import qualified Lang.Crucible.LLVM.MemModel.MemLog as C hiding (Mem)
import qualified Lang.Crucible.LLVM.MemModel.Generic as C.G
import qualified Lang.Crucible.LLVM.MemModel.Pointer as C
import qualified Lang.Crucible.LLVM.MemModel.Type as C
import qualified Lang.Crucible.LLVM.Translation.Monad as C


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

-- instance W4.TestEquality f => C.EqF f where
--   eqF x y = isJust $ W4.testEquality x y

instance W4.TestEquality (FixpointEntry sym) => C.EqF (FixpointEntry sym) where
  eqF x y = isJust $ W4.testEquality x y

data MemFixpointEntry sym = forall w . (1 <= w) => MemFixpointEntry
  { memFixpointEntrySym :: sym
  , memFixpointEntryJoinVariable :: W4.SymBV sym w
  , memFixpointEntryWidth :: C.NatRepr w
  -- , memFixpointEntryStoregeType :: C.StorageType
  }

instance W4.TestEquality (W4.SymExpr sym) => Eq (MemFixpointEntry sym) where
  (MemFixpointEntry _ x_join_variable x_width) == (MemFixpointEntry _ y_join_variable y_width)
    | Just Refl <- W4.testEquality x_join_variable y_join_variable =
      True
    | otherwise = False

data FixpointStuff sym blocks = forall args . FixpointStuff
  { fixpointStatus :: FixpointStatus
  , fixpointBlockId :: C.Some (C.BlockID blocks)
  , fixpointAssumptionFrameIdentifier :: C.FrameIdentifier
  , substitution :: MapF (W4.SymExpr sym) (FixpointEntry sym)
  , fixpointRegMap :: C.RegMap sym args
  , fixpointMemSubstitution :: Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType)
  , fixpointLoopCondition :: W4.Pred sym
  , fixpointLoopIndexBound :: LoopIndexBound sym
  }

type FixpointMonad sym = StateT (MapF (W4.SymExpr sym) (FixpointEntry sym)) IO

joinRegEntries ::
  C.IsSymInterface sym =>
  sym ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  FixpointMonad sym (Ctx.Assignment (C.RegEntry sym) ctx)
joinRegEntries sym = Ctx.zipWithM (joinRegEntry sym)

joinRegEntry ::
  C.IsSymInterface sym =>
  sym ->
  C.RegEntry sym tp ->
  C.RegEntry sym tp ->
  FixpointMonad sym (C.RegEntry sym tp)
joinRegEntry sym left right = do
--  liftIO $ putStrLn $ "joinRegEntry: left_type=" ++ show (C.regType left) ++ " , right_type=" ++ show (C.regType right)
 case C.regType left of
  C.LLVMPointerRepr w
    | List.isPrefixOf "cmacaw_reg" (show $ W4.printSymNat $ C.llvmPointerBlock (C.regValue left))
    , List.isPrefixOf "cmacaw_reg" (show $ W4.printSymExpr $ C.llvmPointerOffset (C.regValue left)) -> do
      -- liftIO $ putStrLn $ "joinRegEntry: cmacaw_reg"
      return left
    | C.llvmPointerBlock (C.regValue left) == C.llvmPointerBlock (C.regValue right) -> do
      -- liftIO $ putStrLn $ "joinRegEntry: LLVMPointerRepr"
      subst <- get
      if isJust (W4.testEquality (C.llvmPointerOffset (C.regValue left)) (C.llvmPointerOffset (C.regValue right))) then do
        -- liftIO $ putStrLn $ "joinRegEntry: left == right"
        return left
      else case MapF.lookup (C.llvmPointerOffset (C.regValue left)) subst of
        Just join_entry -> do
          -- liftIO $ putStrLn $ "joinRegEntry: LLVMPointerRepr: Just: " ++ show (W4.printSymExpr $ bodyValue join_entry)  ++ " -> " ++ show (W4.printSymExpr $ C.llvmPointerOffset (C.regValue right))
          put $ MapF.insert
            (C.llvmPointerOffset (C.regValue left))
            (join_entry { bodyValue = (C.llvmPointerOffset (C.regValue right)) })
            subst
          return left
        Nothing -> do
          -- liftIO $ putStrLn $ "joinRegEntry: LLVMPointerRepr: Nothing"
          join_varaible <- liftIO $ W4.freshConstant sym (fromRight undefined $ W4.userSymbol "foo") (W4.BaseBVRepr w)
          let join_entry = FixpointEntry
                { headerValue = (C.llvmPointerOffset (C.regValue left))
                , bodyValue = (C.llvmPointerOffset (C.regValue right))
                }
          put $ MapF.insert join_varaible join_entry subst
          return $ C.RegEntry (C.LLVMPointerRepr w) $ C.LLVMPointer (C.llvmPointerBlock (C.regValue left)) join_varaible
    | otherwise -> do
      -- liftIO $ putStrLn $ "joinRegEntry: " ++ show (C.ppPtr $ C.regValue left) ++ " \\/ " ++ show (C.ppPtr $ C.regValue right)
      fail ""
  C.BoolRepr
    | List.isPrefixOf "cmacaw" (show $ W4.printSymExpr $ (C.regValue left)) -> do
      -- liftIO $ putStrLn $ "joinRegEntry: " ++ (show $ W4.printSymExpr $ (C.regValue left))
      return left
    | otherwise -> do
      -- liftIO $ putStrLn $ "joinRegEntry: " ++ show (W4.printSymExpr $ C.regValue left) ++ " \\/ " ++ show (W4.printSymExpr $ C.regValue right)
      join_varaible <- liftIO $ W4.freshConstant sym (fromRight undefined $ W4.userSymbol "macaw_reg") W4.BaseBoolRepr
      return $ C.RegEntry (C.BoolRepr) $ join_varaible
  C.StructRepr field_types -> do
    -- liftIO $ putStrLn $ "joinRegEntry: StructRepr"
    C.RegEntry (C.regType left) <$> fmapFC (C.RV . C.regValue) <$> joinRegEntries sym (Ctx.generate (Ctx.size field_types) $ \i -> C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue left) Ctx.! i) (Ctx.generate (Ctx.size field_types) $ \i -> C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue right) Ctx.! i)
  _ -> do
    -- liftIO $ putStrLn "boo!"
    fail ""


applysubstitutionRegEntries ::
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  Ctx.Assignment (C.RegEntry sym) ctx
applysubstitutionRegEntries sym substitution = fmapFC (applySubstitutionRegEntry sym substitution)

applySubstitutionRegEntry ::
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  C.RegEntry sym tp ->
  C.RegEntry sym tp
applySubstitutionRegEntry sym substitution entry = case C.regType entry of
  C.LLVMPointerRepr{} ->
    entry { C.regValue = C.LLVMPointer (C.llvmPointerBlock (C.regValue entry)) (MapF.findWithDefault (C.llvmPointerOffset (C.regValue entry)) (C.llvmPointerOffset (C.regValue entry)) substitution) }
  C.BoolRepr ->
    entry
  C.StructRepr field_types ->
    entry { C.regValue = fmapFC (C.RV . C.regValue) $ applysubstitutionRegEntries sym substitution $ Ctx.generate (Ctx.size field_types) $ \i -> C.RegEntry (field_types Ctx.! i) $ C.unRV $ (C.regValue entry) Ctx.! i }
  _ -> error "boo: applySubstitutionRegEntry"


findLoopIndex ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  IO (W4.SymBV sym wptr, Natural, Natural)
findLoopIndex sym substitution = do
  foo <- catMaybes <$> mapM
    (\(MapF.Pair variable FixpointEntry{..}) -> case W4.testEquality (W4.BaseBVRepr ?ptrWidth) (W4.exprType variable) of
      Just Refl -> do
        diff <- liftIO $ W4.bvSub sym (bodyValue) variable
        case (BV.asNatural <$> W4.asBV (headerValue), BV.asNatural <$> W4.asBV diff) of
          (Just start, Just step) -> do
            -- liftIO $ putStrLn $ "loop: " ++ (show $ W4.printSymExpr variable) ++ "=" ++ show (start, step)
            return $ Just (variable, start, step)
          _ -> return Nothing
      Nothing -> return Nothing)
    (MapF.toList substitution)
  case foo of
    [bar] -> return bar
    _ -> fail "boo index"

findLoopBound ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  W4.Pred sym ->
  Natural ->
  Natural ->
  IO (W4.SymBV sym wptr)
findLoopBound sym condition _start step =
  case (Set.toList $ W4.exprUninterpConstants sym condition) of
    [C.Some loop_stop, _, _]
      | Just Refl <- W4.testEquality (W4.BaseBVRepr ?ptrWidth) (W4.exprType $ W4.varExpr sym loop_stop) ->
        W4.bvMul sym (W4.varExpr sym loop_stop) =<< W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral step)
    _ -> fail "boo..."

data LoopIndexBound sym = forall w . 1 <= w => LoopIndexBound
  { index :: W4.SymBV sym w
  , start :: Natural
  , stop :: W4.SymBV sym w
  , step :: Natural
  }

findLoopIndexBound ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr) =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  W4.Pred sym ->
  IO (LoopIndexBound sym)
findLoopIndexBound sym substitution condition = do
  (index, start, step) <- findLoopIndex sym substitution
  stop <- findLoopBound sym condition start step
  return $ LoopIndexBound
    { index = index
    , start = start
    , stop = stop
    , step = step
    }

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
loopIndexStartStepCondition sym LoopIndexBound{..} = do
  start_bv <- W4.bvLit sym (W4.bvWidth index) (BV.mkBV (W4.bvWidth index) $ fromIntegral start)
  step_bv <- W4.bvLit sym (W4.bvWidth index) (BV.mkBV (W4.bvWidth index) $ fromIntegral step)
  W4.bvEq sym start_bv =<< W4.bvUrem sym index step_bv

-- newtype SymBVWrapper sym w = SymBVWrapper { unSymBV :: W4.SymBV sym w }


loadMemJoinVariables ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  C.MemImpl sym ->
  Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType) ->
  IO (MapF (W4.SymExpr sym) (W4.SymExpr sym))
loadMemJoinVariables sym mem subst = MapF.fromList <$> mapM
  (\((blk, off, _sz), (MemFixpointEntry { memFixpointEntryJoinVariable = join_varaible, memFixpointEntryWidth = _bv_width}, storeage_type)) -> do
    ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral off)
    val <- C.doLoad sym mem ptr storeage_type (C.LLVMPointerRepr $ W4.bvWidth join_varaible) C.noAlignment
    case W4.asNat (C.llvmPointerBlock val) of
      Just 0 -> return $ MapF.Pair join_varaible $ C.llvmPointerOffset val
      _ -> fail "boo... loadMemJoinVariables")
  (Map.toAscList subst)

storeMemJoinVariables ::
  (C.IsSymInterface sym, C.HasPtrWidth wptr, C.HasLLVMAnn sym) =>
  sym ->
  C.MemImpl sym ->
  Map (Natural, Natural, Natural) (MemFixpointEntry sym, C.StorageType) ->
  MapF (W4.SymExpr sym) (W4.SymExpr sym) ->
  IO (C.MemImpl sym)
storeMemJoinVariables sym mem mem_subst eq_subst = foldlM
  (\mem_acc ((blk, off, _sz), (MemFixpointEntry { memFixpointEntryJoinVariable = join_varaible, memFixpointEntryWidth = _bv_width}, storeage_type)) -> do
    ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth $ fromIntegral off)
    C.doStore sym mem_acc ptr (C.LLVMPointerRepr $ W4.bvWidth join_varaible) storeage_type C.noAlignment =<< C.llvmPointer_bv sym (MapF.findWithDefault join_varaible join_varaible eq_subst))
  mem
  (Map.toAscList mem_subst)

dropMemStackFrame :: C.IsSymInterface sym => C.MemImpl sym -> (C.MemImpl sym, C.MemAllocs sym, C.MemWrites sym)
dropMemStackFrame mem = case (C.memImplHeap mem) ^. C.memState of
  (C.StackFrame _ _ _ (a, w) s) -> ((mem { C.memImplHeap = (C.memImplHeap mem) & C.memState .~ s }), a, w)
  _ -> error $ "dropMemStackFrame: not a stack frame " ++ show (C.ppMem $ C.memImplHeap mem)


filterSubstitution ::
  C.IsSymInterface sym =>
  sym ->
  MapF (W4.SymExpr sym) (FixpointEntry sym) ->
  MapF (W4.SymExpr sym) (FixpointEntry sym)
filterSubstitution sym substitution =
  -- TODO: fixpoint
  let uninterp_constants = foldMapF
        (varExprSet sym . W4.exprUninterpConstants sym . bodyValue)
        substitution
  in
  MapF.filterWithKey (\variable _entry -> Set.member (C.Some variable) uninterp_constants) substitution

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
  in  (normal_substitution, uninterpreted_constant_substitution)

-- newtype SymExprList sym tp = SymExprList { unSymExprList :: [W4.SymExpr sym tp] }
--   deriving (Semigroup, Monoid)


varExprSet ::
  C.IsSymInterface sym =>
  sym ->
  Set (C.Some (W4.BoundVar sym)) ->
  Set (C.Some (W4.SymExpr sym))
varExprSet sym = Set.fromList . map (C.mapSome $ W4.varExpr sym) . Set.toList


instance W4.IsExpr (W4.SymExpr sym) => Show (C.RegEntry sym tp) where
  show (C.RegEntry C.LLVMPointerRepr{} x) = show $ C.ppPtr x
  show (C.RegEntry (C.StructRepr field_types) x) = show $ toListFC C.Some $ Ctx.generate (Ctx.size field_types) $ \i -> C.RegEntry @sym (field_types Ctx.! i) $ C.unRV $ x Ctx.! i
  show (C.RegEntry C.BoolRepr x) = show $ W4.printSymExpr $ x
  show _ = undefined
instance W4.IsExpr (W4.SymExpr sym) => ShowF (C.RegEntry sym)


simpleLoopFixpoint ::
  -- forall sym arch p rtp blocks init ret .
  -- (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  -- C.LLVMContext arch ->
  -- sym ->
  -- C.CFG (C.LLVM arch) blocks init ret ->
  -- IO (C.ExecutionFeature p sym (C.LLVM arch) rtp)
  forall sym ext p rtp blocks init ret .
  (C.IsSymInterface sym, C.HasLLVMAnn sym, ?memOpts :: C.MemOptions) =>
  sym ->
  C.CFG ext blocks init ret ->
  C.GlobalVar C.Mem ->
  (MapF (W4.SymExpr sym) (FixpointEntry sym) -> W4.Pred sym -> IO (MapF (W4.SymExpr sym) (W4.SymExpr sym), W4.Pred sym)) ->
  IO (C.ExecutionFeature p sym ext rtp)
simpleLoopFixpoint sym cfg@C.CFG{..} mem_var foo_func = do
  let ?ptrWidth = knownNat @64
  -- putStrLn $ "SimpleLoopFixpoint: " ++ show (C.cfgWeakTopologicalOrdering cfg)
  let flattenWTOComponent = \case
        C.SCC (C.SCCData{..}) ->  wtoHead : (concatMap flattenWTOComponent wtoComps)
        C.Vertex v -> [v]
  let loop_map = Map.fromList $ catMaybes $ map
        (\case
          C.SCC (C.SCCData{..}) -> Just (wtoHead, (wtoHead : (concatMap flattenWTOComponent wtoComps)))
          C.Vertex{} -> Nothing)
        (C.cfgWeakTopologicalOrdering cfg)
  -- putStrLn $ "loops: " ++ show loop_map

  fixpoint_stuff_ref <- newIORef @(FixpointStuff sym blocks) $ FixpointStuff
    { fixpointStatus = BeforeFixpoint
    , fixpointBlockId = undefined
    , fixpointAssumptionFrameIdentifier = undefined
    , substitution = MapF.empty
    , fixpointRegMap = undefined
    , fixpointMemSubstitution = undefined
    , fixpointLoopCondition = undefined
    , fixpointLoopIndexBound = undefined
    }

  return $ C.ExecutionFeature $ \exec_state -> do
    fixpoint_stuff <- readIORef fixpoint_stuff_ref
    case exec_state of
      C.RunningState (C.RunBlockStart block_id) state
        | C.SomeHandle cfgHandle == C.frameHandle (state ^. C.stateCrucibleFrame)
        , Just Refl <- W4.testEquality
            (fmapFC C.blockInputs cfgBlockMap)
            (fmapFC C.blockInputs $ C.frameBlockMap $ state ^. C.stateCrucibleFrame)
        , Map.member (C.Some block_id) loop_map -> do
          case fixpointStatus fixpoint_stuff of

            BeforeFixpoint -> do
              -- putStrLn $ "RunningState: BeforeFixpoint -> ComputeFixpoint"
              assumption_frame_identifier <- C.pushAssumptionFrame sym
              let (Just mem_impl) = C.lookupGlobal mem_var (state ^. C.stateGlobals)
              let mem_impl' = mem_impl { C.memImplHeap = C.pushStackFrameMem "foo" $ C.memImplHeap mem_impl }
              writeIORef fixpoint_stuff_ref $ FixpointStuff
                { fixpointStatus = ComputeFixpoint
                , fixpointBlockId = C.Some block_id
                , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
                , substitution = MapF.empty
                , fixpointRegMap = state ^. C.stateCrucibleFrame ^. C.frameRegs
                , fixpointMemSubstitution = Map.empty
                , fixpointLoopCondition = undefined
                , fixpointLoopIndexBound = undefined
                }
              return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                state & C.stateGlobals %~ C.insertGlobal mem_var mem_impl'

            ComputeFixpoint
              | FixpointStuff { fixpointRegMap = fixpoint_reg_map } <- fixpoint_stuff
              , Just Refl <- W4.testEquality
                  (fmapFC C.regType $ C.regMap fixpoint_reg_map)
                  (fmapFC C.regType $ C.regMap $ state ^. C.stateCrucibleFrame ^. C.frameRegs) -> do
                -- putStrLn $ "RunningState: ComputeFixpoint: " ++ show block_id
                _ <- C.popAssumptionFrameAndObligations sym $ fixpointAssumptionFrameIdentifier fixpoint_stuff
                (fixpoint_reg_map', substitution') <- runStateT
                  (joinRegEntries sym (C.regMap fixpoint_reg_map) (C.regMap $ state ^. C.stateCrucibleFrame ^. C.frameRegs)) $
                  substitution fixpoint_stuff
                let (Just mem_impl) = C.lookupGlobal mem_var (state ^. C.stateGlobals)
                let (mem_impl', mem_allocs, mem_writes) = dropMemStackFrame mem_impl
                when (C.sizeMemAllocs mem_allocs /= 0) $
                  fail "boo... allocs"
                fixpoint_mem_substitution <- if Map.null (fixpointMemSubstitution fixpoint_stuff)
                  then
                    Map.fromList <$> catMaybes <$> case mem_writes of
                      C.MemWrites [C.MemWritesChunkIndexed mmm] -> mapM
                        (\case
                          (C.MemWrite ptr (C.MemStore _ storeage_type _))
                            | Just blk <- W4.asNat (C.llvmPointerBlock ptr)
                            , Just off <- BV.asNatural <$> W4.asBV (C.llvmPointerOffset ptr) -> do
                              let sz = C.bytesToBits $ C.typeEnd 0 storeage_type
                              some_join_varaible <- liftIO $ case W4.mkNatRepr sz of
                                C.Some bv_width
                                  | Just C.LeqProof <- W4.testLeq (W4.knownNat @1) bv_width -> do
                                    join_varaible <- W4.freshConstant sym (fromRight undefined $ W4.userSymbol "bar") (W4.BaseBVRepr bv_width)
                                    return $ MemFixpointEntry
                                      { memFixpointEntrySym = sym
                                      , memFixpointEntryJoinVariable = join_varaible
                                      , memFixpointEntryWidth = bv_width
                                      }
                                  | otherwise -> error "zero size"
                              return $ Just ((blk, off, sz), (some_join_varaible, storeage_type))
                            | Just _blk <- W4.asNat (C.llvmPointerBlock ptr) ->
                              return Nothing
                          _ -> fail $ "boo..." ++ show (C.ppMem $ C.memImplHeap mem_impl'))
                        (List.concat $ IntMap.elems mmm)
                      _ -> fail $ "boo... not MemWritesChunkIndexed" ++ show (C.ppMemWrites mem_writes)
                  else
                    return $ fixpointMemSubstitution fixpoint_stuff

                assumption_frame_identifier <- C.pushAssumptionFrame sym

                if MapF.keys substitution' == MapF.keys (substitution fixpoint_stuff)
                  then do
                    -- putStrLn $ "RunningState: ComputeFixpoint -> CheckFixpoint"
                    -- putStrLn $ "cond: " ++ show (W4.printSymExpr $ fixpointLoopCondition fixpoint_stuff)
                    -- putStrLn $ "cond vars: " ++ show (map (C.viewSome W4.printSymExpr) $ map (C.mapSome $ W4.varExpr sym) $ Set.toList $ W4.exprUninterpConstants sym $ fixpointLoopCondition fixpoint_stuff)

                    foo <- loadMemJoinVariables sym mem_impl' $ fixpointMemSubstitution fixpoint_stuff
                    bar <- loadMemJoinVariables sym mem_impl $ fixpointMemSubstitution fixpoint_stuff
                    let substitution'' = MapF.union substitution' $
                          MapF.intersectWithKeyMaybe (\_k x y -> Just $ FixpointEntry x y) foo bar
                    let substitution''' = filterSubstitution sym substitution''
                    let (substitution'''', equality_substitution) = uninterpretedConstantEqualitySubstitution sym substitution'''
                    -- putStrLn $ "filterSubstitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList substitution'''')
                    -- putStrLn $ "equality_substitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList equality_substitution)

                    let fixpoint_reg_map'' = applysubstitutionRegEntries sym equality_substitution fixpoint_reg_map'
                    -- putStrLn $ "fixpoint_reg_map'': " ++ show fixpoint_reg_map''

                    mem_impl'' <- storeMemJoinVariables
                      sym
                      (mem_impl' { C.memImplHeap = C.pushStackFrameMem "foo" (C.memImplHeap mem_impl') })
                      fixpoint_mem_substitution
                      equality_substitution

                    loop_index_bound <- findLoopIndexBound sym substitution'''' $ fixpointLoopCondition fixpoint_stuff

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
                      , substitution = substitution''''
                      , fixpointRegMap = C.RegMap fixpoint_reg_map''
                      , fixpointMemSubstitution = fixpoint_mem_substitution
                      , fixpointLoopCondition = fixpointLoopCondition fixpoint_stuff
                      , fixpointLoopIndexBound = loop_index_bound
                      }
                    return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                      state & (C.stateCrucibleFrame . C.frameRegs) .~ (C.RegMap fixpoint_reg_map'')
                        & C.stateGlobals %~ C.insertGlobal mem_var mem_impl''

                  else do
                    -- putStrLn $ "RunningState: ComputeFixpoint -> ComputeFixpoint"
                    -- putStrLn $ "diff: " ++ show (MapF.size (MapF.intersectWithKeyMaybe (\_k a b -> if isNothing (W4.testEquality a b) then Just a else Nothing) substitution' (substitution fixpoint_stuff)))

                    mem_impl'' <- storeMemJoinVariables sym
                      (mem_impl' { C.memImplHeap = C.pushStackFrameMem "foo" (C.memImplHeap mem_impl') })
                      fixpoint_mem_substitution
                      MapF.empty

                    writeIORef fixpoint_stuff_ref $ FixpointStuff
                      { fixpointStatus = ComputeFixpoint
                      , fixpointBlockId = C.Some block_id
                      , fixpointAssumptionFrameIdentifier = assumption_frame_identifier
                      , substitution = substitution'
                      , fixpointRegMap = C.RegMap fixpoint_reg_map'
                      , fixpointMemSubstitution = fixpoint_mem_substitution
                      , fixpointLoopCondition = undefined
                      , fixpointLoopIndexBound = undefined
                      }
                    return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                      state & (C.stateCrucibleFrame . C.frameRegs) .~ (C.RegMap fixpoint_reg_map')
                        & C.stateGlobals %~ C.insertGlobal mem_var mem_impl''
              | otherwise -> error ""

            CheckFixpoint
              | FixpointStuff { fixpointRegMap = fixpoint_reg_map } <- fixpoint_stuff
              , Just Refl <- W4.testEquality
                  (fmapFC C.regType $ C.regMap fixpoint_reg_map)
                  (fmapFC C.regType $ C.regMap $ state ^. C.stateCrucibleFrame ^. C.frameRegs) -> do
                -- putStrLn $ "RunningState: CheckFixpoint -> AfterFixpoint: " ++ show block_id

                (_ :: ()) <- case fixpointLoopIndexBound fixpoint_stuff of
                  LoopIndexBound{ index = loop_index, stop = loop_stop } -> do
                    loc <- W4.getCurrentProgramLoc sym
                    index_bound_condition <- loopIndexBoundCondition
                      sym
                      (bodyValue $ fromJust $ MapF.lookup loop_index $ substitution fixpoint_stuff)
                      loop_stop
                    C.addProofObligation sym $ C.LabeledPred index_bound_condition $ C.SimError loc ""

                _ <- C.popAssumptionFrame sym $ fixpointAssumptionFrameIdentifier fixpoint_stuff

                let (Just mem_impl) = C.lookupGlobal mem_var (state ^. C.stateGlobals)
                let (mem_impl', _mem_allocs, _mem_writes) = dropMemStackFrame mem_impl

                bar <- loadMemJoinVariables sym mem_impl $ fixpointMemSubstitution fixpoint_stuff
                let substitution' = MapF.mapWithKey
                      (\variable fixpoint_entry -> fixpoint_entry { bodyValue = MapF.findWithDefault (bodyValue fixpoint_entry) variable bar })
                      (substitution fixpoint_stuff)
                -- putStrLn $ "filterSubstitution: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr $ bodyValue y)) $ MapF.toList substitution')

                (lalala, lalalala) <- liftIO $ foo_func substitution' $ fixpointLoopCondition fixpoint_stuff
                locloc <- W4.getCurrentProgramLoc sym
                C.addProofObligation sym $ C.LabeledPred lalalala $ C.SimError locloc ""
                -- putStrLn $ "foo_func: " ++ show (map (\(MapF.Pair x y) -> (W4.printSymExpr x, W4.printSymExpr y)) $ MapF.toList lalala)

                let fixpoint_reg_map' = C.RegMap $ applysubstitutionRegEntries sym lalala (C.regMap fixpoint_reg_map)

                mem_impl'' <- storeMemJoinVariables sym mem_impl' (fixpointMemSubstitution fixpoint_stuff) lalala

                (_ :: ()) <- case fixpointLoopIndexBound fixpoint_stuff of
                  LoopIndexBound{ index = loop_index, stop = loop_stop } -> do
                    let loop_index' = MapF.findWithDefault loop_index loop_index lalala
                    loc <- W4.getCurrentProgramLoc sym
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
                  , substitution = substitution'
                  }
                return $ C.ExecutionFeatureModifiedState $ C.RunningState (C.RunBlockStart block_id) $
                  state & (C.stateCrucibleFrame . C.frameRegs) .~ fixpoint_reg_map'
                    & C.stateGlobals %~ C.insertGlobal mem_var mem_impl''
              | otherwise -> error ""

            AfterFixpoint -> error "boo!"

        | otherwise -> do
          -- putStrLn $ "RunningState: RunBlockStart: " ++ show block_id
          return C.ExecutionFeatureNoChange

      C.SymbolicBranchState branch_condition true_frame false_frame _target state
        | Just loop_body_some_block_ids <- Map.lookup (fixpointBlockId fixpoint_stuff) loop_map
        , JustPausedFrameTgtId true_frame_some_block_id <- pausedFrameTgtId true_frame
        , JustPausedFrameTgtId false_frame_some_block_id <- pausedFrameTgtId false_frame
        , C.SomeHandle cfgHandle == C.frameHandle (state ^. C.stateCrucibleFrame)
        , Just Refl <- W4.testEquality
            (fmapFC C.blockInputs cfgBlockMap)
            (fmapFC C.blockInputs $ C.frameBlockMap $ state ^. C.stateCrucibleFrame)
        , (elem true_frame_some_block_id loop_body_some_block_ids) /= (elem false_frame_some_block_id loop_body_some_block_ids) -> do

          (loop_condition, inside_loop_frame, outside_loop_frame) <- if (elem true_frame_some_block_id loop_body_some_block_ids) then
              return (branch_condition, true_frame, false_frame)
            else do
              not_branch_condition <- W4.notPred sym branch_condition
              return (not_branch_condition, false_frame, true_frame)

          (condition, frame) <- case fixpointStatus fixpoint_stuff of
            BeforeFixpoint -> error "boo!"
            ComputeFixpoint -> do
              -- putStrLn $ "SymbolicBranchState: ComputeFixpoint"
              writeIORef fixpoint_stuff_ref $ fixpoint_stuff { fixpointLoopCondition = loop_condition }
              return (loop_condition, inside_loop_frame)
            CheckFixpoint -> do
              -- putStrLn $ "SymbolicBranchState: CheckFixpoint"
              return (loop_condition, inside_loop_frame)
            AfterFixpoint -> do
              -- putStrLn $ "SymbolicBranchState: AfterFixpoint"
              not_loop_condition <- W4.notPred sym loop_condition
              return (not_loop_condition, outside_loop_frame)

          loc <- W4.getCurrentProgramLoc sym
          C.addAssumption sym $ C.BranchCondition loc (C.pausedLoc frame) condition
          C.ExecutionFeatureNewState <$> runReaderT (C.resumeFrame (C.forgetPostdomFrame frame) $ state ^. C.stateTree ^. C.actContext) state

      _ -> return C.ExecutionFeatureNoChange


data MaybePausedFrameTgtId f where
  JustPausedFrameTgtId :: C.Some (C.BlockID b) -> MaybePausedFrameTgtId (C.CrucibleLang b r)
  NothingPausedFrameTgtId :: MaybePausedFrameTgtId f

pausedFrameTgtId :: C.PausedFrame p sym ext rtp f -> MaybePausedFrameTgtId f
pausedFrameTgtId C.PausedFrame{ resume = resume } = case resume of
  C.ContinueResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  C.CheckMergeResumption (C.ResolvedJump tgt_id _) -> JustPausedFrameTgtId $ C.Some tgt_id
  _ -> NothingPausedFrameTgtId
