------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.ArraySizeProfile
-- Description      : Execution feature to observe argument buffer sizes
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Samuel Breese <sbreese@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# Options -Wall #-}
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
{-# Language GADTs #-}

module Lang.Crucible.LLVM.ArraySizeProfile
 ( FunctionProfile(..), funProfileName, funProfileArgs
 , ArgProfile(..), argProfileSize, argProfileInitialized
 , arraySizeProfile
 ) where

import Control.Lens.TH

import Control.Monad
import Control.Lens

import Numeric.Natural

import Data.Type.Equality ((:~:)(..), testEquality)
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Parameterized.Some
import Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import qualified Lang.Crucible.Analysis.Fixpoint as C
import qualified Lang.Crucible.Analysis.Fixpoint.Components as C
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C

import qualified Lang.Crucible.LLVM.DataLayout as C
import qualified Lang.Crucible.LLVM.Extension as C
import qualified Lang.Crucible.LLVM.MemModel as C
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.Translation.Monad as C

import qualified What4.Interface as W4
import qualified What4.Partial as W4

------------------------------------------------------------------------
-- Profiles

data ArgProfile = ArgProfile
  { _argProfileSize :: Maybe Int
  , _argProfileInitialized :: Bool
  } deriving (Show, Eq, Ord)
makeLenses ''ArgProfile

data FunctionProfile = FunctionProfile
  { _funProfileName :: Text
  , _funProfileArgs :: [ArgProfile]
  } deriving (Show, Eq, Ord)
makeLenses ''FunctionProfile

------------------------------------------------------------------------
-- Learning a profile from an ExecState

ptrStartsAlloc ::
  W4.IsExpr (W4.SymExpr sym) =>
  C.LLVMPtr sym w ->
  Bool
ptrStartsAlloc (C.llvmPointerView -> (_, W4.asUnsignedBV -> Just 0)) = True
ptrStartsAlloc _ = False

ptrAllocSize ::
  forall sym w.
  C.IsSymInterface sym =>
  G.Mem sym ->
  C.LLVMPtr sym w ->
  Maybe Int
ptrAllocSize mem (C.llvmPointerView -> (blk, _)) = msum $ inAlloc <$> G.memAllocs mem
  where
    inAlloc :: G.MemAlloc sym -> Maybe Int
    inAlloc memAlloc
      | G.Alloc _ a (Just sz) _ _ _ <- memAlloc
      , Just a == W4.asNat blk =
        fromIntegral <$> W4.asUnsignedBV sz
      | otherwise = Nothing

ptrArraySize ::
  C.IsSymInterface sym =>
  G.Mem sym ->
  C.LLVMPtr sym w ->
  Maybe Int
ptrArraySize mem ptr
  | ptrStartsAlloc ptr = ptrAllocSize mem ptr
  | otherwise = Nothing

ptrIsInitialized ::
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.LLVMPtr sym w ->
  IO Bool
ptrIsInitialized sym mem ptr =
  G.readMem sym C.PtrWidth ptr (C.bitvectorType 1) C.noAlignment mem >>= \case
  W4.NoErr{} -> pure True
  _ -> pure False

intrinsicArgProfile ::
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  SymbolRepr nm ->
  C.CtxRepr ctx ->
  C.Intrinsic sym nm ctx ->
  IO ArgProfile
intrinsicArgProfile sym mem
  (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
  (Ctx.Empty Ctx.:> C.BVRepr (testEquality ?ptrWidth -> Just Refl)) i =
   ArgProfile (ptrArraySize mem i) <$> ptrIsInitialized sym mem i
intrinsicArgProfile _ _ _ _ _ = pure $ ArgProfile Nothing False

regValueArgProfile ::
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.TypeRepr tp ->
  C.RegValue sym tp ->
  IO ArgProfile
regValueArgProfile sym mem (C.IntrinsicRepr nm ctx) i = intrinsicArgProfile sym mem nm ctx i
regValueArgProfile _ _ _ _ = pure $ ArgProfile Nothing False

regEntryArgProfile ::
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.RegEntry sym tp ->
  IO ArgProfile
regEntryArgProfile sym mem (C.RegEntry t v) = regValueArgProfile sym mem t v

newtype Wrap a (b :: C.CrucibleType) = Wrap { unwrap :: a }
argProfiles ::
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  IO [ArgProfile]
argProfiles sym mem as =
  sequence (Vector.toList $ Ctx.toVector (fmapFC (Wrap . regEntryArgProfile sym mem) as) unwrap)

------------------------------------------------------------------------
-- Generalize loops

type WTOMap = Map Int (Int, Int)

buildWTOMap :: [C.WTOComponent (Some (C.BlockID blocks))] -> WTOMap
buildWTOMap = snd . go 0 0 Map.empty
  where
    go :: Int -> Int -> WTOMap -> [C.WTOComponent (Some (C.BlockID blocks))] -> (Int, WTOMap)
    go !x !_ m [] = (x, m)
    go !x !d m (C.Vertex (Some bid):cs) =
       let m' = Map.insert (Ctx.indexVal $ C.blockIDIndex bid) (x, d) m
       in go (x + 1) d m' cs
    go !x !d m (C.SCC (Some hd) subcs : cs) =
       let m' = Map.insert (Ctx.indexVal $ C.blockIDIndex hd) (x, d + 1) m
           (x', m'') = go (x + 1) (d + 1) m' subcs
       in go x' d m'' cs

isBackedge ::
  WTOMap ->
  Some (C.BlockID blocks) ->
  C.BlockID blocks args ->
  Bool
isBackedge wtoMap (Some current) target
  | Just (cx, _) <- Map.lookup (Ctx.indexVal $ C.blockIDIndex current) wtoMap
  , Just (tx, _) <- Map.lookup (Ctx.indexVal $ C.blockIDIndex target) wtoMap
  , tx <= cx
  = True
  | otherwise = False

data ReadByteResult sym = Uninitialized | Concrete Integer | Symbolic (W4.SymBV sym 8)

readByte ::
  forall sym w.
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.Alignment ->
  Natural ->
  Integer ->
  IO (ReadByteResult sym)
readByte sym mem alignment blk off = do
  ptr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym C.PtrWidth off
  G.readMem sym C.PtrWidth ptr (C.bitvectorType 1) alignment mem >>= \case
    W4.NoErr (W4.Partial _ (C.LLVMValInt _ val))
      | Just x <- W4.asUnsignedBV val
        -> pure $ Concrete x
      | Just Refl <- testEquality (W4.knownNat :: W4.NatRepr 8) (W4.bvWidth val)
        -> pure $ Symbolic val
    _ -> pure Uninitialized

readAlloc ::
  forall sym w.
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  Natural ->
  Integer ->
  C.Alignment ->
  IO [ReadByteResult sym]
readAlloc sym mem blk sz alignment = mapM (readByte sym mem alignment blk) [0, 1 .. sz - 1 ]

compareReadByte ::
  forall sym.
  (C.IsSymInterface sym) =>
  ReadByteResult sym ->
  ReadByteResult sym ->
  Bool
compareReadByte (Concrete x) (Concrete y)
  | x /= y = True
  | otherwise = False
compareReadByte _ Symbolic{} = False
compareReadByte Symbolic{} _ = False
compareReadByte _ Concrete{} = True
compareReadByte _ Uninitialized = False

summarizeReadByte ::
  forall sym.
  (C.IsSymInterface sym) =>
  sym ->
  W4.SymNat sym ->
  ReadByteResult sym ->
  ReadByteResult sym ->
  IO (C.LLVMVal sym)
summarizeReadByte sym blkZero (Concrete x) (Concrete y)
  | x /= y = do
      let symbol = W4.safeSymbol $ mconcat ["generalize_", show x, "_", show y]
      val <- W4.freshConstant sym symbol (W4.BaseBVRepr $ W4.knownNat @8)
      pure $ C.LLVMValInt blkZero val
  | otherwise = C.LLVMValInt blkZero <$> W4.bvLit sym (W4.knownNat @8) x
summarizeReadByte _ blkZero _ (Symbolic s) = pure $ C.LLVMValInt blkZero s
summarizeReadByte _ blkZero (Symbolic s) _ = pure $ C.LLVMValInt blkZero s
summarizeReadByte sym blkZero _ (Concrete x) = C.LLVMValInt blkZero
  <$> W4.bvLit sym (W4.knownNat @8) x
summarizeReadByte sym blkZero _ Uninitialized = do
  let symbol = W4.safeSymbol "generalize_undef"
  val <- W4.freshConstant sym symbol (W4.BaseBVRepr $ W4.knownNat @8)
  pure $ C.LLVMValInt blkZero val

compareReadAlloc ::
  forall sym.
  (C.IsSymInterface sym) =>
  [ReadByteResult sym] ->
  [ReadByteResult sym] ->
  Bool
compareReadAlloc old new = or $ zipWith compareReadByte old new

summarizeReadAlloc ::
  forall sym.
  (C.IsSymInterface sym) =>
  sym ->
  W4.SymNat sym ->
  [ReadByteResult sym] ->
  [ReadByteResult sym] ->
  IO [C.LLVMVal sym]
summarizeReadAlloc sym blkZero old new = zipWithM (summarizeReadByte sym blkZero) old new

generalizeMemory ::
  forall sym w.
  (C.IsSymInterface sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym {- ^ Old memory -} ->
  G.Mem sym {- ^ New memory -} ->
  IO (Maybe (G.Mem sym)) {- ^ Nothing if old memory already generalizes new memory -}
generalizeMemory sym old new = do
  let allocs = G.memAllocs old
  (mem, wrote) <- foldM
    ( \(mem, wrote) -> \case
        G.Alloc _ blk (Just (W4.asUnsignedBV -> Just sz)) G.Mutable alignment _
          | Just (Some (szRepr :: W4.NatRepr x)) <- W4.someNat sz
          , Just W4.LeqProof <- W4.testLeq (W4.knownNat :: W4.NatRepr 1) szRepr -> do
              oldBytes <- readAlloc sym old blk sz alignment
              newBytes <- readAlloc sym mem blk sz alignment
              if | compareReadAlloc oldBytes newBytes
                   -> do
                     blkPtr <- C.LLVMPointer <$> W4.natLit sym blk <*> W4.bvLit sym C.PtrWidth 0
                     blkZero <- W4.natLit sym 0
                     let ty = C.arrayType (fromIntegral sz) $ C.bitvectorType 1
                     summary <- summarizeReadAlloc sym blkZero oldBytes newBytes
                     let val = C.LLVMValArray (C.bitvectorType 1)
                               . Vector.fromList
                               $ summary
                     (mem', _, _) <- G.writeMem sym C.PtrWidth blkPtr ty alignment val mem
                     pure (mem', True)
                 | otherwise -> pure (mem, wrote)
        _ -> pure (mem, wrote)
    ) (new, False) allocs
  pure $ if wrote then Just mem else Nothing

------------------------------------------------------------------------
-- Execution feature for learning profiles

updateProfiles ::
  (C.IsSymInterface sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef (Map Text [FunctionProfile]) ->
  C.ExecState p sym (C.LLVM arch) rtp ->
  IO ()
updateProfiles llvm cell state
  | C.CallState _ (C.CrucibleCall _ frame) sim <- state
  , C.CallFrame { C._frameCFG = cfg, C._frameRegs = regs } <- frame
  , Just mem <- C.memImplHeap <$> C.lookupGlobal (C.llvmMemVar llvm) (sim ^. C.stateGlobals)
  = do
      argProfs <- argProfiles (sim ^. C.stateSymInterface) mem $ C.regMap regs
      modifyIORef' cell $ \profs ->
        let name = Text.pack . show $ C.cfgHandle cfg
            funProf = FunctionProfile name argProfs
        in case Map.lookup name profs of
             Nothing -> Map.insert name [funProf] profs
             Just variants
               | funProf `elem` variants -> profs
               | otherwise -> Map.insert name (funProf:variants) profs
  | otherwise = pure ()

arraySizeProfile ::
  forall sym arch p rtp.
  (C.IsSymInterface sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef (Map Text [FunctionProfile]) ->
  IO (C.ExecutionFeature p sym (C.LLVM arch) rtp)
arraySizeProfile llvm profiles = do
  (frameLoopStarts :: IORef (Map Text (Set Int))) <- newIORef Map.empty
  (frameWTOMaps :: IORef (Map Text WTOMap)) <- newIORef Map.empty
  (frameMemCache :: IORef (Map Text (G.Mem sym))) <- newIORef Map.empty
  pure . C.ExecutionFeature $ \s -> do
    updateProfiles llvm profiles s
    case s of
      C.CallState _ (C.CrucibleCall _ C.CallFrame { C._frameCFG = g }) _ -> do
        let name = Text.pack . show $ C.cfgHandle g
        let wtoMap = buildWTOMap $ C.cfgWeakTopologicalOrdering g
        modifyIORef frameWTOMaps $ \fwto ->
          case Map.lookup name fwto of
            Just _ -> fwto
            Nothing -> Map.insert name wtoMap fwto
        pure C.ExecutionFeatureNoChange
      C.RunningState (C.RunBlockStart bid) st -> do
        frameStarts <- readIORef frameLoopStarts
        let sym = st ^. C.stateSymInterface
        let name = Text.pack . show . C.frameHandle $ st ^. C.stateCrucibleFrame
        case Map.lookup name frameStarts of
          Just starts
            | Set.member (Ctx.indexVal $ C.blockIDIndex bid) starts
            , Just memImpl <- C.lookupGlobal (C.llvmMemVar llvm) $ st ^. C.stateGlobals
              -> do
                fmc <- readIORef frameMemCache
                case Map.lookup name fmc of
                  Just oldMem -> generalizeMemory sym oldMem (C.memImplHeap memImpl) >>= \case
                    Just genMem -> do
                      writeIORef frameMemCache $ Map.insert name genMem fmc
                      let st' = st & C.stateGlobals
                            %~ C.insertGlobal (C.llvmMemVar llvm) memImpl { C.memImplHeap = genMem }
                      pure . C.ExecutionFeatureModifiedState
                        $ C.RunningState (C.RunBlockStart bid) st'
                    Nothing -> let
                      loc = C.frameProgramLoc $ st ^. C.stateCrucibleFrame
                      err = C.SimError loc $ C.GenericSimError "exiting loop with fully generalized state"
                      in pure . C.ExecutionFeatureNewState
                         $ C.AbortState (C.AssumedFalse $ C.AssumingNoError err) st
                  _ -> do
                    writeIORef frameMemCache $ Map.insert name (C.memImplHeap memImpl) fmc
                    pure C.ExecutionFeatureNoChange
          _ -> pure C.ExecutionFeatureNoChange
      C.ControlTransferState (C.ContinueResumption (C.ResolvedJump target _)) st ->
        transition frameLoopStarts frameWTOMaps target st
      C.ControlTransferState (C.CheckMergeResumption (C.ResolvedJump target _)) st ->
        transition frameLoopStarts frameWTOMaps target st
      _ -> pure C.ExecutionFeatureNoChange
  where
    transition frameLoopStarts frameWTOMaps target st = do
      let name = Text.pack . show . C.frameHandle $ st ^. C.stateCrucibleFrame
      fwto <- readIORef frameWTOMaps
      case Map.lookup name fwto of
        Just wtoMap
          | isBackedge wtoMap (st ^. C.stateCrucibleFrame . C.frameBlockID) target
            -> modifyIORef frameLoopStarts
               $ Map.alter
               ( \case
                   Just s -> Just $ Set.insert (Ctx.indexVal $ C.blockIDIndex target) s
                   Nothing -> Just . Set.singleton . Ctx.indexVal $ C.blockIDIndex target
               ) name
        _ -> pure ()
      pure C.ExecutionFeatureNoChange
