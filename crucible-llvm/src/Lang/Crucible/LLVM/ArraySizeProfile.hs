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

import Data.Type.Equality (testEquality)
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.BitVector.Sized as BV
import Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.RegMap as C

import qualified Lang.Crucible.LLVM.DataLayout as C
import qualified Lang.Crucible.LLVM.Extension as C
import qualified Lang.Crucible.LLVM.MemModel as C
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.Translation.Monad as C

import qualified What4.Interface as W4

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
ptrStartsAlloc (C.llvmPointerView -> (_, W4.asBV -> Just (BV.BV 0))) = True
ptrStartsAlloc _ = False

ptrAllocSize ::
  forall sym w.
  C.IsSymInterface sym =>
  G.Mem sym ->
  C.LLVMPtr sym w ->
  Maybe Int
ptrAllocSize mem (C.llvmPointerView -> (blk, _)) = msum $ inAlloc <$> G.memAllocs mem
  where inAlloc :: G.MemAlloc sym -> Maybe Int
        inAlloc memAlloc
          | G.Alloc _ a (Just sz) _ _ _ <- memAlloc
          , Just a == W4.asNat blk =
            fromIntegral <$> BV.asUnsigned <$> W4.asBV sz
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
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.LLVMPtr sym w ->
  IO Bool
ptrIsInitialized sym mem ptr =
  G.readMem sym C.PtrWidth Nothing ptr (C.bitvectorType 1) C.noAlignment mem >>= \case
  C.NoErr{} -> pure True
  _ -> pure False

intrinsicArgProfile ::
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth w) =>
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
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.TypeRepr tp ->
  C.RegValue sym tp ->
  IO ArgProfile
regValueArgProfile sym mem (C.IntrinsicRepr nm ctx) i = intrinsicArgProfile sym mem nm ctx i
regValueArgProfile _ _ _ _ = pure $ ArgProfile Nothing False

regEntryArgProfile ::
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  C.RegEntry sym tp ->
  IO ArgProfile
regEntryArgProfile sym mem (C.RegEntry t v) = regValueArgProfile sym mem t v

newtype Wrap a (b :: C.CrucibleType) = Wrap { unwrap :: a }
argProfiles ::
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth w) =>
  sym ->
  G.Mem sym ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  IO [ArgProfile]
argProfiles sym mem as =
  sequence (Vector.toList $ Ctx.toVector (fmapFC (Wrap . regEntryArgProfile sym mem) as) unwrap)

------------------------------------------------------------------------
-- Execution feature for learning profiles

updateProfiles ::
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth (C.ArchWidth arch)) =>
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
  (C.IsSymInterface sym, C.HasLLVMAnn sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef (Map Text [FunctionProfile]) ->
  IO (C.ExecutionFeature p sym (C.LLVM arch) rtp)
arraySizeProfile llvm profiles = do
  pure . C.ExecutionFeature $ \s -> do
    updateProfiles llvm profiles s
    pure C.ExecutionFeatureNoChange
