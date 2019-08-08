------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.ArraySizeProfile
-- Description      : Execution feature to observe argument buffer sizes
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Andrei Stefanescu <andrei@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# OPTIONS -Wall -Werror #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.ArraySizeProfile
  ( Profile
  , arraySizeProfile
  ) where

import Control.Lens (view)

import Data.Type.Equality ((:~:)(..))
import Data.Foldable (msum)
import Data.Text (Text, pack)
import qualified Data.Vector as Vector
import Data.Parameterized.SymbolRepr (SymbolRepr, knownSymbol)
import Data.Parameterized.Classes (testEquality)
import Data.Parameterized.Context (Assignment, toVector, pattern Empty, pattern (:>))
import Data.Parameterized.TraversableFC (fmapFC)
import Data.IORef (IORef, modifyIORef')

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Simulator.BoundedExec as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.RegMap as C

import qualified Lang.Crucible.LLVM.Extension as C
import qualified Lang.Crucible.LLVM.Intrinsics.Common as C
import qualified Lang.Crucible.LLVM.MemModel as C

import qualified Lang.Crucible.LLVM.MemModel.Generic as G

import What4.Interface (IsExpr, IsExprBuilder, SymExpr, asNat, asUnsignedBV)

type Profile = (Text, [[Maybe Int]])

ptrStartsAlloc ::
  IsExpr (SymExpr sym) =>
  C.LLVMPtr sym w ->
  Maybe ()
ptrStartsAlloc (C.llvmPointerView -> (_, asUnsignedBV -> Just 0)) = Just ()
ptrStartsAlloc _ = Nothing

ptrAllocSize ::
  forall sym w. IsExpr (SymExpr sym) =>
  [G.MemAlloc sym] ->
  C.LLVMPtr sym w ->
  Maybe Int
ptrAllocSize mem (C.llvmPointerView -> (blk, _)) = msum $ inAlloc <$> mem
  where inAlloc :: G.MemAlloc sym -> Maybe Int
        inAlloc (G.Alloc _ _ Nothing _ _ _) = Nothing
        inAlloc (G.Alloc _ a (Just size) _ _ _) = do
          blk' <- asNat blk
          if a == blk'
            then fromIntegral <$> asUnsignedBV size
            else Nothing
        inAlloc _ = Nothing

ptrIsArray :: IsExpr (SymExpr sym) =>
              [G.MemAlloc sym] ->
              C.LLVMPtr sym w ->
              Maybe Int
ptrIsArray mem ptr = ptrStartsAlloc ptr *> ptrAllocSize mem ptr

intrinsicIsArray ::
  IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  SymbolRepr nm ->
  C.CtxRepr ctx ->
  C.Intrinsic sym nm ctx ->
  Maybe Int
intrinsicIsArray mem
  (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
  (Empty :> C.BVRepr _w) i = ptrIsArray mem i
intrinsicIsArray _ _ _ _ = Nothing

regValueIsArray ::
  IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  C.TypeRepr tp ->
  C.RegValue sym tp ->
  Maybe Int
regValueIsArray mem (C.IntrinsicRepr nm ctx) i = intrinsicIsArray mem nm ctx i
regValueIsArray _ _ _ = Nothing

regEntryIsArray ::
  IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  C.RegEntry sym tp ->
  Maybe Int
regEntryIsArray mem (C.RegEntry t v) = regValueIsArray mem t v

newtype Wrap a (b :: C.CrucibleType) = Wrap { unwrap :: a }
argArraySizes ::
  IsExprBuilder sym =>
  [G.MemAlloc sym] ->
  Assignment (C.RegEntry sym) ctx ->
  [Maybe Int]
argArraySizes mem as = Vector.toList $ toVector (fmapFC (Wrap . regEntryIsArray mem) as) unwrap

arraySizeProfile ::
  (C.IsSymInterface sym, C.HasPtrWidth (C.ArchWidth arch)) =>
  C.LLVMContext arch ->
  IORef [Profile] ->
  IO (C.ExecutionFeature p sym (C.LLVM arch) rtp)
arraySizeProfile llvm cell = do
  be <- C.runExecutionFeature . C.genericToExecutionFeature
        <$> C.boundedExecFeature (const . pure $ Just 0) False
  pure . C.ExecutionFeature $ \s -> do
    case s of
      C.CallState _
        (C.CrucibleCall _
          C.CallFrame { C._frameCFG = g
                      , C._frameRegs = regs
                      }) sim ->
        let globals = view (C.stateTree . C.actFrame . C.gpGlobals) sim
        in case C.memImplHeap <$> C.lookupGlobal (C.llvmMemVar llvm) globals of
          Nothing -> pure ()
          Just mem -> do
            modifyIORef' cell $ \profs ->
              let name = pack . show $ C.cfgHandle g
                  sizes = argArraySizes (G.memAllocs mem) $ C.regMap regs
              in case lookup name profs of
                Nothing -> (name, [sizes]):profs
                Just variants
                  | sizes `elem` variants -> profs
                  | otherwise -> (name, sizes:variants):filter ((/= name) . fst) profs
      _ -> pure ()
    be s
