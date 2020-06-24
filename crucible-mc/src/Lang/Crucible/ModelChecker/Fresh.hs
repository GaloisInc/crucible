{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.Fresh
-- Description      : Helpers to create fresh symbolic values
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.Fresh
  ( freshGlobals,
    freshRegMap,
  )
where

import Control.Monad (foldM)
import Control.Monad.IO.Class
import Data.Functor.Const
import Data.Functor.Product
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.CFG.Core
import Lang.Crucible.LLVM.DataLayout (noAlignment)
import Lang.Crucible.LLVM.Globals
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.MemType
import Lang.Crucible.LLVM.TypeContext
import Lang.Crucible.ModelChecker.SallyWhat4
import Lang.Crucible.Simulator
import qualified Text.LLVM as TL
import qualified What4.Interface as What4

freshGlobals ::
  (?lc :: TypeContext) =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  Backend.IsSymInterface sym =>
  sym ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
freshGlobals sym gimap mem0 = foldM f mem0 (Map.elems gimap)
  where
    f _ (_, Left msg) = fail msg
    f mem (gl, Right (mty, Just _)) = freshGlobal sym gl mty mem
    f _ (_, Right (_, Nothing)) = error "Consider whether to make symbolic global values for uninitialized globals"

-- TODO: consider moving this in Crux?
freshGlobal ::
  (?lc :: TypeContext) =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  Backend.IsSymInterface sym =>
  sym ->
  TL.Global ->
  MemType ->
  MemImpl sym ->
  IO (MemImpl sym)
freshGlobal sym gl mty mem =
  do
    ty <- toStorableType mty
    ptr <- doResolveGlobal sym mem (TL.globalSym gl)
    llvmVal <- case mty of
      IntType w ->
        do
          case someNat w of
            Just (Core.Some wN) -> do
              case isPosNat wN of
                Just LeqProof -> do
                  -- bitvectors are represented as pointers within "block 0"
                  blk <- What4.natLit sym 0
                  let TL.Symbol s = TL.globalSym gl
                  bv <- What4.freshConstant sym (userSymbol' s) (BaseBVRepr wN)
                  return (LLVMValInt blk bv)
                Nothing -> error "Global bitvector width is zero"
            Nothing -> error "Negative natural, this should not happen"
      _ -> error $ "Unhandled type in freshGlobal: " ++ show mty
    storeRaw sym mem ptr ty noAlignment llvmVal

-- | Create a fresh register value of the wanted type
freshRegValue ::
  Backend.IsSymInterface sym =>
  sym ->
  String ->
  TypeRepr tp ->
  IO (RegValue sym tp)
freshRegValue sym argName argTypeRepr =
  case argTypeRepr of
    (asBaseType -> AsBaseType bt) ->
      liftIO $ What4.freshConstant sym (userSymbol' argName) bt
    (LLVMPointerRepr w) ->
      do
        freshBV <- What4.freshConstant sym (userSymbol' argName) (BaseBVRepr w)
        llvmPointer_bv sym freshBV
    _ -> error $ "freshRegValue: unhandled repr " ++ show argTypeRepr

-- | Create a fresh register entry of the wanted type
freshRegEntry ::
  Backend.IsSymInterface sym =>
  sym ->
  String ->
  TypeRepr tp ->
  IO (RegEntry sym tp)
freshRegEntry sym argName argTypeRepr =
  RegEntry argTypeRepr <$> freshRegValue sym argName argTypeRepr

-- | Populate a register map with fresh variables of the appropriate types
freshRegMap ::
  forall sym ctx.
  Backend.IsSymInterface sym =>
  sym ->
  Ctx.Assignment (Const What4.SolverSymbol) ctx ->
  CtxRepr ctx ->
  IO (RegMap sym ctx)
freshRegMap sym nameCtx typeCtx =
  RegMap
    <$> traverseFC
      (\(Pair (Const argName) argTypeRepr) -> freshRegEntry sym (show argName) argTypeRepr)
      (Ctx.zipWith Pair nameCtx typeCtx)
