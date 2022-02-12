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
-- Copyright        : (c) Galois, Inc 2020-2022
-- License          : BSD3
-- Maintainer       : Valentin Robert <val@galois.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.Fresh
  ( freshGlobals,
    freshRegMap,
  )
where

import Control.Monad (foldM)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Functor.Const (Const (Const))
import Data.Functor.Product (Product (Pair))
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
  ( TraversableFC (traverseFC),
  )
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.DataLayout (noAlignment)
import Lang.Crucible.LLVM.Globals (GlobalInitializerMap)
import qualified Lang.Crucible.LLVM.MemModel as MemModel
import Lang.Crucible.LLVM.MemType (MemType (IntType))
import Lang.Crucible.LLVM.TypeContext (TypeContext)
import Lang.Crucible.ModelChecker.SallyWhat4 (userSymbol')
import Lang.Crucible.Simulator
  ( RegEntry (RegEntry),
    RegMap (RegMap),
    RegValue,
  )
import qualified Text.LLVM as TL
import qualified What4.Interface as What4
import Lang.Crucible.Backend (HasSymInterface(backendGetSym))

freshGlobals ::
  (?lc :: TypeContext) =>
  MemModel.HasPtrWidth wptr =>
  MemModel.HasLLVMAnn sym =>
  Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  bak ->
  GlobalInitializerMap ->
  MemModel.MemImpl sym ->
  IO (MemModel.MemImpl sym)
freshGlobals bak gimap mem0 = foldM f mem0 (Map.elems gimap)
  where
    f _ (_, Left msg) = fail msg
    f mem (gl, Right (mty, Just _)) = freshGlobal bak gl mty mem
    f _ (_, Right (_, Nothing)) = error "Consider whether to make symbolic global values for uninitialized globals"

-- TODO: consider moving this in Crux?
freshGlobal ::
  (?lc :: TypeContext) =>
  MemModel.HasPtrWidth wptr =>
  MemModel.HasLLVMAnn sym =>
  Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  bak ->
  TL.Global ->
  MemType ->
  MemModel.MemImpl sym ->
  IO (MemModel.MemImpl sym)
freshGlobal bak gl mty mem =
  do
    let sym = backendGetSym bak
    ty <- MemModel.toStorableType mty
    ptr <- MemModel.doResolveGlobal bak mem (TL.globalSym gl)
    llvmVal <- case mty of
      IntType w ->
        do
          case Core.someNat w of
            Just (Core.Some wN) -> do
              case Core.isPosNat wN of
                Just Core.LeqProof -> do
                  -- bitvectors are represented as pointers within "block 0"
                  blk <- What4.natLit sym 0
                  let TL.Symbol s = TL.globalSym gl
                  bv <- What4.freshConstant sym (userSymbol' s) (Core.BaseBVRepr wN)
                  return (MemModel.LLVMValInt blk bv)
                Nothing -> error "Global bitvector width is zero"
            Nothing -> error "Negative natural, this should not happen"
      _ -> error $ "Unhandled type in freshGlobal: " ++ show mty
    MemModel.storeRaw bak mem ptr ty noAlignment llvmVal

-- | Create a fresh register value of the wanted type
freshRegValue ::
  Backend.IsSymInterface sym =>
  sym ->
  String ->
  Core.TypeRepr tp ->
  IO (RegValue sym tp)
freshRegValue sym argName argTypeRepr =
  case argTypeRepr of
    (Core.asBaseType -> Core.AsBaseType bt) ->
      liftIO $ What4.freshConstant sym (userSymbol' argName) bt
    (MemModel.LLVMPointerRepr w) ->
      do
        freshBV <- What4.freshConstant sym (userSymbol' argName) (Core.BaseBVRepr w)
        MemModel.llvmPointer_bv sym freshBV
    _ -> error $ "freshRegValue: unhandled repr " ++ show argTypeRepr

-- | Create a fresh register entry of the wanted type
freshRegEntry ::
  Backend.IsSymInterface sym =>
  sym ->
  String ->
  Core.TypeRepr tp ->
  IO (RegEntry sym tp)
freshRegEntry sym argName argTypeRepr =
  RegEntry argTypeRepr <$> freshRegValue sym argName argTypeRepr

-- | Populate a register map with fresh variables of the appropriate types
freshRegMap ::
  forall sym ctx.
  Backend.IsSymInterface sym =>
  sym ->
  Ctx.Assignment (Const What4.SolverSymbol) ctx ->
  Core.CtxRepr ctx ->
  IO (RegMap sym ctx)
freshRegMap sym nameCtx typeCtx =
  RegMap
    <$> traverseFC
      (\(Pair (Const argName) argTypeRepr) -> freshRegEntry sym (show argName) argTypeRepr)
      (Ctx.zipWith Pair nameCtx typeCtx)
