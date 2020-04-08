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
  ( freshRegMap,
  )
where

import Control.Monad.IO.Class
import Data.Functor.Const
import Data.Functor.Product
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.Simulator
import What4.Interface

userSymbol' :: String -> SolverSymbol
userSymbol' s = case userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

-- | Create a fresh register value according to the wanted type
freshRegValue ::
  Backend.IsSymInterface sym =>
  sym ->
  String ->
  Core.TypeRepr tp ->
  IO (RegValue sym tp)
freshRegValue sym argName argTypeRepr =
  case argTypeRepr of
    (Core.asBaseType -> Core.AsBaseType bt) ->
      liftIO $ freshConstant sym (userSymbol' argName) bt
    (LLVMPointerRepr w) ->
      do
        freshBV <- freshBoundedBV sym (userSymbol' argName) w Nothing Nothing
        llvmPointer_bv sym freshBV
    _ -> error $ "freshRegValue: unhandled repr " ++ show argTypeRepr

-- | Create a fresh register entry according to the wanted type
freshRegEntry ::
  Backend.IsSymInterface sym =>
  sym ->
  String ->
  Core.TypeRepr tp ->
  IO (RegEntry sym tp)
freshRegEntry sym argName argTypeRepr =
  RegEntry argTypeRepr <$> freshRegValue sym argName argTypeRepr

-- | Populate a register map with fresh variables for the appropriate types
freshRegMap ::
  forall sym ctx.
  Backend.IsSymInterface sym =>
  sym ->
  Ctx.Assignment (Const String) ctx ->
  Core.CtxRepr ctx ->
  IO (RegMap sym ctx)
freshRegMap sym nameCtx typeCtx =
  RegMap
    <$> traverseFC
      (\(Pair (Const argName) argTypeRepr) -> freshRegEntry sym argName argTypeRepr)
      (Ctx.zipWith Pair nameCtx typeCtx)
