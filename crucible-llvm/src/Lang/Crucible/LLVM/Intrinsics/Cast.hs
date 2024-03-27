-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Cast
-- Description      : Cast between bitvectors and pointers in signatuers
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.LLVM.Intrinsics.Cast
  ( ValCastError
  , printValCastError
  , ArgCast(applyArgCast)
  , ValCast(applyValCast)
  , castLLVMArgs
  , castLLVMRet
  ) where

import           Control.Monad.IO.Class (liftIO)
import           Control.Lens

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (fmapFC)

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.MemModel

data ValCastError
  = MismatchedShape
  | ValCastError (Some TypeRepr) (Some TypeRepr)

printValCastError :: ValCastError -> [String]
printValCastError =
  \case
    MismatchedShape -> ["argument shape mismatch"]
    ValCastError (Some ret) (Some ret') ->
      [ "Cannot cast types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

newtype ArgCast p sym ext args args' =
  ArgCast { applyArgCast :: (forall rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym ext rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValCast p sym ext tp tp' =
  ValCast { applyValCast :: (forall rtp l a.
    RegValue sym tp ->
    OverrideSim p sym ext rtp l a (RegValue sym tp')) }

castLLVMArgs :: forall p sym ext bak args args'.
  (IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  CtxRepr args' ->
  CtxRepr args ->
  Either ValCastError (ArgCast p sym ext args args')
castLLVMArgs _ Ctx.Empty Ctx.Empty =
  Right (ArgCast (\_ -> return Ctx.Empty))
castLLVMArgs bak (rest' Ctx.:> tp') (rest Ctx.:> tp) =
  do (ValCast f)  <- castLLVMRet bak tp tp'
     (ArgCast fs) <- castLLVMArgs bak rest' rest
     Right (ArgCast
              (\(xs Ctx.:> x) -> do
                    xs' <- fs xs
                    x'  <- f (regValue x)
                    pure (xs' Ctx.:> RegEntry tp' x')))
castLLVMArgs _ _ _ = Left MismatchedShape

castLLVMRet ::
  (IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  Either ValCastError (ValCast p sym ext ret ret')
castLLVMRet bak (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = Right (ValCast (liftIO . llvmPointer_bv (backendGetSym bak)))
castLLVMRet bak (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = Right (ValCast (liftIO . projectLLVM_bv bak))
castLLVMRet bak (VectorRepr tp) (VectorRepr tp')
  = do ValCast f <- castLLVMRet bak tp tp'
       Right (ValCast (traverse f))
castLLVMRet bak (StructRepr ctx) (StructRepr ctx')
  = do ArgCast tf <- castLLVMArgs bak ctx' ctx
       Right (ValCast (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

castLLVMRet _bak ret ret'
  | Just Refl <- testEquality ret ret'
  = Right (ValCast return)
castLLVMRet _bak ret ret' = Left (ValCastError (Some ret) (Some ret'))
