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
  , ArgTransformer(applyArgTransformer)
  , ValTransformer(applyValTransformer)
  , transformLLVMArgs
  , transformLLVMRet
  ) where

import           Control.Monad.IO.Class (liftIO)
import           Control.Lens
import           Data.Either.Extra (mapLeft)
import qualified Data.Text as Text
import           Data.Vector (Vector)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (fmapFC)

import           Lang.Crucible.Backend
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           What4.FunctionName

import           Lang.Crucible.LLVM.MemModel

data ValCastError
  = MismatchedShape
  | ValCastError (Some TypeRepr) (Some TypeRepr)

printValCastError :: ValCastError -> [String]
printValCastError =
  \case
    MismatchedShape -> ["argument shape mismatch"]
    ValCastError (Some ret) (Some ret') ->
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

newtype ArgTransformer p sym ext args args' =
  ArgTransformer { applyArgTransformer :: (forall rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym ext rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym ext tp tp' =
  ValTransformer { applyValTransformer :: (forall rtp l a.
    RegValue sym tp ->
    OverrideSim p sym ext rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall p sym ext bak args args'.
  (IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  CtxRepr args' ->
  CtxRepr args ->
  Either ValCastError (ArgTransformer p sym ext args args')
transformLLVMArgs _ Ctx.Empty Ctx.Empty =
  Right (ArgTransformer (\_ -> return Ctx.Empty))
transformLLVMArgs bak (rest' Ctx.:> tp') (rest Ctx.:> tp) =
  do (ValTransformer f)  <- transformLLVMRet bak tp tp'
     (ArgTransformer fs) <- transformLLVMArgs bak rest' rest
     Right (ArgTransformer
              (\(xs Ctx.:> x) -> do
                    xs' <- fs xs
                    x'  <- f (regValue x)
                    pure (xs' Ctx.:> RegEntry tp' x')))
transformLLVMArgs _ _ _ = Left MismatchedShape

transformLLVMRet ::
  (IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  Either ValCastError (ValTransformer p sym ext ret ret')
transformLLVMRet bak (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = Right (ValTransformer (liftIO . llvmPointer_bv (backendGetSym bak)))
transformLLVMRet bak (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = Right (ValTransformer (liftIO . projectLLVM_bv bak))
transformLLVMRet bak (VectorRepr tp) (VectorRepr tp')
  = do ValTransformer f <- transformLLVMRet bak tp tp'
       Right (ValTransformer (traverse f))
transformLLVMRet bak (StructRepr ctx) (StructRepr ctx')
  = do ArgTransformer tf <- transformLLVMArgs bak ctx' ctx
       Right (ValTransformer (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

transformLLVMRet _bak ret ret'
  | Just Refl <- testEquality ret ret'
  = Right (ValTransformer return)
transformLLVMRet _bak ret ret' = Left (ValCastError (Some ret) (Some ret'))
