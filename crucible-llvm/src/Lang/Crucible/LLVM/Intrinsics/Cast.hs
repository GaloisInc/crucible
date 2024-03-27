-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Cast
-- Description      : Cast between bitvectors and pointers in signatuers
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.LLVM.Intrinsics.Cast
  ( ArgTransformer(applyArgTransformer)
  , ValTransformer(applyValTransformer)
  , transformLLVMArgs
  , transformLLVMRet
  ) where

import           Control.Monad.IO.Class (liftIO)
import           Control.Lens
import qualified Data.Text as Text

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (fmapFC)

import           Lang.Crucible.Backend
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           What4.FunctionName

import           Lang.Crucible.LLVM.MemModel

newtype ArgTransformer p sym ext args args' =
  ArgTransformer { applyArgTransformer :: (forall rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym ext rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym ext tp tp' =
  ValTransformer { applyValTransformer :: (forall rtp l a.
    RegValue sym tp ->
    OverrideSim p sym ext rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall m p sym ext bak args args'.
  (IsSymBackend sym bak, Monad m, HasLLVMAnn sym) =>
  -- | This function name is only used in panic messages.
  FunctionName ->
  bak ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym ext args args')
transformLLVMArgs _fnName _ Ctx.Empty Ctx.Empty =
  return (ArgTransformer (\_ -> return Ctx.Empty))
transformLLVMArgs fnName bak (rest' Ctx.:> tp') (rest Ctx.:> tp) = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformLLVMRet fnName bak tp tp'
                 (ArgTransformer fs) <- transformLLVMArgs fnName bak rest' rest
                 xs' <- fs xs
                 x'  <- RegEntry tp' <$> f (regValue x)
                 pure (xs' Ctx.:> x')))
transformLLVMArgs fnName _ _ _ =
  panic "Intrinsics.transformLLVMArgs"
    [ "transformLLVMArgs: argument shape mismatch!"
    , "in function: " ++ Text.unpack (functionName fnName)
    ]

transformLLVMRet ::
  (IsSymBackend sym bak, Monad m, HasLLVMAnn sym) =>
  -- | This function name is only used in panic messages.
  FunctionName ->
  bak ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ext ret ret')
transformLLVMRet _fnName bak (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . llvmPointer_bv (backendGetSym bak)))
transformLLVMRet _fnName bak (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . projectLLVM_bv bak))
transformLLVMRet fnName bak (VectorRepr tp) (VectorRepr tp')
  = do ValTransformer f <- transformLLVMRet fnName bak tp tp'
       return (ValTransformer (traverse f))
transformLLVMRet fnName bak (StructRepr ctx) (StructRepr ctx')
  = do ArgTransformer tf <- transformLLVMArgs fnName bak ctx' ctx
       return (ValTransformer (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

transformLLVMRet _fnName _bak ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformLLVMRet fnName _bak ret ret'
  = panic "Intrinsics.transformLLVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      , "in function: " ++ Text.unpack (functionName fnName)
      ]

