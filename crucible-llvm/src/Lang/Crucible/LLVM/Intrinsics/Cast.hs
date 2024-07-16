-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Cast
-- Description      : Cast between bitvectors and pointers in signatures
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- The built-in overrides in "Lang.Crucible.LLVM.Intrinsics.Libc" and
-- "Lang.Crucible.LLVM.Intrinsics.LLVM" frequently take arguments of type
-- 'Lang.Crucible.Types.BVType', but at runtime everything is represented as an
-- 'Lang.Crucible.LLVM.MemModel.Pointer.LLVMPtr'. This module contains helpers
-- for \"casting\" between pointers and bitvectors.
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
import qualified Data.Text as Text

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (fmapFC)

import           What4.FunctionName (FunctionName (functionName))

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator (SimErrorReason(AssertFailureSimError))
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.MemModel.Partial (ptrToBv)
import           Lang.Crucible.LLVM.MemModel.Pointer

data ValCastError
  = -- | Mismatched number of arguments ('castLLVMArgs') or struct fields
    -- ('castLLVMRet').
    MismatchedShape
    -- | Can\'t cast between these types
  | ValCastError (Some TypeRepr) (Some TypeRepr)

-- | Turn a 'ValCastError' into a human-readable message (lines).
printValCastError :: ValCastError -> [String]
printValCastError =
  \case
    MismatchedShape -> ["argument shape mismatch"]
    ValCastError (Some ret) (Some ret') ->
      [ "Cannot cast types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | A function to (infallibly) cast between 'Ctx.Assignment's of 'RegEntry's.
newtype ArgCast p sym ext args args' =
  ArgCast { applyArgCast :: (forall rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym ext rtp l a (Ctx.Assignment (RegEntry sym) args')) }

-- | A function to (infallibly) cast a value of types @tp@ to @tp'@.
newtype ValCast p sym ext tp tp' =
  ValCast { applyValCast :: (forall rtp l a.
    RegValue sym tp ->
    OverrideSim p sym ext rtp l a (RegValue sym tp')) }

-- | Attempt to construct a function to cast between 'Ctx.Assignment's of
-- 'RegEntry's.
castLLVMArgs :: forall p sym ext bak args args'.
  IsSymBackend sym bak =>
  -- | Only used in error messages
  FunctionName ->
  bak ->
  CtxRepr args' ->
  CtxRepr args ->
  Either ValCastError (ArgCast p sym ext args args')
castLLVMArgs _fnm _ Ctx.Empty Ctx.Empty =
  Right (ArgCast (\_ -> return Ctx.Empty))
castLLVMArgs fnm bak (rest' Ctx.:> tp') (rest Ctx.:> tp) =
  do ValCast f  <- castLLVMRet fnm bak tp tp'
     ArgCast fs <- castLLVMArgs fnm bak rest' rest
     Right (ArgCast
              (\(xs Ctx.:> x) -> do
                    xs' <- fs xs
                    x'  <- f (regValue x)
                    pure (xs' Ctx.:> RegEntry tp' x')))
castLLVMArgs _ _ _ _ = Left MismatchedShape

-- | Attempt to construct a function to cast values of type @ret@ to type
-- @ret'@.
castLLVMRet ::
  IsSymBackend sym bak =>
  -- | Only used in error messages
  FunctionName ->
  bak ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  Either ValCastError (ValCast p sym ext ret ret')
castLLVMRet _fnm bak (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = Right (ValCast (liftIO . llvmPointer_bv (backendGetSym bak)))
castLLVMRet fnm bak (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = let err = 
          AssertFailureSimError
           "Found a pointer where a bitvector was expected"
           ("In the arguments or return value of" ++ Text.unpack (functionName fnm)) in
    Right (ValCast (liftIO . ptrToBv bak err))
castLLVMRet fnm bak (VectorRepr tp) (VectorRepr tp')
  = do ValCast f <- castLLVMRet fnm bak tp tp'
       Right (ValCast (traverse f))
castLLVMRet fnm bak (StructRepr ctx) (StructRepr ctx')
  = do ArgCast tf <- castLLVMArgs fnm bak ctx' ctx
       Right (ValCast (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

castLLVMRet _fnm _bak ret ret'
  | Just Refl <- testEquality ret ret'
  = Right (ValCast return)
castLLVMRet _fnm _bak ret ret' = Left (ValCastError (Some ret) (Some ret'))
