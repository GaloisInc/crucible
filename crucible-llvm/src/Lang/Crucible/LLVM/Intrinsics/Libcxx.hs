-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libcxx
-- Description      : Override definitions for C++ standard library functions
-- Copyright        : (c) Galois, Inc 2015-2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.Libcxx where

import           Control.Applicative (empty)
import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Map.Strict as Map
import           Data.List (isInfixOf)
import           Data.Type.Equality ((:~:)(Refl), testEquality)
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.Backend
import           Lang.Crucible.FunctionHandle (handleArgTypes, handleReturnType)
import           Lang.Crucible.Simulator.RegMap (regValue)
import           Lang.Crucible.Panic (panic)

import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel

import           Lang.Crucible.LLVM.Intrinsics.Common

------------------------------------------------------------------------
-- ** General

-- | C++ overrides generally have a bit more work to do: their types are more
-- complex, their names are mangled in the LLVM module, it's a big mess.
register_cpp_override ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  SomeCPPOverride p sym arch ->
  RegOverrideM p sym arch rtp l a ()
register_cpp_override someCPPOverride = do
  requestedDecl <- ask
  llvmctx       <- get
  case someCPPOverride requestedDecl llvmctx of
    Just (SomeLLVMOverride override) -> register_llvm_override override
    Nothing                          -> empty

type CPPOverride p sym arch args ret =
  L.Declare -> LLVMContext arch -> Maybe (LLVMOverride p sym arch args ret)

type SomeCPPOverride p sym arch =
  L.Declare -> LLVMContext arch -> Maybe (SomeLLVMOverride p sym arch)

------------------------------------------------------------------------
-- ** Declarations

-- | Make an override for an arbitrary function of (LLVM) type @a -> a@, for any @a@.
--
-- The override simply returns its input.
identityOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
                 => (L.Symbol -> Bool)
                 -> SomeCPPOverride p sym arch
identityOverride filt requestedDecl llvmctx =
  let symbName@(L.Symbol textName) = L.decName requestedDecl
  in
    if not (filt symbName)
    then Nothing
    else
      case (Map.lookup symbName (llvmctx ^. symbolMap)) of
        Just (LLVMHandleInfo decl hand) -> Just $
          let (args, ret) = (handleArgTypes hand, handleReturnType hand)
          in case (args, ret) of
               (Ctx.Empty Ctx.:> ty1, ty2) | Just Refl <- testEquality ty1 ty2 ->
                 SomeLLVMOverride $ LLVMOverride decl args ret $ \_mem _sym args' ->
                   -- Just return the input
                   pure (Ctx.uncurryAssignment regValue args')

               _ -> panic "identityOverride" [ "Ill-typed identity override"
                                             , "Name:" ++ textName
                                             , "Args:" ++ show args
                                             , "Ret: " ++ show ret
                                             ]
        _ -> Nothing

endlOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
             => SomeCPPOverride p sym arch
endlOverride =
  identityOverride $ \(L.Symbol nm) ->
    and [ "endl"          `isInfixOf` nm
        , "char_traits"   `isInfixOf` nm
        , "basic_ostream" `isInfixOf` nm
        ]
