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
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Intrinsics.Libcxx
  ( register_cpp_override
    -- ** iostream
  , putToOverride12
  , putToOverride9
  , endlOverride
  , sentryOverride
  , sentryBoolOverride
  ) where

import qualified ABI.Itanium as ABI
import           Control.Applicative (empty)
import           Control.Lens ((^.))
import           Control.Monad.Reader
import           Data.List (isInfixOf)
import           Data.Type.Equality ((:~:)(Refl), testEquality)
import qualified Text.LLVM.AST as L

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (knownNat)

import           What4.Interface (bvLit, natLit)

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.RegMap (RegValue, regValue)
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Types (TypeRepr(UnitRepr), CtxRepr)

import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Intrinsics.Common
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Types

------------------------------------------------------------------------
-- ** General

-- | C++ overrides generally have a bit more work to do: their types are more
-- complex, their names are mangled in the LLVM module, it's a big mess.
register_cpp_override ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  SomeCPPOverride p sym arch ->
  OverrideTemplate p sym arch rtp l a
register_cpp_override someCPPOverride =
  OverrideTemplate (SubstringsMatch ("_Z" : cppOverrideSubstrings someCPPOverride)) $
  do (requestedDecl, decName, llvmctx) <- ask
     case decName of
       Nothing -> empty
       Just nm ->
         case cppOverrideAction someCPPOverride requestedDecl nm llvmctx of
           Nothing -> empty
           Just (SomeLLVMOverride override) -> register_llvm_override override


-- type CPPOverride p sym arch args ret =
--   L.Declare -> LLVMContext arch -> Maybe (LLVMOverride p sym arch args ret)

-- | We can only tell whether we should install a C++ override after demangling
--  the function name, which is expensive. As a first approximation, we ask whether
--  the function's name contains a few substrings, in order.
data SomeCPPOverride p sym arch =
  SomeCPPOverride
  { cppOverrideSubstrings :: [String]
  , cppOverrideAction :: L.Declare -> ABI.DecodedName -> LLVMContext arch -> Maybe (SomeLLVMOverride p sym arch)
  }

------------------------------------------------------------------------
-- ** No-ops

------------------------------------------------------------------------
-- *** Utilities

matchSymbolName :: (L.Symbol -> ABI.DecodedName -> Bool)
                -> L.Declare
                -> ABI.DecodedName
                -> Maybe a
                -> Maybe a
matchSymbolName match decl decodedName =
  if not (match (L.decName decl) decodedName)
  then const Nothing
  else id

panic_ :: (Show a, Show b)
       => String
       -> L.Declare
       -> a
       -> b
       -> c
panic_ from decl args ret =
  panic from [ "Ill-typed override"
             , "Name: " ++ nm
             , "Args: " ++ show args
             , "Ret:  " ++ show ret
             ]
  where L.Symbol nm = L.decName decl

-- | If the requested declaration's symbol matches the filter, look up its
-- function handle in the symbol table and use that to construct an override
mkOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
           => [String] -- ^ Substrings for name filtering
           -> (forall args ret. L.Declare -> CtxRepr args -> TypeRepr ret -> Maybe (SomeLLVMOverride p sym arch))
           -> (L.Symbol -> ABI.DecodedName -> Bool)
           -> SomeCPPOverride p sym arch
mkOverride substrings ov filt =
  SomeCPPOverride substrings $ \requestedDecl decodedName llvmctx ->
    let ?lc = llvmctx^.llvmTypeCtx in
    matchSymbolName filt requestedDecl decodedName $
      llvmDeclToFunHandleRepr' requestedDecl $ \argTys retTy ->
        ov requestedDecl argTys retTy

------------------------------------------------------------------------
-- *** No-op override builders

-- | Make an override for a function which doesn't return anything.
voidOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
             => [String]
             -> (L.Symbol -> ABI.DecodedName -> Bool)
             -> SomeCPPOverride p sym arch
voidOverride substrings =
  mkOverride substrings $ \decl argTys retTy -> Just $
      case retTy of
        UnitRepr -> SomeLLVMOverride $ LLVMOverride decl argTys retTy $ \_mem _sym _args -> pure ()
        _ -> panic_ "voidOverride" decl argTys retTy

-- | Make an override for a function of (LLVM) type @a -> a@, for any @a@.
--
-- The override simply returns its input.
identityOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
                 => [String]
                 -> (L.Symbol -> ABI.DecodedName -> Bool)
                 -> SomeCPPOverride p sym arch
identityOverride substrings =
  mkOverride substrings $ \decl argTys retTy -> Just $
    case argTys of
      (Ctx.Empty Ctx.:> argTy)
        | Just Refl <- testEquality argTy retTy ->
            SomeLLVMOverride $ LLVMOverride decl argTys retTy $ \_mem _sym args ->
              -- Just return the input
              pure (Ctx.uncurryAssignment regValue args)

      _ -> panic_ "identityOverride" decl argTys retTy

-- | Make an override for a function of (LLVM) type @a -> b -> a@, for any @a@.
--
-- The override simply returns its first input.
constOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
              => [String]
              -> (L.Symbol -> ABI.DecodedName -> Bool)
              -> SomeCPPOverride p sym arch
constOverride substrings =
  mkOverride substrings $ \decl argTys retTy -> Just $
    case argTys of
      (Ctx.Empty Ctx.:> fstTy Ctx.:> _)
        | Just Refl <- testEquality fstTy retTy ->
        SomeLLVMOverride $ LLVMOverride decl argTys retTy $ \_mem _sym args ->
          pure (Ctx.uncurryAssignment (const . regValue) args)

      _ -> panic_ "constOverride" decl argTys retTy

-- | Make an override that always returns the same value.
fixedOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
              => TypeRepr ty
              -> (GlobalVar Mem -> sym -> IO (RegValue sym ty))
              -> [String]
              -> (L.Symbol -> ABI.DecodedName -> Bool)
              -> SomeCPPOverride p sym arch
fixedOverride ty regval substrings =
  mkOverride substrings $ \decl argTys retTy -> Just $
    case testEquality retTy ty of
      Just Refl ->
        SomeLLVMOverride $ LLVMOverride decl argTys retTy $ \mem sym _args ->
          liftIO (regval mem sym)

      _ -> panic_ "fixedOverride" decl argTys retTy

-- | Return @true@.
trueOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
             => [String]
             -> (L.Symbol -> ABI.DecodedName -> Bool)
             -> SomeCPPOverride p sym arch
trueOverride =
  fixedOverride (LLVMPointerRepr knownNat) $ \_mem sym ->
    LLVMPointer <$> natLit sym 0 <*> bvLit sym (knownNat @1) (BV.one knownNat)

------------------------------------------------------------------------
-- ** Declarations

------------------------------------------------------------------------
-- *** iostream

------------------------------------------------------------------------
-- **** basic_ostream

-- | Override for the \"put to\" operator, @<<@
--
-- This is the override for the 12th function signature listed here:
-- https://en.cppreference.com/w/cpp/io/basic_ostream/operator_ltlt
putToOverride12 :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
                => SomeCPPOverride p sym arch
putToOverride12 =
  constOverride ["St","ls","basic_ostream"] $ \_ decodedName ->
    case decodedName of
      ABI.Function
         (ABI.NestedName
          []
          [ ABI.SubstitutionPrefix ABI.SubStdNamespace
          , _
          , ABI.UnqualifiedPrefix (ABI.SourceName "basic_ostream")
          , ABI.TemplateArgsPrefix _
          ]
          (ABI.OperatorName ABI.OpShl))
          [ABI.PointerToType (ABI.FunctionType _)] -> True
      _ -> False

-- | Override for the \"put to\" operator, @<<@
--
-- This is the override for the 9th function signature listed here (I think):
-- https://en.cppreference.com/w/cpp/io/basic_ostream/operator_ltlt
putToOverride9 :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
               => SomeCPPOverride p sym arch
putToOverride9 =
  constOverride ["NSt3__1lsINS_11char_traitsIcEEEERNS_13basic_ostreamIcT_EES6_PKc"] $ \(L.Symbol nm) _ ->
    nm == "_ZNSt3__1lsINS_11char_traitsIcEEEERNS_13basic_ostreamIcT_EES6_PKc"

-- | TODO: When @itanium-abi@ get support for parsing templates, make this a
-- more structured match
endlOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
             => SomeCPPOverride p sym arch
endlOverride =
  identityOverride ["endl","char_traits","basic_ostream"] $ \(L.Symbol nm) _decodedName ->
    and [ "endl"          `isInfixOf` nm
        , "char_traits"   `isInfixOf` nm
        , "basic_ostream" `isInfixOf` nm
        ]

sentryOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
               => SomeCPPOverride p sym arch
sentryOverride =
  voidOverride ["basic_ostream", "sentry"] $ \_nm decodedName ->
    case decodedName of
      ABI.Function
         (ABI.NestedName
          []
          [ ABI.SubstitutionPrefix ABI.SubStdNamespace
          , _
          , ABI.UnqualifiedPrefix (ABI.SourceName "basic_ostream")
          , _
          , ABI.UnqualifiedPrefix (ABI.SourceName "sentry")
          ]
          _)
         _ -> True
      _ -> False

-- | An override of the @bool@ operator (cast) on the @sentry@ class,
--
-- @sentry::operator bool()@
sentryBoolOverride :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
                   => SomeCPPOverride p sym arch
sentryBoolOverride =
  trueOverride ["basic_ostream", "sentry"] $ \_nm decodedName ->
    case decodedName of
      ABI.Function
         (ABI.NestedName
          [ABI.Const]
          [ ABI.SubstitutionPrefix ABI.SubStdNamespace
          , _
          , ABI.UnqualifiedPrefix (ABI.SourceName "basic_ostream")
          , _
          , ABI.UnqualifiedPrefix (ABI.SourceName "sentry")
          ]
          (ABI.OperatorName (ABI.OpCast ABI.BoolType)))
          [ABI.VoidType] -> True
      _ -> False
