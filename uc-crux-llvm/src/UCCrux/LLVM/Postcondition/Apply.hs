{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-typed-holes #-}

{-
Module       : UCCrux.LLVM.Postcondition.Apply
Description  : Applying function postconditions to LLVM memory
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Postcondition.Apply
  ( applyPostcond
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (zip)

import           Control.Lens ((^.))
import           Control.Monad (foldM)
import           Data.Functor.Product (Product(Pair))
import           Data.IORef (IORef, modifyIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(Proxy))
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some)
import           Data.Parameterized.TraversableFC (foldlMFC)

-- what4
import qualified What4.Interface as What4

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, MemImpl, MemOptions)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (ConstrainedShape)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.Cursor (Selector(..), Cursor(..), deepenPtr, seekType)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(ClobberGlobal))
import           UCCrux.LLVM.FullType.CrucibleType (CrucibleTypeCompat (CrucibleTypeCompat), zip, opaquePointersToCrucibleCompat)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr(..), ToCrucibleType, pointedToType, MapToCrucibleType)
import qualified UCCrux.LLVM.Mem as Mem
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbolToString)
import           UCCrux.LLVM.Postcondition.Type
import           UCCrux.LLVM.Setup (SymValue(getSymValue), generate)
import           UCCrux.LLVM.Setup.Assume (assume)
import           UCCrux.LLVM.Setup.Monad (TypedSelector, runSetup, resultAssumptions, resultMem, resultAnnotations)
import qualified UCCrux.LLVM.Shape as Shape
{- ORMOLU_ENABLE -}

-- | Generate a value, assume result assumptions, record annotations.
genValue ::
  ArchOk arch =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  Crucible.IsSymBackend sym bak =>
  bak ->
  ModuleContext m arch ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | Context for assumptions
  FuncSymbol m ->
  -- | LLVM memory at time of call to function
  MemImpl sym ->
  -- | Location of value to generate
  Selector m argTypes inTy atTy ->
  -- | Type of value to generate
  FullTypeRepr m atTy ->
  -- | Value to generate
  ConstrainedShape m atTy ->
  IO (SymValue sym arch atTy, MemImpl sym)
genValue bak modCtx annotationRef funcSymb mem selector ty spec =
  do (result, value) <-
       runSetup modCtx mem (generate bak modCtx ty selector spec)
     assume (Text.pack (funcSymbolToString funcSymb)) bak (resultAssumptions result)
     -- The keys are nonces, so they'll never clash, so the bias of the union is
     -- unimportant.
     modifyIORef annotationRef (Map.union (resultAnnotations result))
     return (value ^. Shape.tag, resultMem result)

-- | Generate a value that will be used to clobber part of a container
genClobberValue ::
  ArchOk arch =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  Crucible.IsSymBackend sym bak =>
  bak ->
  ModuleContext m arch ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | Function which is doing the clobbering
  FuncSymbol m ->
  -- | LLVM memory at time of call to function
  MemImpl sym ->
  -- | Type of the container
  FullTypeRepr m inTy ->
  -- | Location of the pointer within the value
  Cursor m inTy ('FTPtr atTy) ->
  -- | Constraints on the freshly-created value
  ConstrainedShape m atTy ->
  IO (SymValue sym arch atTy, MemImpl sym)
genClobberValue bak modCtx annotationRef funcSymb mem containerType cursor valSpec =
  do let mts = modCtx ^. moduleTypes
     let selector = SelectClobbered funcSymb (deepenPtr mts cursor)
     let clobberTy = pointedToType mts (seekType mts cursor containerType)
     genValue bak modCtx annotationRef funcSymb mem selector clobberTy valSpec

-- | Clobber a value at a pointer, that is, generate a fresh value and store it
-- to the specified pointer.
--
-- Values are generated via 'UCCrux.LLVM.Setup.generate', see commentary there.
doClobberValue ::
  forall m arch sym bak argTypes inTy.
  ArchOk arch =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  Crucible.IsSymBackend sym bak =>
  bak ->
  ModuleContext m arch ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | Function which is doing the clobbering
  FuncSymbol m ->
  -- | LLVM memory at time of call to function
  MemImpl sym ->
  -- | Specification of what to clobber, and where
  ClobberValue m inTy ->
  -- | Container value which holds the pointer to the value to be clobbered
  Crucible.RegValue sym (ToCrucibleType arch inTy) ->
  IO (MemImpl sym)
doClobberValue bak modCtx annotationRef funcSymb mem clobberVal container =
  do ClobberValue cursor valSpec containerType <- return clobberVal
     (symVal, mem') <-
       genClobberValue bak modCtx annotationRef funcSymb mem containerType cursor valSpec
     Refl <- return (opaquePointersToCrucibleCompat modCtx (Proxy @inTy) containerType)
     ptr <- Mem.seekPtr modCtx bak mem' containerType container cursor
     let mts = modCtx ^. moduleTypes
     let clobberTy = pointedToType mts (seekType mts cursor containerType)
     Mem.store modCtx bak mem' clobberTy ptr (getSymValue symVal)

-- | Generate (via via 'UCCrux.LLVM.Setup.generate') a fresh return value.
genReturnValue ::
  ArchOk arch =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  Crucible.IsSymBackend sym bak =>
  bak ->
  ModuleContext m arch ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | Function which is doing the clobbering
  FuncSymbol m ->
  -- | LLVM memory at time of call to function
  MemImpl sym ->
  -- | Type of to generate
  FS.ReturnTypeRepr m mft ->
  -- | Value to generate
  ReturnValue m mft (ConstrainedShape m) ->
  IO (Crucible.RegValue sym (FS.ReturnTypeToCrucibleType arch mft), MemImpl sym)
genReturnValue bak modCtx annotationRef funcSymb mem retTy retSpec =
  case (retTy, retSpec) of
    (FS.VoidRepr, _) -> return ((), mem)
    (FS.NonVoidRepr retTy', ReturnValue retSpec') ->
      do let selector = SelectReturn funcSymb (Here retTy')
         (val, mem') <-
           genValue bak modCtx annotationRef funcSymb mem selector retTy' retSpec'
         return (getSymValue val, mem')

-- | Apply a function postcondition to an LLVM memory.
--
-- Returns:
--
-- * a return value that conforms to the given postcondition,
-- * LLVM memory after new values have been generated and clobbers have been
--   applied.
--
-- Return values and values used to clobber pointers are generated by
-- 'UCCrux.LLVM.Setup.generate', see commentary there.
applyPostcond ::
  forall m arch sym bak fs va mft args argTypes.
  ArchOk arch =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  (fs ~ 'FS.FuncSig va mft args) =>
  Crucible.IsSymBackend sym bak =>
  bak ->
  ModuleContext m arch ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | Function name
  FuncSymbol m ->
  -- | Function postcondition
  Postcond m fs ->
  -- | Function return type (note that it matches the signature @fs@)
  FS.ReturnTypeRepr m mft ->
  -- | LLVM memory at time of call to function
  MemImpl sym ->
  -- | Arguments to function
  Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch args) ->
  IO (Crucible.RegValue sym (FS.ReturnTypeToCrucibleType arch mft), MemImpl sym)
applyPostcond bak modCtx annotationRef funcSymb postcond retTy mem args =
  do Postcond _va argClobbers globClobbers _ret <- return postcond
     mem' <- foldlMFC clobberArg mem (zip modCtx argClobbers args)
     mem'' <- foldM clobberGlobal mem' globClobbers
     genReturnValue bak modCtx annotationRef funcSymb mem'' retTy (pReturnValue postcond)
  where
    clobberArg ::
      forall ft.
      MemImpl sym ->
      Product (ClobberArg m) (CrucibleTypeCompat arch (Crucible.RegEntry sym)) ft ->
      IO (MemImpl sym)
    clobberArg m =
      \case
        Pair DontClobberArg _ -> return m
        Pair (DoClobberArg spec) (CrucibleTypeCompat arg) ->
          doClobberValue bak modCtx annotationRef funcSymb mem spec (Crucible.regValue arg)

    clobberGlobal ::
      MemImpl sym ->
      SomeClobberValue m ->
      IO (MemImpl sym)
    clobberGlobal _m _ = unimplemented "applyPostcond" ClobberGlobal
