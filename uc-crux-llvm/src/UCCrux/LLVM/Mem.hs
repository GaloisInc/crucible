{-
Module       : UCCrux.LLVM.Mem
Description  : Utilities for dealing with LLVM memory using UC-Crux concepts
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

Mostly provides wrappers that use 'FullType' instead of Crucible-LLVM's
@MemType@ and @StorageType@ and Crucible's @TypeRepr@.

The difference between the ticked and unticked variants of each function is just
about convenience, for both the case where the caller has a 'FullTypeRepr' for
the pointer type or one for the pointee type. These are inter-convertible in the
presence of a 'ModuleTypes'.

TODO(lb): All of these need a review on how they handle alignment.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Mem
  ( loadRaw,
    loadRaw',
    load,
    load',
    store,
    store',
    storeGlobal,
    storeGlobal',
    loadGlobal,
    loadGlobal',
    seekPtr
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), to)
import           Control.Monad (unless)
import           Data.Maybe (fromMaybe)
import           Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector as Vec

import qualified Text.LLVM.AST as L

-- parameterized-utils
import           Data.Parameterized.Classes (ixF')
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (intValue)

-- what4
import           What4.Interface (Pred)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface, IsSymBackend)
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.MemModel (LLVMPointerType, MemImpl, MemOptions, HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(SeekOffset))
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(..), toCrucibleType, translateIndex)
import           UCCrux.LLVM.FullType.StorageType (toStorageType)
import           UCCrux.LLVM.FullType.Type (ModuleTypes, FullType(FTPtr), FullTypeRepr(..), ToCrucibleType, pointedToType, asFullType)

{- ORMOLU_ENABLE -}

loadRaw ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m atTy ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch atTy)))
loadRaw proxy sym mem ptr fullTypeRepr =
  do let typeRepr = toCrucibleType proxy fullTypeRepr
     partVal <-
       LLVMMem.loadRaw sym mem ptr (toStorageType fullTypeRepr) noAlignment
     case partVal of
       LLVMMem.Err p -> return (p, Nothing)
       LLVMMem.NoErr p ptdToVal ->
         (p,) . Just <$> LLVMMem.unpackMemValue sym typeRepr ptdToVal

loadRaw' ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  ModuleTypes m ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m ('FTPtr atTy) ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch atTy)))
loadRaw' proxy sym mem mts ptr fullTypeRepr =
  let pointedToRepr = pointedToType mts fullTypeRepr
  in loadRaw proxy sym mem ptr pointedToRepr

load ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m atTy ->
  IO (Crucible.RegValue sym (ToCrucibleType arch atTy))
load proxy bak mem ptr fullTypeRepr =
  do let typeRepr = toCrucibleType proxy fullTypeRepr
     LLVMMem.doLoad bak mem ptr (toStorageType fullTypeRepr) typeRepr noAlignment

load' ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  ModuleTypes m ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m ('FTPtr atTy) ->
  IO (Crucible.RegValue sym (ToCrucibleType arch atTy))
load' proxy bak mem mts ptr fullTypeRepr =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     load proxy bak mem ptr pointedToRepr

store ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  FullTypeRepr m ft ->
  -- | Pointer to store at
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  -- | Value to store
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
store proxy bak mem fullTypeRepr ptr regValue =
  do let storageType = toStorageType fullTypeRepr
     let cType = toCrucibleType proxy fullTypeRepr
     LLVMMem.doStore bak mem ptr cType storageType noAlignment regValue

store' ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  -- | Pointer to store at
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  -- | Value to store
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
store' proxy bak mem mts fullTypeRepr ptr regValue =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     store proxy bak mem pointedToRepr ptr regValue

storeGlobal ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  FullTypeRepr m ft ->
  -- | Name of global variable
  L.Symbol ->
  -- | Value to store
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
storeGlobal proxy bak mem fullTypeRepr symb regValue =
  do ptr <- LLVMMem.doResolveGlobal bak mem symb
     store proxy bak mem fullTypeRepr ptr regValue

storeGlobal' ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  -- | Name of global variable
  L.Symbol ->
  -- | Value to store
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
storeGlobal' proxy bak mem mts fullTypeRepr symb regValue =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     storeGlobal proxy bak mem pointedToRepr symb regValue

loadGlobal ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  FullTypeRepr m ft ->
  -- | Name of global variable
  L.Symbol ->
  IO (Crucible.RegValue sym (ToCrucibleType arch ft))
loadGlobal proxy bak mem fullTypeRepr symb =
  do ptr <- LLVMMem.doResolveGlobal bak mem symb
     load proxy bak mem ptr fullTypeRepr

loadGlobal' ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  bak ->
  MemImpl sym ->
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  -- | Name of global variable
  L.Symbol ->
  IO (Crucible.RegValue sym (ToCrucibleType arch ft))
loadGlobal' proxy bak mem mts fullTypeRepr symb =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     loadGlobal proxy bak mem pointedToRepr symb

-- | Find a pointer inside of a value
seekPtr ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  bak ->
  -- | Program memory
  MemImpl sym ->
  -- | Type of value that contains pointer
  FullTypeRepr m inTy ->
  -- | Value containing pointer
  Crucible.RegValue sym (ToCrucibleType arch inTy) ->
  -- | Where the pointer is inside the value
  Cursor m inTy ('FTPtr atTy) ->
  IO (Crucible.RegValue sym (LLVMPointerType (ArchWidth arch)))
seekPtr modCtx bak mem fullTypeRepr regVal cursor =
  case (fullTypeRepr, cursor) of
    (FTArrayRepr _n fullTypeRepr', Index i _ cur) ->
      -- TODO(lb): overflow...?
      let val = regVal !!! fromIntegral (intValue i)
      in seekPtr modCtx bak mem fullTypeRepr' val cur
    (FTStructRepr _structInfo fields, Field _fieldTypes idx cur) ->
      let ty = fields ^. ixF' idx
      in case translateIndex modCtx (Ctx.size fields) idx of
           SomeIndex idx' Refl ->
             let val = regVal ^. ixF' idx' . to Crucible.unRV
             in seekPtr modCtx bak mem ty val cur
    (FTPtrRepr ptRepr, Dereference i cur) ->
      do unless (i == 0) $
           unimplemented "seekPtr" SeekOffset
         newVal <-
           load' modCtx bak mem (modCtx ^. moduleTypes) regVal fullTypeRepr
         let ftPtdTo = asFullType (modCtx ^. moduleTypes) ptRepr
         seekPtr modCtx bak mem ftPtdTo newVal cur
    (FTPtrRepr _ptRepr, Here _) -> return regVal
#if __GLASGOW_HASKELL__ <= 810
-- The pattern match coverage checker was improved in GHC 8.10 and can tell that
-- this case is redundant
    _ -> panic "seekPtr" ["Impossible case"]
#endif
  where v !!! i = fromMaybe (panic "seekPtr" ["Impossible"]) (v Vec.!? i)
