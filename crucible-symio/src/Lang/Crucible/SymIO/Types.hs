-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.SymIO.Types
-- Description      : Crucible type definitions related to VFS
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.SymIO.Types
  ( symIOIntrinsicTypes
  , FilePointer(..)
  , FilePointerType
  , pattern FilePointerRepr
  , FileHandle
  , FileHandleType
  , pattern FileHandleRepr
  , FileIdent
  , FileIdentType
  , FileSystem(..)
  , FileSystemType
  , FileSystemIndex
  , pattern FileSystemRepr
  , File(..)
  , FileType
  , muxFile
  , DataChunk
  , DataChunkType
  , SizedDataChunk
  , SizedDataChunkType
  )
where

import           Data.Typeable
import           GHC.TypeNats

import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Context
import           Data.Parameterized.Classes

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.Intrinsics

import           What4.Interface
import qualified What4.CachedArray as CA

-- | The intrinsic types used in the symbolic filesystem
symIOIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
symIOIntrinsicTypes = id
  . MapF.insert (knownSymbol :: SymbolRepr "VFS_filesystem") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "VFS_file") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "VFS_filepointer") IntrinsicMuxFn
  $ MapF.empty

-- | An identifier for a file, which must be resolved into a 'File' to access
-- the underlying filesystem.
type FileIdent sym = RegValue sym FileIdentType

-- | The crucible-level type of 'FileIdent'
type FileIdentType = StringType Unicode

-- | The crucible-level type of 'FileSystem'
type FileSystemType w = IntrinsicType "VFS_filesystem" (EmptyCtx ::> BVType w)

-- | Defines the current state of a symbolic filesystem.
data FileSystem sym w =
  FileSystem
    {
      fsPtrSize :: NatRepr w
    , fsFileNames :: RegValue sym (StringMapType (FileType w))
    -- ^ map from concrete file names to identifiers
    , fsFileSizes :: SymArray sym (EmptyCtx ::> BaseIntegerType) (BaseBVType w)
    -- ^ a symbolic map from file identifiers to their size
    , fsSymData :: CA.CachedArray sym (EmptyCtx ::> BaseBVType w ::> BaseIntegerType) (BaseBVType 8)
    -- ^ array representing symbolic file contents
    , fsConstraints :: forall a. ((IsSymInterface sym, 1 <= w) => a) -> a
    }

-- | A base index into the filesystem, consistent of a file identifier and an offset into that file.
type FileSystemIndex sym w = Assignment (SymExpr sym) (EmptyCtx ::> BaseBVType w ::> BaseIntegerType)

instance (IsSymInterface sym) => IntrinsicClass sym "VFS_filesystem" where
  type Intrinsic sym "VFS_filesystem" (EmptyCtx ::> BVType w) = FileSystem sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) p fs1 fs2 = do
    symData <- CA.muxArrays sym p (fsSymData fs1) (fsSymData fs2)
    return $ fs1 { fsSymData  = symData }
  muxIntrinsic _ _ nm ctx _ _ _ = typeError nm ctx

pattern FileSystemRepr :: () => (1 <= w, ty ~ FileSystemType w) => NatRepr w -> TypeRepr ty
pattern FileSystemRepr w <- IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "VFS_filesystem") -> Just Refl)
                                           (Empty :> BVRepr w)
  where
    FileSystemRepr w = IntrinsicRepr knownSymbol (Empty :> BVRepr w)

-- | The crucible type of file handles.
type FileHandleType w = ReferenceType (MaybeType (FilePointerType w))

-- |  A file handle is a mutable file pointer that increments every time it is read.
type FileHandle sym w = RegValue sym (FileHandleType w)

-- | A 'File' represents a file in the filesystem independent
-- of any open handles to it
data File sym w = File (NatRepr w) (SymInteger sym)

-- | The crucible-level type of 'File'
type FileType w = IntrinsicType "VFS_file" (EmptyCtx ::> BVType w)

instance (IsSymInterface sym) => IntrinsicClass sym "VFS_file" where
  type Intrinsic sym "VFS_file" (EmptyCtx ::> BVType w) = File sym w

  muxIntrinsic sym _iTypes _nm (Empty :> BVRepr _w) = muxFile sym
  muxIntrinsic _ _ nm ctx = typeError nm ctx

muxFile ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  File sym w ->
  File sym w ->
  IO (File sym w)
muxFile sym p (File w f1) (File _w f2) = File w <$> baseTypeIte sym p f1 f2

-- | A file pointer represents an index into a particular file.
data FilePointer sym w =
  FilePointer (File sym w) (SymBV sym w) 

-- | The crucible type of 'FilePointer'
type FilePointerType w = IntrinsicType "VFS_filepointer" (EmptyCtx ::> BVType w)

instance (IsSymInterface sym) => IntrinsicClass sym "VFS_filepointer" where
  type Intrinsic sym "VFS_filepointer" (EmptyCtx ::> BVType w) = FilePointer sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) = muxFilePointer sym
  muxIntrinsic _ _ nm ctx = typeError nm ctx

-- | Mux on 'FilePointer'
muxFilePointer ::
  (1 <= w) =>
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  FilePointer sym w ->
  FilePointer sym w ->
  IO (FilePointer sym w)
muxFilePointer sym p (FilePointer f1 off1) (FilePointer f2 off2) =
  do b   <- muxFile sym p f1 f2
     off <- bvIte sym p off1 off2
     return $ FilePointer b off

type DataChunkType w = SymbolicArrayType (EmptyCtx ::> BaseBVType w) (BaseBVType 8)
type DataChunk sym w = SymArray sym (EmptyCtx ::> BaseBVType w) (BaseBVType 8)


type SizedDataChunkType w = SymbolicStructType (EmptyCtx ::> BaseArrayType (EmptyCtx ::> BaseBVType w) (BaseBVType 8) ::> BaseBVType w)
type SizedDataChunk sym w = SymStruct sym (EmptyCtx ::> BaseArrayType (EmptyCtx ::> BaseBVType w) (BaseBVType 8) ::> BaseBVType w)


pattern FileHandleRepr :: () => (1 <= w, ty ~ FileHandleType w) => NatRepr w -> TypeRepr ty
pattern FileHandleRepr w = ReferenceRepr (MaybeRepr (FilePointerRepr w))

pattern FilePointerRepr :: () => (1 <= w, ty ~ FilePointerType w) => NatRepr w -> TypeRepr ty
pattern FilePointerRepr w <- IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "VFS_filepointer") -> Just Refl)
                                           (Empty :> BVRepr w)
  where
    FilePointerRepr w = IntrinsicRepr knownSymbol (Empty :> BVRepr w)



