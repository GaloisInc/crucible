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

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.SymIO.Types where

import           Data.Typeable
import           GHC.TypeNats

import           Data.Map ( Map ) 
import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.Context
import           Data.Parameterized.Classes

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.Intrinsics

import           What4.Interface
import qualified What4.CachedArray as CA

newtype FileIdent = FileIdent String
  deriving (Typeable, Eq, Ord, Show)


type FileSystemType w = IntrinsicType "VFS_filesystem" (EmptyCtx ::> BVType w)

data FileSystem sym w =
  FileSystem
    {
      fsPtrSize :: NatRepr w
    , fsFileNames :: Map FileIdent Integer
    -- ^ map from concrete file names to identifiers
    , fsFileSizes :: SymArray sym (EmptyCtx ::> BaseIntegerType) (BaseBVType w)
    -- ^ a symbolic map from file identifiers to their size
    , fsSymData :: CA.CachedArray sym (EmptyCtx ::> BaseIntegerType ::> BaseBVType w) (BaseBVType 8)
    -- ^ array representing symbolic file contents
    , fsConstraints :: forall a. ((IsSymInterface sym, 1 <= w) => a) -> a
    }

type FileSystemIndex sym w = Assignment (SymExpr sym) (EmptyCtx ::> BaseIntegerType ::> BaseBVType w)

instance (IsSymInterface sym) => IntrinsicClass sym "VFS_filesystem" where
  type Intrinsic sym "VFS_filesystem" (EmptyCtx ::> BVType w) = FileSystem sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) p fs1 fs2 = do
    symData <- CA.muxArrays sym p (fsSymData fs1) (fsSymData fs2)
    return $ fs1 { fsSymData  = symData }
  muxIntrinsic _ _ nm ctx _ _ _ = typeError nm ctx

-- | The 'CrucibleType' of file handles. A file handle is a mutable pointer
-- that increments every time it is read.
type FileHandleType w = ReferenceType (MaybeType (FilePointerType w))

type FileHandle sym w = RegValue sym (FileHandleType w)

-- | A 'File' represents a file in the filesystem independent
-- of any open handles to it
data File sym w = File (NatRepr w) (SymInteger sym)

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

-- | A file pointer represents an index into a particular file
data FilePointer sym w =
  FilePointer (File sym w) (SymBV sym w) 

data ConcreteFile w = ConcreteFile (NatRepr w) Integer

data ConcreteFilePointer w = ConcreteFilePointer (ConcreteFile w) (BV.BV w)

type FilePointerType w = IntrinsicType "VFS_filepointer" (EmptyCtx ::> BVType w)

instance (IsSymInterface sym) => IntrinsicClass sym "VFS_filepointer" where
  type Intrinsic sym "VFS_filepointer" (EmptyCtx ::> BVType w) = FilePointer sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) = muxFilePointer sym
  muxIntrinsic _ _ nm ctx = typeError nm ctx

-- | Mux function specialized to file pointers values.
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

-- | A 'chunk' of data resulting from a read or write, with
-- a symbolic size
data DataChunk sym w =
  DataChunk
    { chunkArray :: SymArray sym (EmptyCtx ::> BaseBVType w) (BaseBVType 8)
    , chunkSize :: SymBV sym w
    }

type DataChunkType w = IntrinsicType "VFS_datachunk" (EmptyCtx ::> BVType w)

muxDataChunk ::
  (1 <= w) =>
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  DataChunk sym w ->
  DataChunk sym w ->
  IO (DataChunk sym w)
muxDataChunk sym p (DataChunk d1 sz1) (DataChunk d2 sz2) = do
  d <- baseTypeIte sym p d1 d2
  sz <- baseTypeIte sym p sz1 sz2
  return $ DataChunk d sz


instance (IsSymInterface sym) => IntrinsicClass sym "VFS_datachunk" where
  type Intrinsic sym "VFS_datachunk" (EmptyCtx ::> BVType w) = DataChunk sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) = muxDataChunk sym
  muxIntrinsic _ _ nm ctx = typeError nm ctx

pattern FileHandleRepr :: () => (1 <= w, ty ~ FileHandleType w) => NatRepr w -> TypeRepr ty
pattern FileHandleRepr w = ReferenceRepr (MaybeRepr (FilePointerRepr w))

pattern FilePointerRepr :: () => (1 <= w, ty ~ FilePointerType w) => NatRepr w -> TypeRepr ty
pattern FilePointerRepr w <- IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "VFS_filepointer") -> Just Refl)
                                           (Empty :> BVRepr w)
  where
    FilePointerRepr w = IntrinsicRepr knownSymbol (Empty :> BVRepr w)



