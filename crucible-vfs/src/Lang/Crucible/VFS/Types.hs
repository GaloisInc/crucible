-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.VFS.Types
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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Lang.Crucible.VFS.Types where

import           Data.Typeable
import           GHC.TypeNats
import           Numeric.Natural

import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.Context
import           Data.Parameterized.Classes

import qualified Lang.Crucible.LLVM.Types as M
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Types

newtype FileIdent = FileIdent String
  deriving (Typeable, Eq, Ord, Show)

-- | The 'CrucibleType' of a filesystem, which simply wraps
-- an LLVM memory 'M.Mem'.
type Files = IntrinsicType "VFS_files" EmptyCtx

-- | The 'CrucibleType' of file handles. A file handle is a mutable pointer
-- that increments every time it is read.
type VFSFileHandleType w = ReferenceType (M.LLVMPointerType w)

-- | Symbolic VFS file handle of width @w@.
type VFSFileHandle sym w = RegValue sym (VFSFileHandleType w)


-- | This pattern synonym makes it easy to build and destruct runtime
--   representatives of @'VFSFileHandleType' w@.
pattern VFSFileHandleRepr :: () => (1 <= w, ty ~ VFSFileHandleType w) => NatRepr w -> TypeRepr ty
pattern VFSFileHandleRepr w = ReferenceRepr (M.LLVMPointerRepr w)

pattern FileHandleRepr :: M.HasPtrWidth wptr => (ty ~ VFSFileHandleType wptr) => TypeRepr ty
pattern FileHandleRepr = VFSFileHandleRepr M.PtrWidth

-- | Each open file handle is equivalent to an allocated block
-- in the memory filesystem.
data FileHandleIdent w where
  FileHandleIdent ::
    NatRepr w ->
    Natural ->
    FileHandleIdent w
  deriving (Eq)

$(return [])

instance TestEquality FileHandleIdent where
  testEquality =
    $(U.structuralTypeEquality [t|FileHandleIdent|]
       [ (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|]) ])

instance OrdF FileHandleIdent where
  compareF =
    $(U.structuralTypeOrd [t|FileHandleIdent|]
       [ (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|]) ])
