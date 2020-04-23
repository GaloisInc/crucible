-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.VFS.Extension.Syntax
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
--
-- Syntax extension definitions for VFS
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.VFS.Extension.Syntax
  ( VFSExtensionExpr,
    VFSStmt(..)
  ) where

import           Data.Kind
import           GHC.TypeLits
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.TH.GADT as U

import           Lang.Crucible.Types
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.CFG.Extension

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.VFS.Extension.Arch
import           Lang.Crucible.VFS.Types


data VFSExtensionExpr (arch :: VFSArch) :: (CrucibleType -> Type) -> (CrucibleType -> Type)

data VFSStmt (wptr :: Nat) (f :: CrucibleType -> Type) :: CrucibleType -> Type where
  -- | Open a file, returning a fresh file handle pointing to the start of its contents.
  VFS_Open ::
    !(NatRepr wptr)                      {- Pointer width -} ->
    !(GlobalVar Files)                   {- Filesystem global variable -} ->
    !(FileIdent)                         {- Identifier of file to open -} ->
    VFSStmt wptr f (VFSFileHandleType wptr)
  -- | Close a file, marking the given handle as stale
  VFS_Close ::
    !(GlobalVar Files)                   {- Filesystem global variable -} ->
    !(f (VFSFileHandleType wptr))        {- File handle to close -} ->
    VFSStmt wptr f UnitType
  -- | Read a sequence of bytes from a file. The file handle is internally incremented
  -- to point to the end of the sequence.
  VFS_Read ::
    !(GlobalVar Files)                   {- Filesystem global variable -} ->
    !(f (VFSFileHandleType wptr))        {- File handle to read from -} ->
    Bytes                                {- Number of bytes to read -} ->
    VFSStmt wptr f (VectorType (BVType 8))
  -- | Write a sequence of bytes to a file. The file handle is internally incremented
  -- to point to the end of the sequence.
  VFS_Write ::
    !(GlobalVar Files)                   {- Filesystem global variable -} ->
    !(f (VFSFileHandleType wptr))        {- File handle to read from -} ->
    !(f (VectorType (BVType 8)))         {- Byte to write out -} ->
    VFSStmt wptr f UnitType

$(return [])

instance TypeApp (VFSExtensionExpr arch) where
  appType _ = error "appType"

instance PrettyApp (VFSExtensionExpr arch) where
  ppApp _ _ =  error "ppApp"

instance TestEqualityFC (VFSExtensionExpr arch) where
  testEqualityFC _ = error "testEqualityFC"

instance OrdFC (VFSExtensionExpr arch) where
  compareFC _ = error "compareFC"

instance FunctorFC (VFSExtensionExpr arch) where
  fmapFC = fmapFCDefault

instance FoldableFC (VFSExtensionExpr arch) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (VFSExtensionExpr arch) where
  traverseFC _ = error "traverseFC"


instance (1 <= wptr) => TypeApp (VFSStmt wptr) where
  appType = \case
    VFS_Open w _ _ -> VFSFileHandleRepr w
    VFS_Close{} -> knownRepr
    VFS_Read{} -> knownRepr
    VFS_Write{} -> knownRepr

instance PrettyApp (VFSStmt wptr) where
  ppApp pp = \case
    VFS_Open _ vfs fident ->
      text "openFile" <+> text (show vfs) <+> text (show fident)
    VFS_Close vfs fhdl ->
      text "closeHandle" <+> text (show vfs) <+> pp fhdl
    VFS_Read vfs fhdl size ->
      text "readHandle" <+> text (show vfs) <+> pp fhdl <+> text (show size)
    VFS_Write vfs fhdl x ->
      text "writeHandle" <+> text (show vfs) <+> pp fhdl <+> pp x

instance TestEqualityFC (VFSStmt wptr) where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|VFSStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ])

instance OrdFC (VFSStmt wptr) where
  compareFC compareSubterm =
    $(U.structuralTypeOrd [t|VFSStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|compareSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ])

instance FunctorFC (VFSStmt wptr) where
  fmapFC = fmapFCDefault

instance FoldableFC (VFSStmt wptr) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (VFSStmt wptr) where
  traverseFC =
    $(U.structuralTraversal [t|VFSStmt|] [])
