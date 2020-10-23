-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.VFS.Extension
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
--
-- Syntax extension definitions for VFS
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.VFS.Extension
  ( module Lang.Crucible.VFS.Extension.Syntax
  , VFS
  ) where

import           Data.Data (Data)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic, Generic1)

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.Extension

import           Lang.Crucible.VFS.Extension.Arch

-- | The Crucible extension type marker for LLVM.
data VFS (arch :: LLVMArch)
  deriving (Data, Eq, Generic, Generic1, Ord, Typeable)

-- -----------------------------------------------------------------------
-- ** Syntax

type instance ExprExtension (VFS arch) = LLVMExtensionExpr arch
type instance StmtExtension (VFS arch) = LLVMStmt (ArchWidth arch)

instance (1 <= ArchWidth arch) => IsSyntaxExtension (VFS arch)
