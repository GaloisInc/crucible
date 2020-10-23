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

module Lang.Crucible.VFS.Extension.Syntax
  ( ) where

import          Lang.Crucible.VFS.Extension.Arch



data VFSExtensionExpr (arch :: LLVMArch) :: (CrucibleType -> Type) -> (CrucibleType -> Type)
