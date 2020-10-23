------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.VFS.Extension.Arch
-- Description      : Representation of VFS-supporting architectures
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.SymIO.Extension.Arch
  ( type VFSArch ) where

import Lang.Crucible.LLVM.Extension

type VFSArch = LLVMArch
