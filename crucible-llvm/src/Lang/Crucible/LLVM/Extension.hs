-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Extension
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
--
-- Syntax extension definitions for LLVM
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Extension
  ( module Lang.Crucible.LLVM.Extension.Arch
  , module Lang.Crucible.LLVM.Extension.Syntax
  , LLVM
  ) where

import Data.Data (Data)
import Data.Typeable (Typeable)
import GHC.Generics ( Generic )

import Lang.Crucible.CFG.Extension

import Lang.Crucible.LLVM.Extension.Arch
import Lang.Crucible.LLVM.Extension.Syntax

-- | The Crucible extension type marker for LLVM.
data LLVM mem
  deriving (Data, Eq, Generic , Ord, Typeable)

-- -----------------------------------------------------------------------
-- ** Syntax

type instance ExprExtension (LLVM mem) = LLVMExtensionExpr mem
type instance StmtExtension (LLVM mem) = LLVMStmt mem

instance IsSyntaxExtension (LLVM mem)
