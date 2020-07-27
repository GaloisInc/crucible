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

module Lang.Crucible.LLVM.Extension
  ( module Lang.Crucible.LLVM.Extension.Arch
  , module Lang.Crucible.LLVM.Extension.Syntax
  , LLVM
  ) where

import           Data.Data (Data)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic, Generic1)

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.Extension.Arch
import           Lang.Crucible.LLVM.Extension.Syntax

-- | The Crucible extension type marker for LLVM.
data LLVM (arch :: LLVMArch)
  deriving (Data, Eq, Generic, Generic1, Ord, Typeable)

-- -----------------------------------------------------------------------
-- ** Syntax

type instance ExprExtension (LLVM arch) = LLVMExtensionExpr arch
type instance StmtExtension (LLVM arch) = LLVMStmt (ArchWidth arch)

instance (1 <= ArchWidth arch) => IsSyntaxExtension (LLVM arch)
