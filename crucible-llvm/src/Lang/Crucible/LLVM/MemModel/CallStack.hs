------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.CallStack
-- Description      : Call stacks from the LLVM memory model
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

module Lang.Crucible.LLVM.MemModel.CallStack
  ( CallStack
  , getCallStack
  , ppCallStack
  ) where

import Lang.Crucible.LLVM.MemModel.CallStack.Internal
