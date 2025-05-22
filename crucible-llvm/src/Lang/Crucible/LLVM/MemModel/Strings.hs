-- TODO(TODO: file an issue, put number here): Move the definitions of the
-- deprecated imports into this module, and remove the exports from MemModel.
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}

-- | Manipulating C-style null-terminated strings
module Lang.Crucible.LLVM.MemModel.Strings
  ( Mem.loadString
  , Mem.loadMaybeString
  , Mem.strLen
  ) where

import qualified Lang.Crucible.LLVM.MemModel as Mem

