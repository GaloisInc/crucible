{-# Language RankNTypes, ConstraintKinds, TypeFamilies #-}
module Types where

import Lang.Crucible.LLVM.Extension(ArchWidth)
import Lang.Crucible.LLVM.MemModel(LLVMPointerType, HasPtrWidth)

-- | This happens quite a lot, so just a shorter name
type ArchOk arch    = HasPtrWidth (ArchWidth arch)
type TPtr arch      = LLVMPointerType (ArchWidth arch)
type TBits n        = LLVMPointerType n

-- | Index for the crux-c "Language"
data LangLLVM = LangLLVM

