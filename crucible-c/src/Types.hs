{-# Language RankNTypes, ConstraintKinds, TypeFamilies #-}
module Types where


import Lang.Crucible.Simulator.RegMap(RegValue)
import Lang.Crucible.Simulator.OverrideSim(OverrideSim)
import Lang.Crucible.Simulator.ExecutionTree(SimContext)
import Lang.Crucible.LLVM.Extension(LLVM,ArchWidth)
import Lang.Crucible.LLVM.MemModel(LLVMPointerType, HasPtrWidth)

{-
import Model

-- | A simulator context for an arch
type SimCtxt sym arch = SimContext (Model sym) sym (LLVM arch)
-}
-- | This happens quite a lot, so just a shorter name
type ArchOk arch    = HasPtrWidth (ArchWidth arch)
type TPtr arch      = LLVMPointerType (ArchWidth arch)
type TBits n        = LLVMPointerType n

{-
-- | The instane of the override monad we use,
-- when we don't care about the context of the surrounding function.
type OverM sym arch a =
  forall r args ret.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    (LLVM arch)                            -- LLVM extensions
    r
    args
    ret
    a

-- | This is the instance of the 'OverrideSim' monad that we use.
type Fun sym arch args ret =
  forall r.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    (LLVM arch)                            -- LLVM extensions
    r
    args
    ret
    (RegValue sym ret)

-}

