{-# Language RankNTypes, ConstraintKinds, TypeFamilies #-}
module Types where


import Lang.Crucible.Solver.SimpleBackend(SimpleBackend)
import Lang.Crucible.Solver.BoolInterface(Pred)
import Lang.Crucible.Types(UnitType, EmptyCtx)
import Lang.Crucible.Simulator.RegMap(RegValue)
import Lang.Crucible.Simulator.OverrideSim(OverrideSim)
import Lang.Crucible.Simulator.ExecutionTree(SimContext)
import Lang.Crucible.LLVM.Extension(LLVM,ArchWidth)
import Lang.Crucible.LLVM.MemModel(LLVMPointerType)
import Lang.Crucible.LLVM.Types(HasPtrWidth)

import Model

-- | A simulator context for an arch
type SimCtxt scope arch = SimContext Model scope (LLVM arch)

-- | This happens quite a lot, so just a shorter name
type ArchOk arch    = HasPtrWidth (ArchWidth arch)
type TPtr arch      = LLVMPointerType (ArchWidth arch)
type TBits n        = LLVMPointerType n
type Formula b      = Pred b


-- | This is the instance of the 'OverrideSim' monad that we use.
type Fun scope arch args ret =
  forall r.
  OverrideSim
    Model
    (SimpleBackend scope)                  -- the backend
    (LLVM arch)                            -- LLVM extensions
    r
    args
    ret
    (RegValue (SimpleBackend scope) ret)

-- | Special case of 'Fun' with no arguments or return type
type Code scope arch = Fun scope arch EmptyCtx UnitType


