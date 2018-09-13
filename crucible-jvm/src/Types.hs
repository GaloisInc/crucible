{-# Language RankNTypes, ConstraintKinds, TypeFamilies #-}
module Types where


import Lang.Crucible.Simulator.RegMap(RegValue)
import Lang.Crucible.Simulator.OverrideSim(OverrideSim)
import Lang.Crucible.Simulator.ExecutionTree(SimContext)

import Lang.Crucible.JVM.Types

import Model

-- | A simulator context
type SimCtxt sym = SimContext (Model sym) sym JVM

-- | The instane of the override monad we use,
-- when we don't care about the context of the surrounding function.
type OverM sym a =
  forall r args ret.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    JVM                                    -- JVM extensions
    r
    args
    ret
    a

-- | This is the instance of the 'OverrideSim' monad that we use.
type Fun sym args ret =
  forall r.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    JVM
    r
    args
    ret
    (RegValue sym ret)
