{-# Language RankNTypes, ConstraintKinds, TypeFamilies #-}
module Crux.Types where


import Lang.Crucible.Simulator.RegMap(RegValue)
import Lang.Crucible.Simulator.OverrideSim(OverrideSim)
import Lang.Crucible.Simulator.ExecutionTree(SimContext)

import Crux.Model

-- | A simulator context 
type SimCtxt sym p = SimContext (Model sym) sym p

-- | The instane of the override monad we use,
-- when we don't care about the context of the surrounding function.
type OverM sym p a =
  forall r args ret.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    p                                      -- the language
    r
    args
    ret
    a

-- | This is the instance of the 'OverrideSim' monad that we use.
type Fun sym p args ret =
  forall r.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    p
    r
    args
    ret
    (RegValue sym ret)
