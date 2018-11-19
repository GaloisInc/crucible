{-# Language DeriveFunctor, RankNTypes, ConstraintKinds, TypeFamilies, ScopedTypeVariables, GADTs #-}
module Crux.Types where

import Data.Parameterized.Map (MapF)

import Lang.Crucible.Simulator.RegMap(RegValue)
import Lang.Crucible.Simulator.OverrideSim(OverrideSim)
import Lang.Crucible.Simulator.ExecutionTree(SimContext)
import Lang.Crucible.Types(BaseTypeRepr(..),BaseToType)
import What4.Expr
        (GroundValue)
import What4.ProgramLoc
import What4.Interface (Pred)

import Lang.Crucible.Backend
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Simulator
import Lang.Crucible.Types


-- | A simulator context 
type SimCtxt sym p = SimContext (Model sym) sym p

-- | The instance of the override monad we use,
-- when we don't care about the context of the surrounding function.
type OverM sym p a =
  forall r args ret.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    p                                      -- the extension
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

-- NEW: the result of the simulation function, which hides the 'ext'
data Result sym where
  Result :: (ExecResult (Model sym) sym ext (RegEntry sym UnitType)) -> Result sym

--- From Goal



data ProofResult a
   = Proved [a]
   | NotProved (Maybe ModelViews)   -- ^ Counter example, if any
 deriving (Functor)

type LPred sym   = LabeledPred (Pred sym)

data ProvedGoals a =
    AtLoc ProgramLoc (Maybe ProgramLoc) (ProvedGoals a)
  | Branch (ProvedGoals a) (ProvedGoals a)
  | Goal [(AssumptionReason,String)]
         (SimError,String) Bool (ProofResult a)
    -- ^ Keeps only the explanations for the relevant assumptions.
    -- The 'Maybe Int' in the assumptions corresponds to its depth in the tree
    -- (i.e., the step number, if this is a path assumption)
    -- The 'Bool' indicates if the goal is trivial (i.e., the assumptions
    -- are inconsistent)

-- From Model

newtype Model sym   = Model (MapF BaseTypeRepr (Vars sym))
data Entry ty       = Entry { entryName :: String
                            , entryLoc :: ProgramLoc
                            , entryValue :: ty
                            }
newtype Vars sym ty = Vars [ Entry (RegValue sym (BaseToType ty)) ]
newtype Vals ty     = Vals [ Entry (GroundValue ty) ]

-- Should we break this into separate languages?

data ModelViews = ModelViews
  { modelInC :: String
  , modelInJS :: String
  }




