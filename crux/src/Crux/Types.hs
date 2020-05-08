{-# Language DeriveFunctor, RankNTypes, ConstraintKinds, TypeFamilies, ScopedTypeVariables, GADTs #-}
module Crux.Types where

import Data.Sequence (Seq)
import Data.Parameterized.Map (MapF)

import What4.Expr (GroundValue)
import What4.Interface (Pred)

import Lang.Crucible.Backend
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Simulator
import Lang.Crucible.Types


-- | A simulator context 
type SimCtxt sym p = SimContext (Model sym) sym p

-- | The instance of the override monad we use,
-- when we don't care about the context of the surrounding function.
type OverM sym ext a =
  forall r args ret.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    ext                                      -- the extension
    r
    args
    ret
    a

-- | This is the instance of the 'OverrideSim' monad that we use.
type Fun sym ext args ret =
  forall r.
  OverrideSim
    (Model sym)
    sym                                    -- the backend
    ext
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
   | NotProved (Maybe ModelView)   -- ^ Counter example, if any
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


data ProgramCompleteness
 = ProgramComplete
 | ProgramIncomplete
 deriving (Eq,Ord,Show)



data CruxSimulationResult =
  CruxSimulationResult
  { cruxSimResultCompleteness :: ProgramCompleteness
  , cruxSimResultGoals        :: Seq (ProvedGoals (Either AssumptionReason SimError))
  }


-- From Model

-- | SMT model organized by crucible type. I.e., each
-- crucible type is associated with the list of entries
-- (i.e. named, possibly still symbolic, RegValues) at that
-- type for the given model, used to describe the conditions
-- under which an SMT query is satisfiable. N.B., because
-- the values may still be symbolic, they must be evaluated
-- before they are grounded (e.g., see the `evalModel` and
-- `groundEval` functions from Crux.Model and
-- What4.Expr.GroundEval, which are used to construct the
-- ModelView datatype described below).
newtype Model sym   = Model (MapF BaseTypeRepr (Vars sym))

-- | A list of named (possibly still symbolic) RegValues of
-- the same type (used to describe SMT models -- see the
-- Model datatype).
newtype Vars sym ty = Vars [ Entry (RegValue sym (BaseToType ty)) ]

-- | A list of named GroundValues of the same type (used to
-- report SMT models in a portable way -- see the ModelView
-- datatype).
newtype Vals ty     = Vals [ Entry (GroundValue ty) ]

-- | A named value of type `ty` with a program
-- location. Used to describe and report models from SMT
-- queries (see Model and ModelView datatypes).
data Entry ty       = Entry { entryName :: String
                            , entryLoc :: ProgramLoc
                            , entryValue :: ty
                            }

-- | A portable/concrete view of a model's contents, organized by
-- crucible type. I.e., each crucible type is associated
-- with the list of entries (i.e. named GroundValues) at
-- that type for the given model, used to describe the
-- conditions under which an SMT query is satisfiable.
newtype ModelView = ModelView { modelVals :: MapF BaseTypeRepr Vals }




