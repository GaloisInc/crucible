{-# Language DeriveFunctor, RankNTypes, ConstraintKinds, TypeFamilies, ScopedTypeVariables, GADTs #-}
module Crux.Types where

import           Data.Functor.Const
import           Data.Parameterized.Map (MapF)
import           Data.Sequence (Seq)
import           Data.Text ( Text )
import           Data.Void
import           Prettyprinter

import           What4.Expr (GroundValue,GroundValueWrapper)
import           What4.Interface (Pred)
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator
import           Lang.Crucible.Types

-- | A simulator context
type SimCtxt personality sym p = SimContext (personality sym) sym p

-- | The instance of the override monad we use,
-- when we don't care about the context of the surrounding function.
type OverM personality sym ext a =
  forall r args ret.
  OverrideSim
    (personality sym)  -- Extra data available in overrides (frontend-specific)
    sym                -- The symbolic backend (usually a what4 ExprBuilder in some form)
    ext                -- The Crucible syntax extension for the target language
    r
    args
    ret
    a

-- | This is the instance of the 'OverrideSim' monad that we use.
type Fun personality sym ext args ret =
  forall r.
  OverrideSim
    (personality sym)
    sym                                    -- the backend
    ext
    r
    args
    ret
    (RegValue sym ret)

data Result personality sym where
  Result :: (ExecResult (personality sym) sym ext (RegEntry sym UnitType)) -> Result personality sym


data ProcessedGoals =
  ProcessedGoals { totalProcessedGoals :: !Integer
                 , provedGoals :: !Integer
                 , disprovedGoals :: !Integer
                 , incompleteGoals :: !Integer
                 }

data ProofResult sym
   = Proved [Either (Assumption sym) (Assertion sym)]
   | NotProved (Doc Void) (Maybe (ModelView, [CrucibleEvent GroundValueWrapper])) [String]
     -- ^ The first argument is an explanation of the failure and
     -- counter example as provided by the Explainer (if any) and the
     -- second maybe a model for the counter-example.

type LPred sym   = LabeledPred (Pred sym)

data ProvedGoals
  = Branch ProvedGoals ProvedGoals
  | NotProvedGoal
         [CrucibleAssumption (Const ())]
         SimError
         (Doc Void)
         [ProgramLoc]
         (Maybe (ModelView, [CrucibleEvent GroundValueWrapper]))
         [String]
  | ProvedGoal
         [CrucibleAssumption (Const ())]
         SimError
         [ProgramLoc]
         Bool
    -- ^ Keeps only the explanations for the relevant assumptions.
    --
    --   * The array of (AssumptionReason,String) is the set of
    --     assumptions for this Goal.
    --
    --   * The (SimError,String) is information about the failure,
    --     with the specific SimError (Lang.Crucible.Simulator) and a
    --     string representation of the Crucible term that encountered
    --     the error.
    --
    --   * The 'Bool' (third argument) indicates if the goal is
    --     trivial (i.e., the assumptions are inconsistent)


data ProgramCompleteness
 = ProgramComplete
 | ProgramIncomplete
 deriving (Eq,Ord,Show)



data CruxSimulationResult =
  CruxSimulationResult
  { cruxSimResultCompleteness :: ProgramCompleteness
  , cruxSimResultGoals        :: Seq (ProcessedGoals, ProvedGoals)
  }


-- | A dummy datatype that can be used for the "personality"
--   type parameter.
data Crux sym = CruxPersonality


-- | A list of named GroundValues of the same type (used to
-- report SMT models in a portable way -- see the ModelView
-- datatype).
newtype Vals ty     = Vals [ Entry (GroundValue ty) ]

-- | A named value of type @a@ with a program
-- location. Used to describe and report models from SMT
-- queries (see Model and ModelView datatypes).
data Entry a        = Entry { entryName :: String
                            , entryLoc :: ProgramLoc
                            , entryValue :: a
                            }

-- | A portable/concrete view of a model's contents, organized by
-- crucible type. I.e., each crucible type is associated
-- with the list of entries (i.e. named GroundValues) at
-- that type for the given model, used to describe the
-- conditions under which an SMT query is satisfiable.
newtype ModelView = ModelView { modelVals :: MapF BaseTypeRepr Vals }

----------------------------------------------------------------------
-- Various things that can be logged/output

-- | Specify some general text that should be presented (to the user).
data SayWhat = SayWhat SayLevel Text Text  -- ^ fields are: Level From Message
             | SayMore SayWhat SayWhat
             | SayNothing

-- | Specify the verbosity/severity level of a message.  These are in
-- ordinal order for possible filtering, and higher levels may be sent
-- to a different location (e.g. stderr v.s. stdout).
data SayLevel = Noisily | Simply | OK | Warn | Fail deriving (Eq, Ord)
