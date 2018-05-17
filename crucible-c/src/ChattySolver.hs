{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}
-- | A version of the Online solver that keeps track
-- of things it proved.
module ChattySolver where

import Data.IORef

import What4.Interface
import What4.Protocol.Online
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online

data ChattyBackend scope solver = ChattyBackend
  { theSym :: OnlineBackend scope solver
  , proofs :: {-#UNPACK#-} !(IORef [String]) -- XXX
  }


type instance SymExpr (ChattyBackend scope solver) =
              SymExpr (OnlineBackend scope solver)

instance OnlineSolver scope solver =>
         IsBoolSolver (ChattyBackend scope solver) where
  addAssertion             = addAssertion           . theSym
  addAssumption            = addAssumption          . theSym
  addAssumptions           = addAssumptions         . theSym
  getPathCondition         = getPathCondition       . theSym
  pushAssumptionFrame      = pushAssumptionFrame    . theSym
  popAssumptionFrame       = popAssumptionFrame     . theSym
  getProofObligations      = getProofObligations    . theSym
  setProofObligations      = setProofObligations    . theSym
  addFailedAssertion       = addFailedAssertion     . theSym
  cloneAssumptionState     = cloneAssumptionState   . theSym
  restoreAssumptionState   = restoreAssumptionState . theSym

  evalBranch sym p =
    do res <- evalBranch (theSym sym) p
       case res of
         InfeasibleBranch  -> return ()
         NoBranch x        -> return ()
         SymbolicBranch _  -> return ()
       return res
