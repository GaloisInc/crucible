module SAWScript.Proof where

import Control.Monad.State
import Verifier.SAW.SharedTerm

-- | A theorem must contain a boolean term, possibly surrounded by one
-- or more lambdas which are interpreted as universal quantifiers.
data Theorem s = Theorem (SharedTerm s)

-- | A ProofGoal is a term of type Bool, possibly surrounded by one or
-- more lambdas. The abstracted arguments are treated as if they are
-- EXISTENTIALLY quantified, as in the statement of a SAT problem. For
-- proofs of universals, we negate the proposition before running the
-- proof script, and then re-negate the result afterward.
data ProofGoal s =
  ProofGoal {
    goalName :: String
  , goalTerm :: SharedTerm s
  }

type ProofScript s a = StateT (ProofGoal s) IO a

