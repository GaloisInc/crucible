module SAWScript.VerificationCheck where

import Verifier.SAW.Evaluator
import Verifier.SAW.SharedTerm
import Text.PrettyPrint.Leijen

import SAWScript.Utils

data VerificationCheck s
  = AssertionCheck String         -- ^ Name of assertion.
                   (SharedTerm s) -- ^ Assertion term.
  -- | Check that equality assertion is true.
  | EqualityCheck String          -- ^ Name of value to compare
                  (SharedTerm s)  -- ^ Value returned by implementation.
                  (SharedTerm s)  -- ^ Expected value in Spec.

vcName :: VerificationCheck s -> String
vcName (AssertionCheck nm _) = nm
vcName (EqualityCheck nm _ _) = nm

-- | Returns goal that one needs to prove.
vcGoal :: SharedContext s -> VerificationCheck s -> IO (SharedTerm s)
vcGoal _ (AssertionCheck _ n) = return n
vcGoal sc (EqualityCheck _ x y) = scEq sc x y

type CounterexampleFn s = (SharedTerm s -> IO Value) -> IO Doc

-- | Returns documentation for check that fails.
vcCounterexample :: VerificationCheck s -> CounterexampleFn s
vcCounterexample (AssertionCheck nm n) _ =
  return $ text ("Assertion " ++ nm ++ " is unsatisfied:") <+>
           scPrettyTermDoc n
vcCounterexample (EqualityCheck nm impNode specNode) evalFn =
  do ln <- evalFn impNode
     sn <- evalFn specNode
     return (text nm <$$>
        nest 2 (text $ "Encountered: " ++ show ln) <$$>
        nest 2 (text $ "Expected:    " ++ show sn))

ppCheck :: VerificationCheck s -> Doc
ppCheck (AssertionCheck nm tm) =
  hsep [ text (nm ++ ":")
       , scPrettyTermDoc tm
       ]
ppCheck (EqualityCheck nm tm tm') =
  hsep [ text (nm ++ ":")
       , scPrettyTermDoc tm
       , text ":="
       , scPrettyTermDoc tm'
       ]
