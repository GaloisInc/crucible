{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Solver.SimpleBackend
  ( -- * SimpleBackend
    SimpleBackend
  , newSimpleBackend
    -- * SimpleBackendState
  , SimpleBackendState
  , assertions
  , appendAssertion
  , appendAssertions
  ) where

import           Control.Exception ( assert, throw )
import           Control.Lens
import           Data.IORef
import           Data.Parameterized.Nonce
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.SimpleBuilder (BoolElt)
import qualified Lang.Crucible.Solver.SimpleBuilder as SB

type SimpleBackend t = SB.SimpleBuilder t SimpleBackendState

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data SimpleBackendState t
      = SimpleBackendState { _assertions  :: Seq (Assertion (BoolElt t))
                           , _proofObligs :: Seq (Seq (BoolElt t), Assertion (BoolElt t))
                           }

-- | Returns an initial execution staee.
initialSimpleBackendState :: SimpleBackendState t
initialSimpleBackendState
     = SimpleBackendState { _assertions = Seq.empty
                          , _proofObligs = Seq.empty
                          }

-- | The set of active assumptions in the program.
assertions :: Simple Lens (SimpleBackendState t) (Seq (Assertion (BoolElt t)))
assertions = lens _assertions (\s v -> s { _assertions = v })

-- | The sequence of accumulated assertion obligations
proofObligs :: Simple Lens (SimpleBackendState t) (Seq (Seq (BoolElt t), Assertion (BoolElt t)))
proofObligs = lens _proofObligs (\s v -> s { _proofObligs = v })

appendAssertion :: ProgramLoc
                -> BoolElt t
                -> SimErrorReason
                -> SimpleBackendState t
                -> SimpleBackendState t
appendAssertion l p m s =
  let ast = Assertion l p (Just m) in
  s & assertions  %~ (Seq.|> ast)
    & proofObligs %~ (Seq.|> (fmap (^.assertPred) (s^.assertions), ast))

appendAssumption :: ProgramLoc
                 -> BoolElt t
                 -> SimpleBackendState t
                 -> SimpleBackendState t
appendAssumption l p s =
  s & assertions %~ (Seq.|> Assertion l p Nothing)

-- | Append assertions to path state.
appendAssertions :: Seq (Assertion (BoolElt t))
                 -> SimpleBackendState t
                 -> SimpleBackendState t
appendAssertions pairs = assertions %~ (Seq.>< pairs)

newSimpleBackend :: NonceGenerator IO t
                 -> IO (SimpleBackend t)
newSimpleBackend = SB.newSimpleBuilder initialSimpleBackendState

instance SB.IsSimpleBuilderState SimpleBackendState where
  sbAddAssertion sym e m = do
    case SB.asApp e of
      Just SB.TrueBool -> return ()
      Just SB.FalseBool -> do
        loc <- getCurrentProgramLoc sym
        throw (SimError loc m)
      _ -> do
        loc <- getCurrentProgramLoc sym
        modifyIORef' (SB.sbStateManager sym) $ appendAssertion loc e m

  sbAddAssumption sym e = do
    case SB.asApp e of
      Just SB.TrueBool -> return ()
      _ -> do
        loc <- getCurrentProgramLoc sym
        modifyIORef' (SB.sbStateManager sym) $ appendAssumption loc e

  sbAppendAssertions sym s = do
    modifyIORef' (SB.sbStateManager sym) $ appendAssertions s

  sbAssertionsBetween old cur =
    assert (old_cnt <= Seq.length a) $ Seq.drop old_cnt a
    where a = cur^.assertions
          old_cnt = Seq.length $ old^.assertions

  sbAllAssertions sym = do
    s <- readIORef (SB.sbStateManager sym)
    andAllOf sym folded (view assertPred <$> s^.assertions)

  sbEvalBranch _ p = do
    case asConstantPred p of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing    -> return $! SymbolicBranch True

  sbGetProofObligations sym = do
    mg <- readIORef (SB.sbStateManager sym)
    return $ mg^.proofObligs

  sbSetProofObligations sym obligs = do
    modifyIORef' (SB.sbStateManager sym) (set proofObligs obligs)

  sbPushBranchPred _ _ = return ()
  sbBacktrackToState _ _ = return ()
  sbSwitchToState  _ _ _ = return ()
