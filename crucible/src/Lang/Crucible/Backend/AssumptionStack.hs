{-|
Module      : Lang.Crucible.Backend.AssumptionStack
Copyright   : (c) Galois, Inc 2018
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

This module provides managament support for keeping track
of a context of logical assumptions.  The API provided here
is similar to the interactive mode of an SMT solver.  Logical
conditions can be assumed into the current context, and bundles
of assumptions are organized into frames which are pushed and
popped by the user to manage the state.

Additionally, proof goals can be asserted to the system.  These will be
turned into complete logical statements by assuming the current context
and be stashed in a collection of remembered goals for later dispatch to
solvers.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.Backend.AssumptionStack
  ( -- * Assertions and proof goals
    LabeledPred(..)
  , labeledPred
  , labeledPredMsg
  , ProofGoal(..)
  , AssumeAssert(..)

    -- * Frames and assumption stacks
    -- ** Basic data types
  , FrameIdentifier
  , AssumptionFrame(..)
  , AssumptionFrames(..)
  , AssumptionStack(..)
    -- ** Manipulating assumption stacks
  , initAssumptionStack
  , saveAssumptionStack
  , restoreAssumptionStack
  , pushFrame
  , popFrame
  , popFrameAndGoals
  , popFramesUntil
  , resetStack
  , getProofObligations
  , clearProofObligations
  , addProofObligation
  , inFreshFrame
    -- ** Assumption management
  , assume
  , assert
  , collectAssumptions
  , appendAssumptions
  , allAssumptionFrames

    -- * Collection of proof obligations
  , Goals(..), proofGoalsToList
  , ProofGoals
  , LabeledGoalCollector
  ) where

import           Control.Exception (bracketOnError)
import           Control.Lens
import qualified Data.Foldable as F
import           Data.IORef
import           Data.Parameterized.Nonce
import           Data.Sequence (Seq)

import           Lang.Crucible.Backend.ProofGoals
import           Lang.Crucible.Panic (panic)

#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup
#endif

-- | Information about an assertion that was previously made.
data LabeledPred pred msg
   = LabeledPred
     { -- | Predicate that was asserted.
       _labeledPred    :: !pred
       -- | Message added when assumption/assertion was made.
     , _labeledPredMsg :: !msg
     }

-- | Predicate that was asserted.
labeledPred :: Lens (LabeledPred pred msg) (LabeledPred pred' msg) pred pred'
labeledPred = lens _labeledPred (\s v -> s { _labeledPred = v })

-- | Message added when assumption/assertion was made.
labeledPredMsg :: Lens (LabeledPred pred msg) (LabeledPred pred msg') msg msg'
labeledPredMsg = lens _labeledPredMsg (\s v -> s { _labeledPredMsg = v })

-- | A single @AssumptionFrame@ represents a collection
--   of assumtptions.  They will later be recinded when
--   the associated frame is popped from the stack.
data AssumptionFrame pred assumeMsg =
  AssumptionFrame
  { assumeFrameIdent :: FrameIdentifier
  , assumeFrameCond  :: Seq (LabeledPred pred assumeMsg)
  }


type LabeledGoalCollector pred assumeMsg assertMsg =
  GoalCollector (LabeledPred pred assumeMsg) (LabeledPred pred assertMsg)

type ProofGoals pred assumeMsg assertMsg =
  Goals (LabeledPred pred assumeMsg) (LabeledPred pred assertMsg)

proofGoalsToList ::
  Maybe (ProofGoals pred assumeMsg assertMsg) ->
  [ ProofGoal (LabeledPred pred assumeMsg) (LabeledPred pred assertMsg) ]
proofGoalsToList = maybe [] goalsToList


-- | An assumption stack is a data structure for tracking
--   logical assumptions and proof obligations.  Assumptions
--   can be added to the current stack frame, and stack frames
--   may be pushed (to remember a previous state) or popped
--   to restore a previous state.
data AssumptionStack pred assumeMsg assertMsg =
  AssumptionStack
  { assumeStackGen   :: IO FrameIdentifier
  , proofObligations :: IORef (LabeledGoalCollector pred assumeMsg assertMsg)
  }


allAssumptionFrames ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO (AssumptionFrames (LabeledPred pred assumeMsg))
allAssumptionFrames stk =
  gcFrames <$> readIORef (proofObligations stk)

-- | Produce a fresh assumption stack.
initAssumptionStack ::
  NonceGenerator IO t ->
  IO (AssumptionStack pred assumeMsg assertMsg)
initAssumptionStack gen =
  do let genM = FrameIdentifier . indexValue <$> freshNonce gen
     oblsRef <- newIORef emptyGoalCollector
     return AssumptionStack
            { assumeStackGen = genM
            , proofObligations = oblsRef
            }

-- | Record the current state of the assumption stack in a
--   data structure that can later be used to restore the current
--   assumptions.
--
--   NOTE! however, that proof obligations are NOT copied into the saved
--   stack data. Instead, proof obligations remain only in the original
--   @AssumptionStack@ and the new stack has an empty obligation list.
saveAssumptionStack ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO (LabeledGoalCollector pred assumeMsg assertMsg)
saveAssumptionStack stk =
  gcRemoveObligations <$> readIORef (proofObligations stk)

-- | Restore a prevsiously saved assumption stack.  Any proof
--   obligations in the saved stack will be copied into the
--   assumption stack, which will also retain any proof obligations
--   it had previously.  A saved stack created with `saveAssumptionStack`
--   will have no included proof obligations; restoring such a stack will
--   have no effect on the current proof obligations.
restoreAssumptionStack ::
  LabeledGoalCollector pred assumeMsg assertMsg ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO ()
restoreAssumptionStack gc stk =
  modifyIORef' (proofObligations stk) (gcRestore gc)

-- | Add the given logical assumption to the current stack frame.
assume ::
  LabeledPred pred assumeMsg ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO ()
assume p stk =
  modifyIORef' (proofObligations stk) (gcAssume p)

-- | Add the given collection logical assumptions to the current stack frame.
appendAssumptions ::
  Seq (LabeledPred pred assumeMsg) ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO ()
appendAssumptions ps stk =
  modifyIORef' (proofObligations stk) (gcAddAssumes ps)

-- | This class witnesses the ability to inject assertion messages
--   into assumption messages.  This happens when an assertion is made;
--   in addition to producing a proof obligation, the assertion is assumed
--   so that later obligations can rely on it having been proved.
class AssumeAssert assumeMsg assertMsg where
  assertToAssume :: assertMsg -> assumeMsg


-- | Add a new proof obligation to the current collection of obligations based
--   on all the assumptions currently in scope and the predicate in the
--   given assertion.
addProofObligation ::
  LabeledPred pred assertMsg ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO ()
addProofObligation p stk = modifyIORef' (proofObligations stk) (gcProve p)


-- | Add a new proof obligation to the current collection of obligations based
--   on all the assumptions currently in scope and the predicate in the given assertion.
--
--   Then, assume the given assertion predicate in the current assumption frame.
assert ::
  AssumeAssert assumeMsg assertMsg =>
  LabeledPred pred assertMsg ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO ()
assert p stk =
  do modifyIORef' (proofObligations stk) (gcProve p)
     assume (p & over labeledPredMsg assertToAssume) stk

-- | Collect all the assumptions currently in scope in this stack frame
--   and all previously-pushed stack frames.
collectAssumptions ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO (Seq (LabeledPred pred assumeMsg))
collectAssumptions stk =
  do AssumptionFrames base frms <- gcFrames <$> readIORef (proofObligations stk)
     return (base <> F.asum (fmap snd frms))

-- | Retrieve the current collection of proof obligations.
getProofObligations ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO (Maybe (ProofGoals pred assumeMsg assertMsg))
getProofObligations stk = gcFinish <$> readIORef (proofObligations stk)

-- | Remove all pending proof obligations.
clearProofObligations ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO ()
clearProofObligations stk =
  modifyIORef' (proofObligations stk) gcRemoveObligations

-- | Reset the 'AssumptionStack' to an empty set of assumptions,
--   but retain any pending proof obligations.
resetStack :: AssumptionStack pred assumeMsg assertMsg -> IO ()
resetStack stk = modifyIORef' (proofObligations stk) gcReset

-- | Push a new assumption frame on top of the stack.  The
--   returned @FrameIdentifier@ can be used later to pop this
--   frame.  Frames must be pushed and popped in a coherent,
--   well-bracketed way.
pushFrame ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO FrameIdentifier
pushFrame stk =
  do ident <- assumeStackGen stk
     modifyIORef' (proofObligations stk) (gcPush ident)
     return ident

-- | Pop all frames up to and including the frame with the
--   given identifier.  The return value indiciates how
--   many stack frames were popped.
popFramesUntil ::
  FrameIdentifier ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO Int
popFramesUntil ident stk = atomicModifyIORef' (proofObligations stk) (go 1)
 where
 go n gc =
    case gcPop gc of
      Left (ident', _assumes, mg, gc1)
        | ident == ident' -> (gc',n)
        | otherwise -> go (n+1) gc'
       where gc' = case mg of
                     Nothing -> gc1
                     Just g  -> gcAddGoals g gc1
      Right _ ->
        panic "AssumptionStack.popFrameUntil"
          [ "Frame not found in stack."
          , "*** Frame to pop: " ++ showFrameId ident
          ]

 showFrameId (FrameIdentifier x) = show x

-- | Pop a previously-pushed assumption frame from the stack.
--   All assumptions in that frame will be forgotten.  The
--   assumptions contained in the popped frame are returned.
popFrame ::
  FrameIdentifier ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO (Seq (LabeledPred pred assumeMsg))
popFrame ident stk =
  atomicModifyIORef' (proofObligations stk) $ \gc ->
       case gcPop gc of
         Left (ident', assumes, mg, gc1)
           | ident == ident' ->
                let gc' = case mg of
                            Nothing -> gc1
                            Just g  -> gcAddGoals g gc1
                 in (gc', assumes)
           | otherwise ->
               panic "AssumptionStack.popFrame"
                [ "Push/pop mismatch in assumption stack!"
                , "*** Current frame:  " ++ showFrameId ident
                , "*** Expected ident: " ++ showFrameId ident'
                ]
         Right _  ->
           panic "AssumptionStack.popFrame"
             [ "Pop with no push in goal collector."
             , "*** Current frame: " ++ showFrameId ident
             ]

  where
  showFrameId (FrameIdentifier x) = show x


popFrameAndGoals ::
  FrameIdentifier ->
  AssumptionStack pred assumeMsg assertMsg ->
  IO (Seq (LabeledPred pred assumeMsg), Maybe (ProofGoals pred assumeMsg assertMsg))
popFrameAndGoals ident stk =
  atomicModifyIORef' (proofObligations stk) $ \gc ->
       case gcPop gc of
         Left (ident', assumes, mg, gc1)
           | ident == ident' -> (gc1, (assumes, mg))
           | otherwise ->
               panic "AssumptionStack.popFrameAndGoals"
                [ "Push/pop mismatch in assumption stack!"
                , "*** Current frame:  " ++ showFrameId ident
                , "*** Expected ident: " ++ showFrameId ident'
                ]
         Right _  ->
           panic "AssumptionStack.popFrameAndGoals"
             [ "Pop with no push in goal collector."
             , "*** Current frame: " ++ showFrameId ident
             ]

  where
  showFrameId (FrameIdentifier x) = show x


-- | Run an action in the scope of a fresh assumption frame.
--   The frame will be popped and returned on successful
--   completion of the action.  If the action raises an exception,
--   the frame will be popped and discarded.
inFreshFrame ::
  AssumptionStack pred assumeMsg assertMsg ->
  IO a ->
  IO (Seq (LabeledPred pred assumeMsg), a)
inFreshFrame stk action =
  bracketOnError
     (pushFrame stk)
     (\ident -> popFrame ident stk)
     (\ident -> do x <- action
                   frm <- popFrame ident stk
                   return (frm, x))
