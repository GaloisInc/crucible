{-|
Module      : Lang.Crucible.Backend.AssumptionStack
Copyright   : (c) Galois, Inc 2018
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

This module provides management support for keeping track
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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.Backend.AssumptionStack
  ( -- * Assertions and proof goals
    ProofGoal(..)
  , Goals(..)

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
  , collectAssumptions
  , appendAssumptions
  , allAssumptionFrames

  ) where

import           Control.Exception (bracketOnError)
import           Data.Functor ((<&>))
import qualified Data.Foldable as F
import           Data.IORef
import           Data.Parameterized.Nonce

import qualified Prettyprinter as PP

import           Lang.Crucible.Backend.ProofGoals
import           Lang.Crucible.Panic (panic)

-- | A single @AssumptionFrame@ represents a collection
--   of assumptions.  They will later be rescinded when
--   the associated frame is popped from the stack.
data AssumptionFrame asmp =
  AssumptionFrame
  { assumeFrameIdent :: FrameIdentifier
  , assumeFrameCond  :: asmp
  }

-- | An assumption stack is a data structure for tracking
--   logical assumptions and proof obligations.  Assumptions
--   can be added to the current stack frame, and stack frames
--   may be pushed (to remember a previous state) or popped
--   to restore a previous state.
data AssumptionStack asmp ast =
  AssumptionStack
  { assumeStackGen   :: IO FrameIdentifier
  , proofObligations :: IORef (GoalCollector asmp ast)
  }


allAssumptionFrames :: Monoid asmp => AssumptionStack asmp ast -> IO (AssumptionFrames asmp)
allAssumptionFrames stk =
  gcFrames <$> readIORef (proofObligations stk)

-- | Produce a fresh assumption stack.
initAssumptionStack :: NonceGenerator IO t -> IO (AssumptionStack asmp ast)
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
saveAssumptionStack :: Monoid asmp => AssumptionStack asmp ast -> IO (GoalCollector asmp ast)
saveAssumptionStack stk =
  gcRemoveObligations <$> readIORef (proofObligations stk)

-- | Restore a previously saved assumption stack.  Any proof
--   obligations in the saved stack will be copied into the
--   assumption stack, which will also retain any proof obligations
--   it had previously.  A saved stack created with `saveAssumptionStack`
--   will have no included proof obligations; restoring such a stack will
--   have no effect on the current proof obligations.
restoreAssumptionStack ::
  Monoid asmp => 
  GoalCollector asmp ast ->
  AssumptionStack asmp ast ->
  IO ()
restoreAssumptionStack gc stk =
  modifyIORef' (proofObligations stk) (gcRestore gc)

-- | Add the given collection logical assumptions to the current stack frame.
appendAssumptions ::
  Monoid asmp => asmp -> AssumptionStack asmp ast -> IO ()
appendAssumptions ps stk =
  modifyIORef' (proofObligations stk) (gcAddAssumes ps)

-- | Add a new proof obligation to the current collection of obligations based
--   on all the assumptions currently in scope and the predicate in the
--   given assertion.
addProofObligation :: ast -> AssumptionStack asmp ast -> IO ()
addProofObligation p stk = modifyIORef' (proofObligations stk) (gcProve p)


-- | Collect all the assumptions currently in scope in this stack frame
--   and all previously-pushed stack frames.
collectAssumptions :: Monoid asmp => AssumptionStack asmp ast -> IO asmp
collectAssumptions stk =
  do AssumptionFrames base frms <- gcFrames <$> readIORef (proofObligations stk)
     return (base <> F.fold (fmap snd frms))

-- | Retrieve the current collection of proof obligations.
getProofObligations :: Monoid asmp => AssumptionStack asmp ast -> IO (Maybe (Goals asmp ast))
getProofObligations stk = gcFinish <$> readIORef (proofObligations stk)

-- | Remove all pending proof obligations.
clearProofObligations :: Monoid asmp => AssumptionStack asmp ast -> IO ()
clearProofObligations stk =
  modifyIORef' (proofObligations stk) gcRemoveObligations

-- | Reset the 'AssumptionStack' to an empty set of assumptions,
--   but retain any pending proof obligations.
resetStack :: Monoid asmp => AssumptionStack asmp ast -> IO ()
resetStack stk = modifyIORef' (proofObligations stk) gcReset

-- | Push a new assumption frame on top of the stack.  The
--   returned @FrameIdentifier@ can be used later to pop this
--   frame.  Frames must be pushed and popped in a coherent,
--   well-bracketed way.
pushFrame :: AssumptionStack asmp ast -> IO FrameIdentifier
pushFrame stk =
  do ident <- assumeStackGen stk
     modifyIORef' (proofObligations stk) (gcPush ident)
     return ident

-- | Pop all frames up to and including the frame with the
--   given identifier.  The return value indicates how
--   many stack frames were popped.
popFramesUntil :: Monoid asmp => FrameIdentifier -> AssumptionStack asmp ast -> IO Int
popFramesUntil ident stk = atomicModifyIORef' (proofObligations stk) (go 1)
 where
 go n gc =
    case gcPop gc of
      Left frm
        | ident == poppedFrameId frm -> (gc',n)
        | otherwise -> go (n+1) gc'
       where gc' = collectPoppedGoals frm
      Right _ ->
        panic "AssumptionStack.popFrameUntil"
          [ "Frame not found in stack."
          , "*** Frame to pop: " ++ showFrameId ident
          ]

 showFrameId (FrameIdentifier x) = show x

-- | Call 'gcPop' on the 'proofObligations' of this 'AssumptionStack'
popFrameUnchecked ::
  Monoid asmp =>
  AssumptionStack asmp ast ->
  IO (Either (PoppedFrame asmp ast) (Maybe (Goals asmp ast)))
popFrameUnchecked stk =
  atomicModifyIORef' (proofObligations stk) $ \gc ->
    case gcPop gc of
      Left frm -> (collectPoppedGoals frm, Left frm)
      Right mgs -> (gc, Right mgs)

data PopFrameError
  = NoFrames
    -- | Expected, actual
  | WrongFrame FrameIdentifier FrameIdentifier

instance PP.Pretty PopFrameError where
  pretty =
    \case
      NoFrames -> PP.pretty "Pop with no push in goal collector."
      WrongFrame expected actual ->
        PP.hsep
          [ PP.pretty "Mismatch in assumption stack frames."
          , PP.pretty "Expected ident:"
          , PP.viaShow expected
          , PP.pretty "Current frame:"
          , PP.viaShow actual
          ]

instance Show PopFrameError where
  show = show . PP.pretty

-- | Pop a previously-pushed assumption frame from the stack.
--   All assumptions in that frame will be forgotten.  The
--   assumptions contained in the popped frame are returned.
--
--   Returns 'Left' if there are no frames on the stack, or if the top frame
--   doesn\'t have the provided 'FrameIdentifier'.
popFrameChecked ::
  Monoid asmp =>
  FrameIdentifier ->
  AssumptionStack asmp ast ->
  IO (Either PopFrameError (PoppedFrame asmp ast))
popFrameChecked ident stk =
  popFrameUnchecked stk <&>
    \case
      Left frm
        | ident == poppedFrameId frm -> Right frm
        | otherwise -> Left (WrongFrame ident (poppedFrameId frm))
      Right _ -> Left NoFrames

-- | Pop a previously-pushed assumption frame from the stack.
--   All assumptions in that frame will be forgotten.  The
--   assumptions contained in the popped frame are returned.
--
--   Panics if there are no frames on the stack, or if the top frame doesn\'t
--   have the provided 'FrameIdentifier'.
popFrame :: Monoid asmp => FrameIdentifier -> AssumptionStack asmp ast -> IO asmp
popFrame ident stk =
  popFrameChecked ident stk <&>
    \case
      Left err -> panic "AssumptionStack.popFrame" [show err]
      Right frm -> poppedAssumptions frm

-- | Pop the assumptions and goals from the top frame.
--
--   Panics if there are no frames on the stack, or if the top frame doesn\'t
--   have the provided 'FrameIdentifier'.
popFrameAndGoals ::
  Monoid asmp =>
  FrameIdentifier ->
  AssumptionStack asmp ast ->
  IO (asmp, Maybe (Goals asmp ast))
popFrameAndGoals ident stk =
  popFrameChecked ident stk <&>
    \case
      Left err -> panic "AssumptionStack.popFrameAndGoals" [show err]
      Right frm -> (poppedAssumptions frm, poppedGoals frm)

-- | Run an action in the scope of a fresh assumption frame.
--   The frame will be popped and returned on successful
--   completion of the action.  If the action raises an exception,
--   the frame will be popped and discarded.
inFreshFrame :: Monoid asmp => AssumptionStack asmp ast -> IO a -> IO (asmp, a)
inFreshFrame stk action =
  bracketOnError
     (pushFrame stk)
     (\ident -> popFrame ident stk)
     (\ident -> do x <- action
                   frm <- popFrame ident stk
                   return (frm, x))
