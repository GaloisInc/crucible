{-|
Module      : Lang.Crucible.Backend.AssumptionStack
Copyright   : (c) Galois, Inc 2018
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

This module provides management support for keeping track of a context of
logical assumptions and proof obligations that arise from symbolic simulation.
The API provided here is similar to the interactive mode of an SMT solver.
Logical conditions can be assumed into the current context, and conjunctions
of assumptions are organized into frames which are pushed and popped by the
simulator to manage the state.

Additionally, proof goals can be asserted to the system. These will be turned
into complete logical statements by assuming the current context and will be
stashed in a collection of remembered goals for later dispatch to SMT solvers.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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
import qualified Data.Foldable as F
import           Data.IORef
import           Data.Parameterized.Nonce

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

-- | An assumption stack is a data structure for tracking logical assumptions
--   and proof obligations that arise from symbolic simulation.  Assumptions
--   can be added to the current stack frame, and stack frames may be pushed (to
--   remember a previous state) or popped (to restore a previous state).
--
--   The main use of 'AssumptionStack' is as the state of the simple or online
--   backends.
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
popFrame :: Monoid asmp => FrameIdentifier -> AssumptionStack asmp ast -> IO asmp
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
  Monoid asmp =>
  FrameIdentifier ->
  AssumptionStack asmp ast ->
  IO (asmp, Maybe (Goals asmp ast))
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
inFreshFrame :: Monoid asmp => AssumptionStack asmp ast -> IO a -> IO (asmp, a)
inFreshFrame stk action =
  bracketOnError
     (pushFrame stk)
     (\ident -> popFrame ident stk)
     (\ident -> do x <- action
                   frm <- popFrame ident stk
                   return (frm, x))
