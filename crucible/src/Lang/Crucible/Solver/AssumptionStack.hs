{-|
Module      : Lang.Crucible.Solver.AssumptionStack
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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.Solver.AssumptionStack
  ( -- * Assertions and proof goals
    Assertion(..)
  , assertPred
  , ProofGoal(..)

    -- * Frames and assumption stacks
    -- ** Basic data types
  , FrameIdentifier
  , AssumptionFrame(..)
  , AssumptionStack(..)
    -- ** Manipulating assumption stacks
  , initAssumptionStack
  , cloneAssumptionStack
  , pushFrame
  , popFrame
  , getProofObligations
  , setProofObligations
  , stackHeight
  , allAssumptionFrames
  , inFreshFrame
    -- ** Assumption management
  , assume
  , assert
  , collectAssumptions
  , appendAssumptions
  ) where

import           Control.Exception (bracketOnError)
import           Control.Lens
import           Control.Monad
import           Data.IORef
import           Data.Parameterized.Nonce
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Word

import           Lang.Crucible.ProgramLoc

-- | Information about an assertion that was previously made.
data Assertion pred msg
   = Assertion { -- | Location of assertion
                 assertLoc :: !ProgramLoc
                 -- | Predicate that was asserted.
               , _assertPred :: !pred
                 -- | Message added when assertion was made.
               , assertMsg :: !msg
               }

-- | Predicate that was asserted.
assertPred :: Simple Lens (Assertion pred msg) pred
assertPred = lens _assertPred (\s v -> s { _assertPred = v })

-- | A @FrameIdentifier@ is a unique value that is generated when
--   an new assumption frame is pushed onto the stack, and must
--   be provided when poping values from the stack.   This is
--   primarily a debugging aid, to ensure that stack management
--   remains well-bracketed.
newtype FrameIdentifier = FrameIdentifier Word64
 deriving(Eq,Ord)

-- | A single @AssumptionFrame@ represents a collection
--   of assumtptions.  They will later be recinded when
--   the associated frame is popped from the stack.
data AssumptionFrame pred =
  AssumptionFrame
  { assumeFrameIdent :: FrameIdentifier
  , assumeFrameCond  :: IORef (Seq pred)
  }

-- | A proof goal consists of a collection of assumptions
--   that were in scope when an assertion was made, together
--   with the given assertion.
data ProofGoal pred msg =
  ProofGoal
  { proofAssumptions :: Seq pred
  , proofGoal        :: Assertion pred msg
  }

-- | An assumption stack is a data structure for tracking
--   logical assumptions and proof obligations.  Assumptions
--   can be added to the current stack frame, and stack frames
--   may be pushed (to remember a previous state) or popped
--   to restore a previous state.
data AssumptionStack pred msg =
  AssumptionStack
  { assumeStackGen   :: IO FrameIdentifier
  , currentFrame     :: IORef (AssumptionFrame pred)
  , frameStack       :: IORef (Seq (AssumptionFrame pred))
  , proofObligations :: IORef (Seq (ProofGoal pred msg))
  }

-- | Get a collection of all current stack frames, with newer frames on the right.
allAssumptionFrames :: AssumptionStack pred msg -> IO (Seq (AssumptionFrame pred))
allAssumptionFrames stk =
  do frms <- readIORef (frameStack stk)
     topframe <- readIORef (currentFrame stk)
     return (frms |> topframe)

-- | Compute the height of the pushed stack frames.  NOTE! that this count
--   does not include the current stack frame, and thus the @stackHeight@ will
--   always be one less than the number of frames returned by @allAssumptionFrames@
stackHeight :: AssumptionStack pred msg -> IO Int
stackHeight as = Seq.length <$> readIORef (frameStack as)

-- | Produce a fresh assumption stack.
initAssumptionStack ::
  NonceGenerator IO t ->
  IO (AssumptionStack pred msg)
initAssumptionStack gen =
  do let genM = FrameIdentifier . indexValue <$> freshNonce gen
     ident <- genM
     condRef  <- newIORef mempty
     frmRef <- newIORef (AssumptionFrame ident condRef)
     stackRef <- newIORef mempty
     oblsRef <- newIORef mempty
     return AssumptionStack
            { assumeStackGen = genM
            , currentFrame = frmRef
            , frameStack = stackRef
            , proofObligations = oblsRef
            }

-- | Create a deep copy of the given assumption stack so that this exact state
--   can be restored at a later time, without being modified by destructive
--   updates in the meantime.
--
--   NOTE! however, that proof obligations are NOT copied into the clone.
--   Instead, proof obligations remain only in the original @AssumptionStack@
--   and the new stack has an empty obligation list.
cloneAssumptionStack ::
  AssumptionStack pred msg ->
  IO (AssumptionStack pred msg)
cloneAssumptionStack stk =
  do frm'  <- newIORef =<< cloneFrame =<< readIORef (currentFrame stk)
     frms' <- newIORef =<< traverse cloneFrame =<< readIORef (frameStack stk)
     obls' <- newIORef mempty
     return AssumptionStack
            { assumeStackGen = assumeStackGen stk
            , currentFrame = frm'
            , frameStack = frms'
            , proofObligations = obls'
            }

cloneFrame ::
  AssumptionFrame pred ->
  IO (AssumptionFrame pred)
cloneFrame frm =
  do ps <- newIORef =<< readIORef (assumeFrameCond frm)
     return AssumptionFrame
            { assumeFrameIdent = assumeFrameIdent frm
            , assumeFrameCond = ps
            }

-- | Add the given logical assumption to the current stack frame.
assume ::
  pred ->
  AssumptionStack pred msg ->
  IO ()
assume p stk =
  do frm  <- readIORef (currentFrame stk)
     modifyIORef' (assumeFrameCond frm) (\prev -> prev Seq.|> p)

-- | Add the given collection logical assumption to the current stack frame.
appendAssumptions ::
  Seq pred ->
  AssumptionStack pred msg ->
  IO ()
appendAssumptions ps stk =
  do frm  <- readIORef (currentFrame stk)
     modifyIORef' (assumeFrameCond frm) (\prev -> prev Seq.>< ps)

-- | Add a new proof obligation to the current collection of obligations based
--   on all the assumptions currently in scope and the predicate in the given assertion.
--  
--   Then, assume the given assertion predicate in the current assumption frame.
assert ::
  Assertion pred msg ->
  AssumptionStack pred msg ->
  IO ()
assert p stk =
  do assumes <- collectAssumptions stk
     let gl = ProofGoal assumes p
     modifyIORef' (proofObligations stk) (\obls -> obls |> gl)
     assume (p^.assertPred) stk


-- | Collect all the assumptions currently in scope in this stack frame
--   and all previously-pushed stack frames.
collectAssumptions ::
  AssumptionStack pred msg ->
  IO (Seq pred)
collectAssumptions stk = do
  frms <- readIORef (frameStack stk)
  frm  <- readIORef (currentFrame stk)
  join <$> traverse (readIORef . assumeFrameCond) (frms Seq.|> frm)

-- | Retrieve the current collection of proof obligations.
getProofObligations ::
  AssumptionStack pred msg ->
  IO (Seq (ProofGoal pred msg))
getProofObligations stk = readIORef (proofObligations stk)

-- | Set the current collection of proof obligations.
setProofObligations ::
  Seq (ProofGoal pred msg) ->
  AssumptionStack pred msg ->
  IO ()
setProofObligations obls stk = writeIORef (proofObligations stk) obls

freshFrame ::
  AssumptionStack pred msg ->
  IO (AssumptionFrame pred)
freshFrame stk =
  do ident <- assumeStackGen stk
     cond  <- newIORef mempty
     return AssumptionFrame
            { assumeFrameIdent = ident
            , assumeFrameCond  = cond
            }

-- | Push a new assumption frame on top of the stack.  The
--   returned @FrameIdentifier@ can be used later to pop this
--   frame.  Frames must be pushed and popped in a coeherent
--   well-bracketed way.
pushFrame ::
  AssumptionStack pred msg ->
  IO FrameIdentifier
pushFrame stk =
  do new <- freshFrame stk
     let ident = assumeFrameIdent new
     frm <- readIORef (currentFrame stk)
     writeIORef (currentFrame stk) new
     modifyIORef' (frameStack stk) (\frames -> frames |> frm)
     return ident

-- | Pop a previously-pushed assumption frame from the stack.
--   All assumptions in that frame will be forgotten.
popFrame ::
  FrameIdentifier ->
  AssumptionStack pred msg ->
  IO (AssumptionFrame pred)
popFrame ident stk =
  do frm <- readIORef (currentFrame stk)
     unless (assumeFrameIdent frm == ident)
            (fail "Push/pop mismatch in assumption stack!")
     frms <- readIORef (frameStack stk)
     case Seq.viewr frms of
       frms' Seq.:> top ->
         do writeIORef (currentFrame stk) top
            writeIORef (frameStack stk) frms'
       Seq.EmptyR ->
         do new <- freshFrame stk
            writeIORef (currentFrame stk) new
     return frm

-- | Run an action in the scope of a fresh assumption frame.
--   The frame will be popped and returned on successful
--   completion of the action.  If the action raises an exception,
--   the frame will be popped and discarded.
inFreshFrame ::
  AssumptionStack pred msg ->
  IO a ->
  IO (AssumptionFrame pred, a)
inFreshFrame stk action =
  bracketOnError
     (pushFrame stk)
     (\ident -> popFrame ident stk)
     (\ident -> do x <- action
                   frm <- popFrame ident stk
                   return (frm, x))
