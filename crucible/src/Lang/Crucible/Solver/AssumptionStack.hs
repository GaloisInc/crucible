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
  ( Assertion(..)
  , assertPred
  , ProofGoal(..)
  , AssumptionFrame(..)
  , AssumptionStack(..)
  , FrameIdent
  , initAssumptionStack
  , cloneAssumptionStack
  , collectAssumptions
  , assume
  , appendAssumptions
  , assert
  , getProofObligations
  , setProofObligations
  , pushFrame
  , popFrame
  , inFreshFrame
  ) where

import           Control.Exception (bracketOnError)
import           Control.Lens
import           Control.Monad
import           Data.IORef
import           Data.Parameterized.Nonce
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Lang.Crucible.ProgramLoc

-- | Information about an assertion that was previously made.
data Assertion pred msg
   = Assertion { -- | Location of assertion
                 assertLoc :: !ProgramLoc
                 -- | Predicate that was asserted.
               , _assertPred :: !pred
                 -- | Message added when assertion was made.
               , assertMsg :: !(Maybe msg)
               }

-- | Predicate that was asserted.
assertPred :: Simple Lens (Assertion pred msg) pred
assertPred = lens _assertPred (\s v -> s { _assertPred = v })

newtype FrameIdent t = FrameIdent (Nonce t t)
 deriving(Eq,Ord)

data AssumptionFrame pred t =
  AssumptionFrame
  { assumeFrameIdent :: FrameIdent t
  , assumeFrameCond  :: IORef (Seq pred)
  }

data ProofGoal pred msg =
  ProofGoal
  { proofAssumptions :: Seq pred
  , proofGoal        :: Assertion pred msg
  }

initAssumptionStack ::
  NonceGenerator IO t ->
  IO (AssumptionStack pred t msg)
initAssumptionStack gen =
  do ident <- FrameIdent <$> freshNonce gen
     condRef  <- newIORef mempty
     frmRef <- newIORef (AssumptionFrame ident condRef)
     stackRef <- newIORef mempty
     oblsRef <- newIORef mempty
     return AssumptionStack
            { assumeStackGen = gen
            , currentFrame = frmRef
            , frameStack = stackRef
            , proofObligations = oblsRef
            }

cloneAssumptionStack ::
  AssumptionStack pred t msg ->
  IO (AssumptionStack pred t msg)
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
  AssumptionFrame pred t ->
  IO (AssumptionFrame pred t)
cloneFrame frm =
  do ps <- newIORef =<< readIORef (assumeFrameCond frm)
     return AssumptionFrame
            { assumeFrameIdent = assumeFrameIdent frm
            , assumeFrameCond = ps
            }

data AssumptionStack pred t msg =
  AssumptionStack
  { assumeStackGen   :: NonceGenerator IO t
  , currentFrame     :: IORef (AssumptionFrame pred t)
  , frameStack       :: IORef (Seq (AssumptionFrame pred t))
  , proofObligations :: IORef (Seq (ProofGoal pred msg))
  }

assume ::
  pred ->
  AssumptionStack pred t msg ->
  IO ()
assume p stk =
  do frm  <- readIORef (currentFrame stk)
     modifyIORef' (assumeFrameCond frm) (\prev -> prev Seq.|> p)

appendAssumptions ::
  Seq pred ->
  AssumptionStack pred t msg ->
  IO ()
appendAssumptions ps stk =
  do frm  <- readIORef (currentFrame stk)
     modifyIORef' (assumeFrameCond frm) (\prev -> prev Seq.>< ps)

assert ::
  Assertion pred msg ->
  AssumptionStack pred t msg ->
  IO ()
assert p stk =
  do assumes <- collectAssumptions stk
     let gl = ProofGoal assumes p
     modifyIORef' (proofObligations stk) (\obls -> obls |> gl)
     assume (p^.assertPred) stk


collectAssumptions ::
  AssumptionStack pred t msg ->
  IO (Seq pred)
collectAssumptions stk = do
  frms <- readIORef (frameStack stk)
  frm  <- readIORef (currentFrame stk)
  join <$> traverse (readIORef . assumeFrameCond) (frms Seq.|> frm)

getProofObligations ::
  AssumptionStack pred t msg ->
  IO (Seq (ProofGoal pred msg))
getProofObligations stk = readIORef (proofObligations stk)

setProofObligations ::
  Seq (ProofGoal pred msg) ->
  AssumptionStack pred t msg ->
  IO ()
setProofObligations obls stk = writeIORef (proofObligations stk) obls

freshFrame ::
  AssumptionStack pred t msg ->
  IO (AssumptionFrame pred t)
freshFrame stk =
  do ident <- FrameIdent <$> freshNonce (assumeStackGen stk)
     cond  <- newIORef mempty
     return AssumptionFrame
            { assumeFrameIdent = ident
            , assumeFrameCond  = cond
            }

pushFrame ::
  AssumptionStack pred t msg ->
  IO (FrameIdent t)
pushFrame stk =
  do new <- freshFrame stk
     let ident = assumeFrameIdent new
     frm <- readIORef (currentFrame stk)
     writeIORef (currentFrame stk) new
     modifyIORef' (frameStack stk) (\frames -> frames |> frm)
     return ident

popFrame ::
  FrameIdent t ->
  AssumptionStack pred t msg ->
  IO (AssumptionFrame pred t)
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

inFreshFrame ::
  AssumptionStack pred t msg ->
  IO a ->
  IO (AssumptionFrame pred t, a)
inFreshFrame stk action =
  bracketOnError
     (pushFrame stk)
     (\ident -> popFrame ident stk)
     (\ident -> do x <- action
                   frm <- popFrame ident stk
                   return (frm, x))
