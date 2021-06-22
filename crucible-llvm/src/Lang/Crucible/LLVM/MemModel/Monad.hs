------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Monad
-- Description      : Monad for organizing memory model operations
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.MemModel.Monad
( MM
, runMM
, overrideMM
, MMAssertReason(..)
, MMAssertion
, annotateMMPred
, mmFailedAssertion
, mmAssert
, mmAssertUndefined
, mmAssertMemError
) where

import           Control.Lens ( (^.), to )
import           Control.Monad.Trans
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Writer

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.SimError
import qualified Lang.Crucible.Simulator.OverrideSim as OSim
import           Lang.Crucible.LLVM.Errors
import qualified Lang.Crucible.LLVM.Errors.MemoryError as ME
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.Partial

import           What4.Interface
import           What4.ProgramLoc

type MMAssertion sym = LabeledPred (Pred sym) (MMAssertReason sym)

data MMAssertReason sym
  = MMAssertError SimErrorReason
  | MMAssertMemError (MemoryError sym)
  | MMAssertUB (UB.UndefinedBehavior (RegValue' sym))

newtype MM sym a = MM (WriterT [MMAssertion sym] (ExceptT (MMAssertReason sym) IO) a)
  deriving (Applicative, Functor, Monad, MonadIO)

runMM :: MM sym a -> IO (Either (MMAssertReason sym) (a, [MMAssertion sym]))
runMM (MM m) = runExceptT (runWriterT m)

overrideMM :: (IsExprBuilder sym, HasLLVMAnn sym) => MM sym a -> OSim.OverrideSim p sym ext rtp args res a
overrideMM mm =
  do sym <- OSim.getSymInterface
     loc <- liftIO (getCurrentProgramLoc sym)
     liftIO (runMM mm) >>= \case
       Left rsn ->
         do a <- liftIO (annotateMMPred sym loc (falsePred sym) rsn)
            OSim.overrideAssertions [a]
            OSim.overrideAbort
              (AssumedFalse (AssumingNoError (a ^. labeledPredMsg . to assertionSimError)))

       Right (x, asserts) ->
         do asserts' <- liftIO (mapM (annotateMMAssert sym loc) asserts)
            OSim.overrideAssertions asserts'
            return x

annotateMMAssert :: (IsExprBuilder sym, HasLLVMAnn sym) =>
  sym ->
  ProgramLoc ->
  MMAssertion sym ->
  IO (Assertion sym)
annotateMMAssert sym loc (LabeledPred p rsn) = annotateMMPred sym loc p rsn

annotateMMPred :: (IsExprBuilder sym, HasLLVMAnn sym) =>
  sym ->
  ProgramLoc ->
  Pred sym ->
  MMAssertReason sym ->
  IO (Assertion sym)
annotateMMPred _ loc p (MMAssertError err) =
  return (LabeledPred p (AssertionReason False (SimError loc err)))
  
annotateMMPred sym loc p (MMAssertMemError merr@(MemoryError mop _)) =
  do (n, p') <- annotateTerm sym p
     ?recordLLVMAnnotation (BoolAnn n) (BBMemoryError merr)
     let msg = "Error performing " ++ ME.descMemoryOp mop
     let err = AssertFailureSimError msg ""
     return (LabeledPred p' (AssertionReason False (SimError loc err)))

annotateMMPred sym loc p (MMAssertUB ub) =
  do (n, p') <- annotateTerm sym p
     ?recordLLVMAnnotation (BoolAnn n) (BBUndefinedBehavior ub)
     let err = AssertFailureSimError "Undefined behavior encountered" (show (UB.explain ub))
     return (LabeledPred p' (AssertionReason False (SimError loc err)))


mmFailedAssertion :: MMAssertReason sym -> MM sym a
mmFailedAssertion rsn = MM (lift (throwE rsn))

mmAssert :: IsExprBuilder sym => Pred sym -> MMAssertReason sym -> MM sym ()
mmAssert p rsn
  | Just False <- asConstantPred p = mmFailedAssertion rsn
  | otherwise = MM (tell [LabeledPred p rsn])

mmAssertUndefined :: IsExprBuilder sym => Pred sym -> UB.UndefinedBehavior (RegValue' sym) -> MM sym ()
mmAssertUndefined p ub = mmAssert p (MMAssertUB ub)

mmAssertMemError :: (IsExprBuilder sym, 1 <= w) =>
  Pred sym ->
  ME.MemoryOp sym w ->
  ME.MemoryErrorReason sym w ->
  MM sym ()
mmAssertMemError p mop rsn = mmAssert p (MMAssertMemError (MemoryError mop rsn))
