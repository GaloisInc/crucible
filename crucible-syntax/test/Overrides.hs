{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Overrides where

import Control.Lens hiding ((:>), Empty)
import Control.Monad (forM_)
import Control.Monad.IO.Class
import Control.Monad.ST
import System.IO

import Data.Parameterized.Context hiding (view)

import What4.Expr.Builder
import What4.Interface
import What4.SatResult
import What4.Solver.Z3 (runZ3InOverride, z3Options, z3Path)

import Lang.Crucible.Backend
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.SimError (ppSimError)


-- Some overrides for testing purposes.
setupOverrides ::
  (IsSymInterface sym, sym ~ (ExprBuilder t st)) =>
  sym -> HandleAllocator -> IO [(FnBinding p sym ext, Position)]
setupOverrides _ ha =
  do f1 <- FnBinding <$> mkHandle ha "symbolicBranchTest"
                     <*> pure (UseOverride (mkOverride "symbolicBranchTest" symbolicBranchTest))
     f2 <- FnBinding <$> mkHandle ha "symbolicBranchesTest"
                     <*> pure (UseOverride (mkOverride "symbolicBranchesTest" symbolicBranchesTest))
     return [(f1, InternalPos),(f2,InternalPos)]


-- Test the @symbolicBranch@ override operation.
symbolicBranchTest :: IsSymInterface sym =>
  OverrideSim p sym ext r
    (EmptyCtx ::> BoolType ::> IntegerType ::> IntegerType) IntegerType (RegValue sym IntegerType)
symbolicBranchTest =
  do args <- getOverrideArgs
     let p = reg @0 args
     z <- symbolicBranch p args thn (Just (OtherPos "then branch")) args els (Just (OtherPos "else branch"))
     return z

 where
 thn = reg @1 <$> getOverrideArgs
 els = reg @2 <$> getOverrideArgs


-- Test the @symbolicBranches@ override operation.
symbolicBranchesTest :: IsSymInterface sym =>
  OverrideSim p sym ext r
    (EmptyCtx ::> IntegerType ::> IntegerType) IntegerType (RegValue sym IntegerType)
symbolicBranchesTest =
  do sym <- getSymInterface
     x <- reg @0 <$> getOverrideArgs
     x2 <- liftIO $ intAdd sym x x
     p1 <- liftIO $ intEq sym x =<< intLit sym 1
     p2 <- liftIO $ intEq sym x =<< intLit sym 2
     p3 <- liftIO $ intEq sym x =<< intLit sym 3
     z <- symbolicBranches (RegMap (Empty :> RegEntry IntegerRepr x2))
            [ (p1, b1, Just (OtherPos "first branch"))
            , (p2, b2, Just (OtherPos "second branch"))
            , (p3, b3 sym, Just (OtherPos "third branch"))
            , (truePred sym, b4, Just (OtherPos "default branch"))
            ]
     return z

  where
  b1 =
     do y <- reg @1 <$> getOverrideArgs
        return y

  b2 =
     do x2 <- reg @2 <$> getOverrideArgs
        overrideReturn x2

  b3 sym =
     do y <- reg @1 <$> getOverrideArgs
        x2 <- reg @2 <$> getOverrideArgs
        liftIO $ intAdd sym y x2

  b4 = overrideError (GenericSimError "fall-through branch")
