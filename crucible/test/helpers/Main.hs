{-# LANGUAGE AllowAmbiguousTypes #-}

module Main (main) where

import Control.Lens ((^.))
import Data.List (isInfixOf)
import Data.Maybe (fromMaybe)

import Test.Hspec
import Test.Tasty
import Test.Tasty.Hspec (testSpec)
import qualified Test.Tasty.HUnit as TTH

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(Some))
import Lang.Crucible.Backend (SomeBackend(..))
import qualified Lang.Crucible.Backend as LCB
import Lang.Crucible.Backend.Simple (newSimpleBackend)
import Lang.Crucible.Panic
import Lang.Crucible.Simulator.SimError (SimErrorReason(GenericSimError))
import What4.Expr (EmptyExprBuilderState(..))
import What4.Expr.Builder (newExprBuilder)
import qualified What4.Interface as W4I
import What4.FloatMode (FloatModeRepr(FloatIEEERepr))
import qualified What4.LabeledPred as W4L
import qualified What4.ProgramLoc as W4P

import qualified Panic as P

import qualified SymSequence as S

main :: IO ()
main = do
  p <- panicTests
  defaultMain (testGroup "crucible" [p, backendTests, S.tests])

mkBackend :: IO (Some SomeBackend)
mkBackend = do
  Some nonceGen <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState nonceGen
  Some . SomeBackend <$> newSimpleBackend sym

assumePred ::
  LCB.IsSymBackend sym bak =>
  bak ->
  String ->
  W4I.Pred sym ->
  IO ()
assumePred bak msg p =
  LCB.addAssumption bak (LCB.GenericAssumption W4P.initializationLoc msg p)

backendTests :: TestTree
backendTests =
  testGroup
  "Backend"
  [ -- When popping an empty frame, the returned assumptions are just @True@
    TTH.testCase "push/pop nothing" $ do
      Some (SomeBackend bak) <- mkBackend
      asmps <- LCB.popAssumptionFrame bak =<< LCB.pushAssumptionFrame bak
      p <- LCB.assumptionsPred (LCB.backendGetSym bak) asmps
      Just True TTH.@=? W4I.asConstantPred p
    -- When popping a frame, the returned assumptions are the ones that were
    -- assumed in that frame
  , TTH.testCase "push/pop assumptions" $ do
      Some (SomeBackend bak) <- mkBackend
      let sym = LCB.backendGetSym bak
      a <- W4I.freshConstant sym (W4I.safeSymbol "a") W4I.BaseBoolRepr
      assumePred bak "assuming a" a
      frm <- LCB.pushAssumptionFrame bak
      b <- W4I.freshConstant sym (W4I.safeSymbol "b") W4I.BaseBoolRepr
      assumePred bak "assuming b" b
      p <- LCB.assumptionsPred sym =<< LCB.popAssumptionFrame bak frm
      pEqB <- W4I.eqPred sym p b
      Just True TTH.@=? W4I.asConstantPred pEqB
    -- When popping a frame, the returned obligations are the ones that were
    -- asserted in that frame.
  , TTH.testCase "push/pop obligations" $ do
      Some (SomeBackend bak) <- mkBackend
      let sym = LCB.backendGetSym bak
      a <- W4I.freshConstant sym (W4I.safeSymbol "a") W4I.BaseBoolRepr
      assumePred bak "assuming a" a
      b <- W4I.freshConstant sym (W4I.safeSymbol "b") W4I.BaseBoolRepr
      LCB.assert bak b (GenericSimError "asserting b")
      frm <- LCB.pushAssumptionFrame bak
      c <- W4I.freshConstant sym (W4I.safeSymbol "c") W4I.BaseBoolRepr
      assumePred bak "assuming c" c
      d <- W4I.freshConstant sym (W4I.safeSymbol "d") W4I.BaseBoolRepr
      LCB.assert bak d (GenericSimError "asserting d")
      (_asmps, mbGoals) <- LCB.popAssumptionFrameAndObligations bak frm
      [LCB.ProofGoal asmps gl] <- pure (fromMaybe [] (LCB.goalsToList <$> mbGoals))
      asmpsPred <- LCB.assumptionsPred sym asmps
      asmpsEqC <- W4I.eqPred sym c asmpsPred
      Just True TTH.@=? W4I.asConstantPred asmpsEqC
      goalEqD <- W4I.eqPred sym (gl ^. W4L.labeledPred) d
      Just True TTH.@=? W4I.asConstantPred goalEqD
  ]

panicTests :: IO TestTree
panicTests =
  do t <- testSpec "Panicking throws an exception" $
          describe "panic" $
          it "should throw an exception with the right details" $
          shouldThrow (panic "Oh no!" ["line 1", "line 2"]) acceptableExn
     pure $ testGroup "panic" [ t ]
  where
    acceptableExn :: P.Panic Crucible -> Bool
    acceptableExn e =
      let exnMessage = show e
      in isInfixOf "Crucible" exnMessage &&
         isInfixOf "github.com/GaloisInc/crucible/issues" exnMessage
