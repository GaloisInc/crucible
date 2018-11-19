{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module AI (
  aiTests
  ) where

import Control.Monad ( guard )
import Control.Monad.ST ( ST, runST )
import Prelude

import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Data.Parameterized.Context as PU
import qualified Data.Parameterized.Map as PM

import qualified What4.FunctionName as C
import qualified What4.ProgramLoc as P

import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.SSAConversion as SSA
import Lang.Crucible.Syntax
import Lang.Crucible.Analysis.Fixpoint hiding ( Ignore(..) )

import EvenOdd
import Max

aiTests :: T.TestTree
aiTests = T.testGroup "Abstract Interpretation" [
  runTest "eo_p1" (const eo_p1),
  runTest "eo_p2" (const eo_p2),
  runTest "eo_p3" (const eo_p3),
  runTest "eo_p4" (const eo_p4),
  runTest "max_p1" (const max_p1),
  runTest "max_p2" (const max_p2)
  ]

runTest :: (C.IsSyntaxExtension ext, C.ShowF dom) => String -> (forall h . () -> TestCase h ext dom) -> T.TestTree
runTest name tc = T.testCase name $ runST $ testAI (tc ())

testAI :: (C.IsSyntaxExtension ext, C.ShowF dom) => TestCase h ext dom -> ST h T.Assertion
testAI TC { tcHandle = hdl
          , tcDef = def
          , tcGlobals = g
          , tcAssignment = a0
          , tcCheck = check
          , tcDom = dom
          , tcInterp = interp
          } = do
  fh <- hdl
  (G.SomeCFG cfg, _) <- G.defineFunction P.InternalPos fh def
  case SSA.toSSA cfg of
    C.SomeCFG cfg' -> do
      let (assignment', rabs) = forwardFixpoint dom interp cfg' g a0
          mWorklist = do
            -- If we aren't widening, also compute the same
            -- approximation using the worklist-based iteration
            -- strategy.  The result should be the same.
            guard (isWTOIter (domIter dom))
            let dom' = dom { domIter = Worklist }
            return $ forwardFixpoint dom' interp cfg' g a0
      return (check cfg' assignment' rabs mWorklist)

data TestCase h ext dom =
  forall init ret t .
  TC { tcDef :: G.FunctionDef ext h t init ret
     , tcHandle :: ST h (C.FnHandle init ret)
     , tcDom :: Domain dom
     , tcInterp :: Interpretation ext dom
     , tcAssignment :: PU.Assignment dom init
     , tcGlobals :: PM.MapF C.GlobalVar dom
     , tcCheck :: forall blocks tp
                . C.CFG ext blocks init ret
               -> PU.Assignment (PointAbstraction dom) blocks
               -> dom tp
               -> Maybe (PU.Assignment (PointAbstraction dom) blocks, dom tp)
               -> T.Assertion
     }

genHandle :: ST s (C.FnHandle (C.EmptyCtx C.::> C.IntegerType) C.IntegerType)
genHandle = C.withHandleAllocator $ \ha -> C.mkHandle ha C.startFunctionName

type EvenOdd' = Pointed EvenOdd
type Max' = Pointed Max

eo_p1 :: TestCase h EOExt EvenOdd'
eo_p1 = TC { tcDef = \ia -> (Ignore, gen ia)
           , tcHandle = genHandle
           , tcAssignment = PU.empty PU.:> Pointed Even
           , tcGlobals = PM.empty
           , tcCheck = check
           , tcDom = evenOddDom
           , tcInterp = evenOddInterp
           }
  where
    check _cfg _assignment rabs mWorklist = do
      T.assertEqual "retVal" Top rabs
      case mWorklist of
        Nothing -> T.assertFailure "Expected worklist result"
        Just (_, rabs') -> T.assertEqual "WL Result" rabs rabs'

    gen initialAssignment = do
      r0 <- G.newReg (intLitReg 0)
      let x = initialAssignment PU.! PU.baseIndex
      let c = app (atom x `C.IntLt` litExpr 5)
      G.ifte_ c (then_ r0) (else_ r0)
      rval <- G.readReg r0
      G.returnFromFunction rval

    then_ r0 = do
      G.assignReg r0 (litExpr (negate 5))

    else_ r0 = do
      G.assignReg r0 (litExpr 10)

eo_p2 :: TestCase h EOExt EvenOdd'
eo_p2 = TC { tcDef = \ia -> (Ignore, gen ia)
           , tcHandle = genHandle
           , tcAssignment = PU.empty PU.:> Pointed Even
           , tcGlobals = PM.empty
           , tcCheck = check
           , tcDom = evenOddDom
           , tcInterp = evenOddInterp
           }
  where
    check _cfg _assignment rabs mWorklist = do
      T.assertEqual "retVal" (Pointed Even) rabs
      case mWorklist of
        Nothing -> T.assertFailure "Expected worklist result"
        Just (_, rabs') -> do
          T.assertEqual "WL Result" rabs rabs'

    gen initialAssignment = do
      r0 <- G.newReg (intLitReg 0)
      let x = initialAssignment PU.! PU.baseIndex
      let c = app (atom x `C.IntLt` litExpr 5)
      G.ifte_ c (then_ r0) (else_ r0)
      rval <- G.readReg r0
      G.returnFromFunction rval

    then_ r0 = do
      G.assignReg r0 (litExpr 6)

    else_ r0 = do
      G.assignReg r0 (litExpr 10)

eo_p3 :: TestCase h EOExt EvenOdd'
eo_p3 = TC { tcDef = \ia -> (Ignore, gen ia)
           , tcHandle = genHandle
           , tcAssignment = PU.empty PU.:> Pointed Even
           , tcGlobals = PM.empty
           , tcCheck = check
           , tcDom = evenOddDom
           , tcInterp = evenOddInterp
           }
  where
    check _cfg _assignment rabs mWorklist = do
      T.assertEqual "retVal" (Pointed Even) rabs
      case mWorklist of
        Nothing -> T.assertFailure "Expected worklist result"
        Just (_, rabs') -> T.assertEqual "WL Result" rabs rabs'

    gen initialAssignment = do
      r0 <- G.newReg (intLitReg 0)
      r1 <- G.newReg (intLitReg 0)
      let x = initialAssignment PU.! PU.baseIndex
      let c = app (atom x `C.IntLt` litExpr 5)
      G.ifte_ c (then_ r0 r1) (else_ r0 r1)
      rval <- G.readReg r1
      G.returnFromFunction rval

    then_ r0 r1 = do
      v <- G.readReg r0
      G.assignReg r1 (app (v `C.IntAdd` litExpr 2))

    else_ r0 r1 = do
      v <- G.readReg r0
      G.assignReg r1 (app (v `C.IntAdd` litExpr 10))

eo_p4 :: TestCase h EOExt EvenOdd'
eo_p4 = TC { tcDef = \ia -> (Ignore, gen ia)
           , tcHandle = genHandle
           , tcAssignment = PU.empty PU.:> Pointed Even
           , tcGlobals = PM.empty
           , tcCheck = check
           , tcDom = evenOddDom
           , tcInterp = evenOddInterp
           }
  where
    check _cfg _assignment rabs mWorklist = do
      T.assertEqual "retVal" (Pointed Odd) rabs
      case mWorklist of
        Nothing -> T.assertFailure "Expected worklist result"
        Just (_, rabs') -> T.assertEqual "WL Result" rabs rabs'

    gen initialAssignment = do
      r0 <- G.newReg (intLitReg 0)
      r1 <- G.newReg (intLitReg 0)
      let x = initialAssignment PU.! PU.baseIndex
      let c = app (atom x `C.IntLt` litExpr 5)
      G.ifte_ c (then_ r0 r1) (else_ r0 r1)
      rval <- G.readReg r1
      G.returnFromFunction rval

    then_ r0 r1 = do
      v <- G.readReg r0
      G.assignReg r1 (app (v `C.IntAdd` litExpr 3))

    else_ r0 r1 = do
      v <- G.readReg r0
      G.assignReg r1 (app (v `C.IntAdd` litExpr 11))

max_p1 :: TestCase h SyntaxExt Max'
max_p1 = TC { tcDef = \ia -> (Ignore, gen ia)
            , tcHandle = genHandle
            , tcAssignment = PU.empty PU.:> Pointed (Max 5)
            , tcGlobals = PM.empty
            , tcCheck = check
            , tcDom = maxDom
            , tcInterp = maxInterp
            }
  where
    check _cfg _assignment rabs _ =
      T.assertEqual "retVal" (Pointed (Max 11)) rabs

    gen initialAssignment = do
      let x = initialAssignment PU.! PU.baseIndex
      let c = app (atom x `C.IntLt` litExpr 5)
      r0 <- G.newReg (atom x)
      G.ifte_ c (then_ r0) (else_ r0)
      rval <- G.readReg r0
      G.returnFromFunction rval

    then_ r0 = do
      v <- G.readReg r0
      G.assignReg r0 (app (v `C.IntAdd` litExpr 5))

    else_ r0 = do
      v <- G.readReg r0
      G.assignReg r0 (app (v `C.IntAdd` litExpr 6))

max_p2 :: TestCase h SyntaxExt Max'
max_p2 = TC { tcDef = \ia -> (Ignore, gen ia)
            , tcHandle = genHandle
            , tcAssignment = PU.empty PU.:> Pointed (Max 5)
            , tcGlobals = PM.empty
            , tcCheck = check
            , tcDom = maxDom
            , tcInterp = maxInterp
            }
  where
    check _cfg _assignment rabs _ = do
      T.assertEqual "retVal" Top rabs

    gen initialAssignment = do
      let x = initialAssignment PU.! PU.baseIndex
      r0 <- G.newReg (atom x)
      G.while (P.InternalPos, test r0) (P.InternalPos, body r0)
      rval <- G.readReg r0
      G.returnFromFunction rval

    test r0 = do
      v <- G.readReg r0
      return (app (v `C.IntLt` litExpr 100))

    body r0 = do
      v <- G.readReg r0
      G.assignReg r0 (app (v `C.IntAdd` litExpr 1))


intLitReg :: C.IsSyntaxExtension exp => Integer -> G.Expr exp s C.IntegerType
intLitReg i = litExpr i

atom :: G.Atom s tp -> G.Expr exp s tp
atom = G.AtomExpr

data Ignore i = Ignore

isWTOIter :: IterationStrategy dom -> Bool
isWTOIter WTO = True
isWTOIter _ = False
