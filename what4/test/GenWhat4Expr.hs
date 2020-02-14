{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : GenWhat4Expr
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : kquick@galois.com

This module provides Hedgehog generators for What4 expression values
that have associated Haskell counterparts; the Haskell value predicts
the What4 value on evaluation.

The What4 expression is often generated from a Haskell value
evaluation, so the "distance" between the tests and the implementation
might be seen as fairly small.  However, there is a lot of
simplification and subterm-elimination that is attempted in What4
expressions; this testing can verify the expected *functional*
behavior of the expressions as various simplifications and
implementation adjustments are made.

Because these are generated expressions, they don't tend to shrink as
much one would expect (e.g.  @(5 + 1)@ will not be shrunk to @6@)
because that requires domain-specific expression evaluation.  When
failures occur, it can be helpful to temporarily edit out portions of
these generators to attempt simplification.
-}

module GenWhat4Expr where

import           Data.Bits
import           Data.Word
import           GHC.Natural
import           GHC.TypeNats ( KnownNat )
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Internal.Gen as IGen
import qualified Hedgehog.Range as Range
import           Test.Tasty.HUnit
import           What4.Interface


-- | A convenience class to extract the description string and haskell
-- value (and type) for any type of TestExpr.
class IsTestExpr x where
  type HaskellTy x
  desc :: x -> String
  testval :: x -> HaskellTy x

  -- n.b. cannot ad What4BTy, because the target (SymExpr) is a type
  -- synonym for a type family and type family instances cannot
  -- specify a type synonym as a target.
  --
  -- data What4BTy x :: BaseType -- -> Type
  -- type What4BTy x :: Type -> Type

  -- testexpr :: forall sym. (IsExprBuilder sym) => x -> sym -> IO (What4BTy x sym)

pdesc :: IsTestExpr x => x -> String
pdesc s = "(" <> desc s <> ")"

----------------------------------------------------------------------

-- Somewhat awkward, but when using Gen.subtermN for Gen.recursive,
-- each of the subterms is required to have the same type as the
-- result of the recursive term.  This is fine for uniform values
-- (e.g. simply-typed lambda calculi) but for a DSL like the What4
-- IsExprBuilder this means that even though there are separate
-- generators here for each subtype the results must be wrapped in a
-- common type that can hold all the 't' results from 'SymExpr sym
-- t'... the 'TestExpr' type here.  There's a lot of expectation of
-- which value is present when unwrapping (this is just test code),
-- and there various uses of Hedgehog 'Gen.filter' to ensure the right
-- value is returned even in the face of shrinking: when shrinking a
-- recursive term (e.g. "natEq x y") the result is a 'Pred sym', but
-- shrinking will try to eliminate the 'natEq' wrapper and end up
-- trying to return 'x' or 'y', which is a 'SymNat sym' instead.

data TestExpr = TE_Bool PredTestExpr
              | TE_Nat NatTestExpr
              | TE_BV8 BV8TestExpr
              | TE_BV16 BV16TestExpr
              | TE_BV32 BV32TestExpr
              | TE_BV64 BV64TestExpr

isBoolTestExpr, isNatTestExpr,
  isBV8TestExpr, isBV16TestExpr, isBV32TestExpr, isBV64TestExpr
  :: TestExpr -> Bool

isBoolTestExpr = \case
  TE_Bool _ -> True
  _ -> False

isNatTestExpr = \case
  TE_Nat _ -> True
  _ -> False

isBV8TestExpr = \case
  TE_BV8 _ -> True
  _ -> False

isBV16TestExpr = \case
  TE_BV16 _ -> True
  _ -> False

isBV32TestExpr = \case
  TE_BV32 _ -> True
  _ -> False

isBV64TestExpr = \case
  TE_BV64 _ -> True
  _ -> False

----------------------------------------------------------------------

data PredTestExpr =
  PredTest { preddsc :: String
           , predval :: Bool
           , predexp :: forall sym. (IsExprBuilder sym) => sym -> IO (Pred sym)
           }

instance IsTestExpr PredTestExpr where
  type HaskellTy PredTestExpr = Bool
  desc = preddsc
  testval = predval


genBoolCond :: (HasCallStack, Monad m) => GenT m TestExpr
genBoolCond = Gen.recursive Gen.choice
  [
    return $ TE_Bool $ PredTest "true" True $ return . truePred
  , return $ TE_Bool $ PredTest "false" False $ return . falsePred
  ]
  $
  let boolTerm = IGen.filterT isBoolTestExpr genBoolCond
      natTerm = IGen.filterT isNatTestExpr genNatTestExpr
      bv8Term = IGen.filterT isBV8TestExpr genBV8TestExpr
      bv16Term = IGen.filterT isBV16TestExpr genBV16TestExpr
      bv32Term = IGen.filterT isBV32TestExpr genBV32TestExpr
      bv64Term = IGen.filterT isBV64TestExpr genBV64TestExpr
      subBoolTerm2 gen = Gen.subterm2 boolTerm boolTerm
                         (\(TE_Bool x) (TE_Bool y) -> TE_Bool $ gen x y)
      subBoolTerm3 gen = Gen.subterm3 boolTerm boolTerm boolTerm
                         (\(TE_Bool x) (TE_Bool y) (TE_Bool z) -> TE_Bool $ gen x y z)
      subNatTerms2 gen = Gen.subterm2 natTerm natTerm (\(TE_Nat x) (TE_Nat y) -> TE_Bool $ gen x y)
      -- subBV16Terms2 gen = Gen.subterm2 bv16Term bv16Term (\(TE_BV16 x) (TE_BV16 y) -> TE_Bool $ gen x y)
      -- subBV8Terms2 gen = Gen.subterm2 bv8Term bv8Term (\(TE_BV8 x) (TE_BV8 y) -> TE_Bool $ gen x y)
  in
  [
    Gen.subterm genBoolCond
    (\(TE_Bool itc) -> TE_Bool $ PredTest ("not " <> pdesc itc)
                       (not $ testval itc)
                       (\sym -> notPred sym =<< predexp itc sym))

  , subBoolTerm2
    (\x y ->
       PredTest ("and " <> pdesc x <> " " <> pdesc y)
       (testval x && testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   andPred sym x' y'
       ))

  , subBoolTerm2
    (\x y ->
       PredTest ("or " <> pdesc x <> " " <> pdesc y)
       (testval x || testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   orPred sym x' y'
       ))

  , subBoolTerm2
    (\x y ->
       PredTest ("eq " <> pdesc x <> " " <> pdesc y)
       (testval x == testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   eqPred sym x' y'
       ))

  , subBoolTerm2
    (\x y ->
       PredTest ("xor " <> pdesc x <> " " <> pdesc y)
       (testval x `xor` testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   xorPred sym x' y'
       ))

  , subBoolTerm3
    (\c x y ->
       PredTest ("ite " <> pdesc c <> " " <> pdesc x <> " " <> pdesc y)
       (if testval c then testval x else testval y)
       (\sym -> do c' <- predexp c sym
                   x' <- predexp x sym
                   y' <- predexp y sym
                   itePred sym c' x' y'
       ))

  , subNatTerms2
    (\x y ->
        PredTest ("natEq " <> pdesc x <> " " <> pdesc y)
        (testval x == testval y)
        (\sym -> do x' <- natexpr x sym
                    y' <- natexpr y sym
                    natEq sym x' y'
        ))

  , subNatTerms2
    (\x y ->
        PredTest (pdesc x <> " nat.<= " <> pdesc y)
        (testval x <= testval y)
        (\sym -> do x' <- natexpr x sym
                    y' <- natexpr y sym
                    natLe sym x' y'
        ))

  , subNatTerms2
    (\x y ->
        PredTest (pdesc x <> " nat.< " <> pdesc y)
        (testval x < testval y)
        (\sym -> do x' <- natexpr x sym
                    y' <- natexpr y sym
                    natLt sym x' y'
        ))

  , Gen.subterm2 natTerm bv16Term
    -- Note [natTerm]: natTerm is used as the index into
    -- bv16term. This is somewhat inefficient, but saves the
    -- administrative overhead of another TestExpr member.  However,
    -- the NatExpr could be greater than the bit range, so mod the
    -- result if necessary.  Also note that the testBitBV uses an
    -- actual Natural, not a What4 Nat, so the natval is used and the
    -- natexpr is ignored.
    (\(TE_Nat i) (TE_BV16 v) -> TE_Bool $  -- KWQ: bvsized
      let ival = testval i `mod` 16 in
      PredTest
      (pdesc v <> "[" <> show ival <> "]")
      (testBit (testval v) (fromEnum ival))
      (\sym -> testBitBV sym ival =<< bvexpr v sym))

  ]
  ++ bvPredExprs bv8Term (\(TE_BV8 x) -> x) bv8expr 8
  ++ bvPredExprs bv16Term (\(TE_BV16 x) -> x) bvexpr 16
  ++ bvPredExprs bv32Term (\(TE_BV32 x) -> x) bv32expr 32
  ++ bvPredExprs bv64Term (\(TE_BV64 x) -> x) bv64expr 64


bvPredExprs :: ( Monad m
               , HaskellTy bvtestexpr ~ Integer
               , IsTestExpr bvtestexpr
               , 1 <= w
               )
            => GenT m TestExpr
            -> (TestExpr -> bvtestexpr)
            -> (bvtestexpr
                -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w)))
            -> Natural
            -> [GenT m TestExpr]
bvPredExprs bvTerm projTE expr width =
  let subBVTerms2 gen = Gen.subterm2 bvTerm bvTerm
                        (\x y -> TE_Bool $ gen (projTE x) (projTE y))
      mask = (.&.) (2^width - 1)
      uBV v = if v >= 0 then v else 2^width + v
      sBV v = let norm = if v >= 0 then v else mask (v - 2^width)
              in if norm >= (2^(width-1)) then norm - 2^width else norm
      pfx o = "bv" <> show width <> "." <> o
  in
  [
    subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvEq", pdesc y])
        (uBV (testval x) == uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvEq sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvNe", pdesc y])
        (uBV (testval x) /= uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvNe sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUlt", pdesc y])
        (uBV (testval x) < uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUlt sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUle", pdesc y])
        (uBV (testval x) <= uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUle sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUge", pdesc y])
        (uBV (testval x) >= uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUge sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUgt", pdesc y])
        (uBV (testval x) > uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUgt sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSlt", pdesc y])
        (sBV (testval x) < sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSlt sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSle", pdesc y])
        (sBV (testval x) <= sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSle sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSge", pdesc y])
        (sBV (testval x) >= sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSge sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSgt", pdesc y])
        (sBV (testval x) > sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSgt sym x' y'
        ))

  , Gen.subterm bvTerm
    (\vt -> TE_Bool $ let v = projTE vt in
        PredTest
        (pfx "isneg? " <> pdesc v)
        (mask (testval v) < 0 || mask (testval v) >= 2^(width-1))
        (\sym -> bvIsNeg sym =<< expr v sym))

  , Gen.subterm bvTerm
    (\vt -> TE_Bool $ let v = projTE vt in
        PredTest
        (pfx "isNonZero? " <> pdesc v)
        (testval v /= 0)
        (\sym -> bvIsNonzero sym =<< expr v sym))

  ]


----------------------------------------------------------------------

data NatTestExpr = NatTestExpr { natdesc :: String
                               , natval  :: Natural
                               , natexpr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymNat sym)
                               }

instance IsTestExpr NatTestExpr where
  type HaskellTy NatTestExpr = Natural
  desc = natdesc
  testval = natval

genNatTestExpr :: Monad m => GenT m TestExpr
genNatTestExpr = Gen.recursive Gen.choice
  [
    do n <- Gen.integral $ Range.constant 0 6  -- keep the range small, or will never see dup values for natEq
       return $ TE_Nat $ NatTestExpr (show n) n $ \sym -> natLit sym n
  ]
  $
  let natTerm = IGen.filterT isNatTestExpr genNatTestExpr
      natTermNZ = IGen.filterT isNatNZTestExpr genNatTestExpr
      isNatNZTestExpr = \case
        TE_Nat n -> testval n > 0
        _ -> False
      subNatTerms2 gen = Gen.subterm2 natTerm natTerm (\(TE_Nat x) (TE_Nat y) -> TE_Nat $ gen x y)
      subNatTerms2nz gen = Gen.subterm2 natTerm natTermNZ
                           (\(TE_Nat x) (TE_Nat y) -> TE_Nat $ gen x y)
  in
  [
    subNatTerms2 (\x y -> NatTestExpr (pdesc x <> " nat.+ " <> pdesc y)
                          (testval x + testval y)
                          (\sym -> do x' <- natexpr x sym
                                      y' <- natexpr y sym
                                      natAdd sym x' y'
                          ))
  , subNatTerms2
    (\x y ->
       -- avoid creating an invalid negative Nat
        if testval x > testval y
        then NatTestExpr (pdesc x <> " nat.- " <> pdesc y)
             (testval x - testval y)
             (\sym -> do x' <- natexpr x sym
                         y' <- natexpr y sym
                         natSub sym x' y'
             )
        else NatTestExpr (pdesc y <> " nat.- " <> pdesc x)
             (testval y - testval x)
             (\sym -> do x' <- natexpr x sym
                         y' <- natexpr y sym
                         natSub sym y' x'
             ))
  , subNatTerms2
    (\x y -> NatTestExpr (pdesc x <> " nat.* " <> pdesc y)
             (testval x * testval y)
             (\sym -> do x' <- natexpr x sym
                         y' <- natexpr y sym
                         natMul sym x' y'
             ))
  , subNatTerms2nz  -- nz on 2nd to avoid divide-by-zero
    (\x y -> NatTestExpr (pdesc x <> " nat./ " <> pdesc y)
             (testval x `div` testval y)
             (\sym -> do x' <- natexpr x sym
                         y' <- natexpr y sym
                         natDiv sym x' y'
             ))
  , subNatTerms2nz  -- nz on 2nd to avoid divide-by-zero
    (\x y -> NatTestExpr (pdesc x <> " nat.mod " <> pdesc y)
             (testval x `mod` testval y)
             (\sym -> do x' <- natexpr x sym
                         y' <- natexpr y sym
                         natMod sym x' y'
             ))
  , Gen.subterm3
    (IGen.filterT isBoolTestExpr genBoolCond)
    natTerm natTerm
    (\(TE_Bool c) (TE_Nat x) (TE_Nat y) -> TE_Nat $ NatTestExpr
      (pdesc c <> " nat.? " <> pdesc x <> " : " <> pdesc y)
      (if testval c then testval x else testval y)
      (\sym -> do c' <- predexp c sym
                  x' <- natexpr x sym
                  y' <- natexpr y sym
                  natIte sym c' x' y'
      ))
  ]


----------------------------------------------------------------------

-- TBD: genIntTestExpr :: Monad m => GenT m TestExpr


----------------------------------------------------------------------

allbits8, allbits16, allbits32, allbits64 :: Integer
allbits8  = (2 :: Integer) ^ (8 :: Integer) - 1
allbits16 = (2 :: Integer) ^ (16 :: Integer) - 1
allbits32 = (2 :: Integer) ^ (32 :: Integer) - 1
allbits64 = (2 :: Integer) ^ (64 :: Integer) - 1

genBV8val :: Monad m => GenT m Integer
genBV8val = Gen.choice
            [
              -- keep the range small, or will never see dup values
              Gen.integral $ Range.constantFrom 0 (-10) 10
            , Gen.integral $ Range.constant (128-1) (128+1)
            , Gen.integral $ Range.constant (allbits8-2) allbits8
            ]

data BV8TestExpr = BV8TestExpr { bv8desc :: String
                               , bv8val  :: Integer
                               , bv8expr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 8)
                               }

instance IsTestExpr BV8TestExpr where
  type HaskellTy BV8TestExpr = Integer
  desc = bv8desc
  testval = bv8val

genBV8TestExpr :: Monad m => GenT m TestExpr
genBV8TestExpr = let ret8 = return . TE_BV8 in
  Gen.recursive Gen.choice
  [
    do n <- genBV8val
       ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> bvLit sym knownRepr n
  , ret8 $ BV8TestExpr ("0`8") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits8
    in ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits8 `shiftR` 1
    in ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits8 `xor` (allbits8 `shiftR` 1)
    in ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  let bvTerm = IGen.filterT isBV8TestExpr genBV8TestExpr
  in bvExprs bvTerm TE_BV8 (\(TE_BV8 x) -> x) BV8TestExpr bv8expr 8
     (fromIntegral :: Integer -> Word8)


genBV16val :: Monad m => GenT m Integer
genBV16val = Gen.choice
             [
               -- keep the range small, or will never see dup values
               Gen.integral $ Range.constantFrom 0 (-10) 10
             , Gen.integral $ Range.constant (allbits8-1) (allbits8+2)
             , Gen.integral $ Range.constant ((-1) * (allbits8+2)) ((-1) * (allbits8-1))
             , Gen.integral $ Range.constant (allbits16-2) allbits16
             ]

data BV16TestExpr =
  BV16TestExpr { bvdesc :: String
               , bvval  :: Integer
               , bvexpr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 16)
               }

instance IsTestExpr BV16TestExpr where
  type HaskellTy BV16TestExpr = Integer
  desc = bvdesc
  testval = bvval

genBV16TestExpr :: Monad m => GenT m TestExpr
genBV16TestExpr = let ret16 = return . TE_BV16 in
  Gen.recursive Gen.choice
  [
    do n <- genBV16val
       ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> bvLit sym knownRepr n
  , ret16 $ BV16TestExpr ("0`16") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits16
    in ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits16 `shiftR` 1
    in ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits16 `xor` (allbits16 `shiftR` 1)
    in ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  let bvTerm = IGen.filterT isBV16TestExpr genBV16TestExpr
  in
  bvExprs bvTerm TE_BV16 (\(TE_BV16 x) -> x) BV16TestExpr bvexpr 16
  (fromIntegral :: Integer -> Word16)
  ++
  [
    -- TBD: bvZext
    -- TBD: bvSext
    -- TBD: bvTrunc
    -- TBD: bvConcat
    -- TBD: bvSelect
  ]


genBV32val :: Monad m => GenT m Integer
genBV32val = Gen.choice
             [
               -- keep the range small, or will never see dup values
               Gen.integral $ Range.constantFrom 0 (-10) 10
             , Gen.integral $ Range.constant (allbits8-1) (allbits8+2)
             , Gen.integral $ Range.constant (allbits16-1) (allbits16+2)
             , Gen.integral $ Range.constant ((-1) * (allbits16+2)) ((-1) * (allbits16-1))
             , Gen.integral $ Range.constant (allbits32-2) allbits32
             ]


data BV32TestExpr =
  BV32TestExpr { bv32desc :: String
               , bv32val  :: Integer
               , bv32expr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 32)
               }

instance IsTestExpr BV32TestExpr where
  type HaskellTy BV32TestExpr = Integer
  desc = bv32desc
  testval = bv32val

genBV32TestExpr :: Monad m => GenT m TestExpr
genBV32TestExpr = let ret32 = return . TE_BV32 in
  Gen.recursive Gen.choice
  [
    do n <- genBV32val
       ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> bvLit sym knownRepr n
  , ret32 $ BV32TestExpr ("0`32") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits32
    in ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits32 `shiftR` 1
    in ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits32 `xor` (allbits32 `shiftR` 1)
    in ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  let bvTerm = IGen.filterT isBV32TestExpr genBV32TestExpr
  in
  bvExprs bvTerm TE_BV32 (\(TE_BV32 x) -> x) BV32TestExpr bv32expr 32
  (fromIntegral :: Integer -> Word32)


genBV64val :: Monad m => GenT m Integer
genBV64val = Gen.choice
             [
               -- keep the range small, or will never see dup values
               Gen.integral $ Range.constantFrom 0 (-10) 10
             , Gen.integral $ Range.constant (allbits8-1) (allbits8+2)
             , Gen.integral $ Range.constant (allbits16-1) (allbits16+2)
             , Gen.integral $ Range.constant (allbits32-1) (allbits32+2)
             , Gen.integral $ Range.constant ((-1) * (allbits32+2)) ((-1) * (allbits32-1))
             , Gen.integral $ Range.constant (allbits64-2) allbits64
             ]


data BV64TestExpr =
  BV64TestExpr { bv64desc :: String
               , bv64val  :: Integer
               , bv64expr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 64)
               }

instance IsTestExpr BV64TestExpr where
  type HaskellTy BV64TestExpr = Integer
  desc = bv64desc
  testval = bv64val

genBV64TestExpr :: Monad m => GenT m TestExpr
genBV64TestExpr = let ret64 = return . TE_BV64 in
  Gen.recursive Gen.choice
  [
    do n <- genBV64val
       ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> bvLit sym knownRepr n
  , ret64 $ BV64TestExpr ("0`64") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits64
    in ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits64 `shiftR` 1
    in ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits64 `xor` (allbits64 `shiftR` 1)
    in ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  let bvTerm = IGen.filterT isBV64TestExpr genBV64TestExpr
  in bvExprs bvTerm TE_BV64 (\(TE_BV64 x) -> x) BV64TestExpr bv64expr 64
     (fromIntegral :: Integer -> Word64)
  -- n.b. toEnum . fromEnum doesn't work for very large Word64 values
  -- (-1, -2, high-bit set?), so use fromIntegral instead (probably faster?)


bvExprs :: ( Monad m
           , HaskellTy bvtestexpr ~ Integer
           , IsTestExpr bvtestexpr
           , 1 <= w
           , KnownNat w
           , Integral word
           , Bits word
           , FiniteBits word
           )
        => GenT m TestExpr
        -> (bvtestexpr -> TestExpr)
        -> (TestExpr -> bvtestexpr)
        -> (String -> Integer
            -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w))
            -> bvtestexpr)
        -> (bvtestexpr
            -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w)))
        -> Natural
        -> (HaskellTy bvtestexpr -> word)
        -> [GenT m TestExpr]
bvExprs bvTerm conTE projTE teSubCon expr width toWord =
  let subBVTerms1 gen = Gen.subterm bvTerm (conTE . gen . projTE)
      subBVTerms2 gen = Gen.subterm2 bvTerm bvTerm
                        (\x y -> conTE $ gen (projTE x) (projTE y))
      subBVTerms2nz gen = Gen.subterm2 bvTerm bvTermNZ
                          (\x y -> conTE $ gen (projTE x) (projTE y))
      bvTermNZ = do t <- projTE <$> bvTerm
                    -- adjust 0 to +1 to avoid divide-by-zero.  A
                    -- Gen.filterT tends to lead to non-termination
                    -- here
                    return $ if testval t == 0
                             then conTE $ teSubCon
                                  (pdesc t <> " +1")
                                  (testval t + 1)
                                  (\sym -> do lit1 <- bvLit sym knownRepr 1

                                              orig <- expr t sym
                                              bvAdd sym orig lit1)
                             else conTE t
      mask = (.&.) (2^width - 1)
      uBV v = if v >= 0 then v else 2^width + v
      sBV v = let norm = if v >= 0 then v else mask (v - 2^width)
              in if norm >= (2^(width-1)) then norm - 2^width else norm
      pfx o = "bv" <> show width <> "." <> o
  in
  [
    subBVTerms1
    (\x -> teSubCon (pfx "neg " <> pdesc x)
           (mask ((-1) * testval x))
           (\sym -> bvNeg sym =<< expr x sym))

  , subBVTerms1
    (\x -> teSubCon (pfx "not " <> pdesc x)
           (mask (complement $ testval x))
           (\sym -> bvNotBits sym =<< expr x sym))

  , subBVTerms2
    (\x y -> teSubCon (pdesc x <> " " <> pfx "+ " <> pdesc y)
             (mask (testval x + testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvAdd sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "-", pdesc y])
             (mask (testval x - testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvSub sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "*", pdesc y])
             (mask (testval x * testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvMul sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "u/", pdesc y])
             (mask (uBV (testval x) `quot` uBV (testval y)))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvUdiv sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "urem", pdesc y])
             (mask (uBV (testval x) `rem` uBV (testval y)))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvUrem sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "s/", pdesc y])
             (let x' = sBV $ testval x
                  y' = sBV $ testval y
              in mask (x' `quot` y'))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvSdiv sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "srem", pdesc y])
             (let x' = sBV $ testval x
                  y' = sBV $ testval y
              in mask (x' `rem` y'))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvSrem sym x' y'))

  , Gen.subterm3
    (IGen.filterT isBoolTestExpr genBoolCond)
    bvTerm bvTerm
    (\(TE_Bool c) lt rt -> conTE $
    let l = projTE lt
        r = projTE rt
    in teSubCon
       (unwords [pdesc c, pfx "?", pdesc l, ":", pdesc r])
       (if testval c then testval l else testval r)
       (\sym -> do c' <- predexp c sym
                   l' <- expr l sym
                   r' <- expr r sym
                   bvIte sym c' l' r'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "rol", pdesc y])
             (let x' = toWord $ uBV $ testval x
                  y' = fromEnum $ uBV $ testval y
              in mask (toInteger (x' `rotateL` y')))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvRol sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "ror", pdesc y])
             (let x' = toWord $ uBV $ testval x
                  y' = fromEnum $ uBV $ testval y
              in mask (toInteger (x' `rotateR` y')))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvRor sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "&", pdesc y])
             (mask (testval x .&. testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvAndBits sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "|", pdesc y])
             (mask (testval x .|. testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvOrBits sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "xor", pdesc y])
             (mask (testval x `xor` testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvXorBits sym x' y'))

  , let natTerm = IGen.filterT isNatTestExpr genNatTestExpr
        boolTerm = IGen.filterT isBoolTestExpr genBoolCond
    in
      Gen.subterm3 bvTerm natTerm boolTerm $
      -- see Note [natTerm]
      \bvt (TE_Nat n) (TE_Bool b) ->
        let bv = projTE bvt
            nval = testval n `mod` width
            ival = fromIntegral nval
        in conTE $ teSubCon
           (pdesc bv <> "[" <> show ival <> "]" <> pfx ":=" <> pdesc b)
           (if testval b
            then setBit (testval bv) ival
            else clearBit (testval bv) ival)
           (\sym -> do bv' <- expr bv sym
                       b' <- predexp b sym
                       bvSet sym bv' nval b')

  , let boolTerm = IGen.filterT isBoolTestExpr genBoolCond
    in
      Gen.subterm boolTerm $
      \(TE_Bool b) ->
        -- technically bvFill also takes a NatRepr for the output
        -- width, but due to the arrangement of these expression
        -- generators, it will just generate the size specified for
        -- the current width
        conTE $ teSubCon
        (pfx "=" <> pdesc b <> "..")
        (if testval b then mask (-1) else mask 0)
        (\sym -> bvFill sym knownRepr =<< predexp b sym)

  , subBVTerms1
    (\x -> teSubCon (pfx "bvPopCount " <> pdesc x)
           (fromIntegral $ popCount $ mask $ testval x)
           (\sym -> bvPopcount sym =<< expr x sym))

  , subBVTerms1
    (\x -> teSubCon (pfx "bvCountLeadingZeros " <> pdesc x)
           (fromIntegral $ countLeadingZeros $ toWord $ uBV $ mask $ testval x)
           (\sym -> bvCountLeadingZeros sym =<< expr x sym))

  , subBVTerms1
    (\x -> teSubCon (pfx "bvCountTrailingZeros " <> pdesc x)
           (fromIntegral $ countTrailingZeros $ toWord $ uBV $ mask $ testval x)
           (\sym -> bvCountTrailingZeros sym =<< expr x sym))

  -- TBD: carrylessMultiply

  ] ++
  if width <= 16
  then
    [
      -- Currently, shifts must be handled very carefully.  The
      -- underlying datatype for a BV is Integer, which is not
      -- Bounded, and the shift amount is the same BV size as the
      -- shifted source.  Shifting a 64-bit value left by something
      -- between 32 and 64-bits requires a very large Haskell
      -- allocation for storing those huge integers.
      --
      -- Properly, the shift source should return 0 (or -1) if the
      -- shift amount is greater than the current BV size, but this is
      -- not currently implemented.  For the time being, the
      -- constraint above limits these tests to be run for shift sizes
      -- that are supportable within a couple of GB of system memory.
      --
      -- Observed results:
      --
      --   8bit & 16bit BV : test time < 8 sec, tests pass
      --   32-bit BV : memory utilization goes up to ~4-5GB
      --               and tests take 90+ seconds (but pass)
      --   64-bit BV : tests *fail* in 9-25 sec with either
      --               "Unable to commit 136366260224 bytes of memory" or
      --               "Exception: heap overflow"

      subBVTerms2
      (\x y -> teSubCon (unwords [pdesc x, pfx "<<", pdesc y])
               (mask (testval x `shiftL` (fromEnum $ uBV $ testval y)))
               (\sym -> do x' <- expr x sym
                           y' <- expr y sym
                           bvShl sym x' y'))

    , subBVTerms2
      (\x y -> teSubCon (unwords [pdesc x, pfx "lsr", pdesc y])
               (let s = fromEnum $ uBV $ testval y
                in mask (uBV (testval x) `shiftR` s))
               (\sym -> do x' <- expr x sym
                           y' <- expr y sym
                           bvLshr sym x' y'))

    , subBVTerms2
      (\x y -> teSubCon (unwords [pdesc x, pfx "asr", pdesc y])
               (let s = fromEnum $ sBV $ testval y
                in mask (if s >= 0
                          then sBV (testval x) `shiftR` s
                          else testval x `shiftL` (-s)))
               (\sym -> do x' <- expr x sym
                           y' <- expr y sym
                           bvAshr sym x' y'))

    ]
    else []

-- TBD: BV operations returning a (Pred,BV) pair will need another TestExpr
-- representation: addUnsignedOF, addSignedOF, subUnsignedOF,
-- subSignedOF, mulUnsignedOF, mulSignedOF

-- TBD: BV operations returning a (BV,BV) pair will need another
-- TestExpr representation: unsignedWideMultiplyBV, signedWideMultiplyBV

-- TBD: struct operations
-- TBD: array operations
-- TBD: Lossless conversions
-- TBD: Lossless combinators
-- TBD: Lossy conversions
-- TBD: Lossy (non-injective) combinators
-- TBD: Bitvector operations (intSetWidth, uintSetWidth, intToUInt)
-- TBD: string operations
-- TBD: real operations
-- TBD: IEEE-754 floating-point operations
-- TBD: Cplx operations
-- TBD: misc functions in Interface.hs
