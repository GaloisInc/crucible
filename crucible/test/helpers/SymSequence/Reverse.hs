{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}

module SymSequence.Reverse (tests) where

import Data.Parameterized.Nonce qualified as Nonce
import Data.Parameterized.Some (Some(Some))
import Lang.Crucible.Backend (SomeBackend(SomeBackend), backendGetSym)
import Lang.Crucible.Backend.Simple (newSimpleBackend)
import Lang.Crucible.Simulator.SymSequence (SymSequence)
import Lang.Crucible.Simulator.SymSequence qualified as S
import System.Timeout (timeout)
import Test.Tasty qualified as TT
import Test.Tasty.HUnit qualified as TTU
import What4.Expr (EmptyExprBuilderState(EmptyExprBuilderState))
import What4.Expr.Builder (newExprBuilder)
import What4.FloatMode (FloatModeRepr(FloatIEEERepr))
import What4.Interface qualified as WI

---------------------------------------------------------------------
-- Tests

tests :: TT.TestTree
tests = TT.testGroup "reverse performance"

  -- Pure cons-list (no branching, no appends):
  --
  --   Cons -> Cons -> ... -> Cons -> Nil
  --
  [ reverseTest "reverse large cons-list" $ \sym ->
      buildSeq sym 1500000 $ \s _ acc ->
        S.consSymSequence s True acc

  -- Cons-list with a Mux node every 100 elements.
  -- At each Mux both branches point to the same shared tail:
  --
  --                                 /--true---\
  --   Cons -> ... -> Cons -> Mux ->            Cons -> ... -> Nil
  --                                 \--false--/
  --
  , reverseTest "reverse cons-list with periodic muxes" $ \sym ->
      buildSeq sym 250000 $ \s i acc -> do
        acc' <-
          if i `mod` 100 == 0
          then do
            t <- S.consSymSequence s True acc
            f <- S.consSymSequence s False acc
            S.muxSymSequence s (WI.truePred s) t f
          else pure acc
        S.consSymSequence s True acc'

  -- Left-nested chain of Appends:
  --
  --   Append -> Append -> ... -> Append -> Nil
  --
  , reverseTest "reverse left-nested appends" $ \sym ->
      buildSeq sym 250000 $ \s _ acc -> do
        singleton <- S.consSymSequence s True S.SymSequenceNil
        S.appendSymSequence s acc singleton

  -- Right-nested chain of Appends:
  --
  --   Append -> Append -> ... -> Append -> Nil
  --
  , reverseTest "reverse right-nested appends" $ \sym ->
      buildSeq sym 250000 $ \s _ acc -> do
        singleton <- S.consSymSequence s True S.SymSequenceNil
        S.appendSymSequence s singleton acc

  -- Left-deep chain of Muxes (true branch grows):
  --
  --   Mux -> Mux -> Mux -> ... -> Mux -> Nil
  --
  , reverseTest "reverse left-deep mux chain" $ \sym ->
      buildSeq sym 250000 $ \s _ acc -> do
        singleton <- S.consSymSequence s True S.SymSequenceNil
        S.muxSymSequence s (WI.truePred s) acc singleton

  -- Right-deep chain of Muxes (true branch is a leaf):
  --
  --   Mux -> Mux -> Mux -> ... -> Mux -> Nil
  --
  , reverseTest "reverse right-deep mux chain" $ \sym ->
      buildSeq sym 250000 $ \s _ acc -> do
        singleton <- S.consSymSequence s True S.SymSequenceNil
        S.muxSymSequence s (WI.truePred s) singleton acc

  -- Balanced binary tree of Appends over singletons:
  --
  --            Append
  --           /      \
  --       Append    Append
  --       /    \    /    \
  --     [1]  [2]  [3]  [4] ...
  --
  , reverseTest "reverse balanced appends" $ \sym ->
      buildBalanced sym 250000 $ \s acc1 acc2 ->
        S.appendSymSequence s acc1 acc2

  -- Balanced binary tree of Muxes over singletons:
  --
  --            Mux
  --           /   \
  --        Mux    Mux
  --       /   \  /   \
  --     [1] [2] [3] [4] ...
  --
  , reverseTest "reverse balanced muxes" $ \sym ->
      buildBalanced sym 250000 $ \s acc1 acc2 ->
        S.muxSymSequence s (WI.truePred s) acc1 acc2
  ]

---------------------------------------------------------------------
-- Helpers

mkBackend :: IO (Some SomeBackend)
mkBackend = do
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState Nonce.globalNonceGenerator
  Some . SomeBackend <$> newSimpleBackend sym

-- | Build a sequence, reverse it, and check that length is preserved.
--   Must complete within 5 seconds.
reverseTest ::
  String ->
  (forall sym. WI.IsExprBuilder sym => sym -> IO (SymSequence sym Bool)) ->
  TT.TestTree
reverseTest name build = TTU.testCase name $ do
  Some (SomeBackend bak) <- mkBackend
  let sym = backendGetSym bak
  s <- build sym
  origLen <- S.lengthSymSequence sym s
  result <- timeout (5 * 1000000) $ do
    r <- S.reverseSymSequence sym s
    S.lengthSymSequence sym r
  case result of
    Nothing -> TTU.assertFailure (name ++ " timed out (>5s)")
    Just revLen ->
      TTU.assertEqual "length preserved"
        (WI.asInteger (WI.natToIntegerPure origLen))
        (WI.asInteger (WI.natToIntegerPure revLen))

-- | Iterate a step function n times starting from nil.
buildSeq ::
  WI.IsExprBuilder sym =>
  sym ->
  Int ->
  (sym -> Int -> SymSequence sym Bool -> IO (SymSequence sym Bool)) ->
  IO (SymSequence sym Bool)
buildSeq sym n step = go n S.SymSequenceNil
  where
    go 0 acc = pure acc
    go i acc = go (i - 1) =<< step sym i acc

-- | Build a balanced binary tree of n singletons combined with the given
--   binary operation (e.g. appendSymSequence or muxSymSequence).
buildBalanced ::
  WI.IsExprBuilder sym =>
  sym ->
  Int ->
  (sym -> SymSequence sym Bool -> SymSequence sym Bool -> IO (SymSequence sym Bool)) ->
  IO (SymSequence sym Bool)
buildBalanced sym n combine = do
  leaves <- mapM (\_ -> S.consSymSequence sym True S.SymSequenceNil) [1..n]
  reduce leaves
  where
    reduce [] = pure S.SymSequenceNil
    reduce [x] = pure x
    reduce xs = reduce =<< pairUp xs
    pairUp [] = pure []
    pairUp [x] = pure [x]
    pairUp (x:y:rest) = do
      combined <- combine sym x y
      (combined :) <$> pairUp rest
