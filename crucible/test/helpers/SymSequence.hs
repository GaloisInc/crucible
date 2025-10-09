{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module SymSequence (tests) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable qualified as F
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Parameterized.Nonce qualified as Nonce
import Data.Parameterized.Some (Some(Some))
import Hedgehog (Gen)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Lang.Crucible.Backend (SomeBackend(SomeBackend), backendGetSym)
import Lang.Crucible.Backend.Simple (newSimpleBackend)
import Lang.Crucible.Simulator.SymSequence (SymSequence)
import Lang.Crucible.Simulator.SymSequence qualified as S
import Test.Tasty qualified as TT
import Test.Tasty.Hedgehog qualified as TTH
import Test.Tasty.HUnit qualified as TTHU
import What4.Expr (EmptyExprBuilderState(EmptyExprBuilderState))
import What4.Expr.Builder (newExprBuilder)
import What4.FloatMode (FloatModeRepr(FloatIEEERepr))
import What4.Interface qualified as WI
import What4.Partial qualified as WP

---------------------------------------------------------------------
-- Tests

tests :: TT.TestTree
tests =
  TT.testGroup "SymSequence"
  [ TTH.testProperty "propSame" propSame
  -- TODO: reflexivity, symmetry, transitivity of equality
  , TTH.testProperty "propSameEq"
      (H.withTests 4096 (H.withShrinks 4096 propSameEq))

  -- Concrete test cases that have failed in the past
  , TTHU.testCase "concrete test 1" $ do
      let false = OElem False
      testCase $
        OEq
        (OAppend (OAppend ONil ONil) (OCons false ONil))
        (OAppend (OCons false ONil) ONil)
  , TTHU.testCase "concrete test 2" $ do
      testCase (OEq (OAppend ONil ONil) ONil)
  ]
  where
    testCase :: Op Bool Bool -> TTHU.Assertion
    testCase op = do
      Some (SomeBackend bak) <- mkBackend
      let sym = backendGetSym bak
      let l = opList op
      r <- liftIO (opSeq sym op)
      l TTHU.@=? r

propSame :: H.Property
propSame =
  H.property $ do
    Some (SomeBackend bak) <- liftIO mkBackend
    let sym = backendGetSym bak
    op <- H.forAll (genList Gen.bool)
    let l = opList op
    s <- liftIO (opSeq sym op)
    l' <- liftIO (F.toList <$> asSeq sym s)
    l H.=== l'
  where
    asSeq sym =
      S.concretizeSymSequence (pure . asConstPred (Just sym)) pure

propSameEq :: H.Property
propSameEq =
  H.property $ do
    Some (SomeBackend bak) <- liftIO mkBackend
    let sym = backendGetSym bak
    op <- H.forAll (genEq Gen.bool)
    -- For debugging nontermination:
    -- liftIO (putStrLn "~~~~~~~~~~~~~~~~~")
    -- liftIO (print op)
    let l = opList op
    r <- liftIO (opSeq sym op)
    l H.=== r

---------------------------------------------------------------------
-- Helpers

mkBackend :: IO (Some SomeBackend)
mkBackend = do
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState Nonce.globalNonceGenerator
  Some . SomeBackend <$> newSimpleBackend sym

asConstPred ::
  WI.IsExprBuilder sym =>
  proxy sym ->
  WI.Pred sym ->
  Bool
asConstPred _proxy p =
  case WI.asConstantPred p of
    Just True -> True
    Just False -> False
    Nothing -> error "non-constant predicate?"

---------------------------------------------------------------------
-- Op

data Elem a deriving Show

data List a deriving Show

-- TODO: Replace with `Seq` for performance
type family AsList t where
  AsList (List a) = [a]
  AsList (Elem a) = a
  AsList (Maybe a) = Maybe (AsList a)
  AsList (a, b) = (AsList a, AsList b)
  AsList a = a

type family AsSeq sym t where
  AsSeq sym (List a) = SymSequence sym a
  AsSeq sym (Elem a) = a
  AsSeq sym (Maybe a) = Maybe (AsSeq sym a)
  AsSeq sym (a, b) = (AsSeq sym a, AsSeq sym b)
  AsSeq sym a = a

-- | An interaction with the 'SymSequence' API
data Op a t where
  -- Generic functions
  OTrue :: Op a Bool
  OFalse :: Op a Bool
  OFst :: Op a (l, r) -> Op a l
  OSnd :: Op a (l, r) -> Op a r
  OElem:: a -> Op a (Elem a)
  OFromMaybe :: Op a t -> Op a (Maybe t) -> Op a t

  -- Constructors
  ONil :: Op a (List a)
  OCons :: Op a (Elem a) -> Op a (List a) -> Op a (List a)
  OAppend :: Op a (List a) -> Op a (List a) -> Op a (List a)
  OMux :: Op a Bool -> Op a (List a) -> Op a (List a) -> Op a (List a)

  -- Operations
  OUncons :: Op a (List a) -> Op a (Maybe (Elem a), (List a))
  OLength :: Op a (List a) -> Op a Integer
  OEq :: Op a (List a) -> Op a (List a) -> Op a Bool
  -- TODO: length actually can't be generated from genList
  -- bc there is no consumer for its return type

  -- TODO: isNil, head, tail

sexp :: [String] -> String
sexp s = '(' : (unwords s ++ ")")

fun :: String -> [String] -> String
fun f s = sexp (f:s)

fun1 :: Show a => String -> a -> String
fun1 f a = fun f [show a]

fun2 :: (Show a, Show b) => String -> a -> b -> String
fun2 f a b = fun f [show a, show b]

fun3 :: (Show a, Show b, Show c) => String -> a -> b -> c -> String
fun3 f a b c = fun f [show a, show b, show c]

instance Show a => Show (Op a t) where
  show =
    \case
      -- Generic functions
      OTrue -> "true"
      OFalse -> "false"
      OFst t -> fun1 "fst" t
      OSnd t -> fun1 "snd" t
      OElem a -> show a
      OFromMaybe a m -> fun2 "fromMaybe" a m

      -- Constructors
      ONil -> "nil"
      OCons l r -> fun2 "cons" l r
      OAppend l r -> fun2 "append" l r
      OMux b l r -> fun3 "mux" b l r

      -- Operations
      OUncons l -> fun1 "uncons" l
      OLength l -> fun1 "length" l
      OEq l r -> fun2 "eq" l r

---------------------------------------------------------------------
-- Generating Op

genBoolLit :: Gen (Op a Bool)
genBoolLit = Gen.choice [pure OTrue , pure OFalse]

genBool :: Gen a -> Gen (Op a Bool)
genBool genA =
  Gen.recursive
    Gen.choice
    [genBoolLit]
    [genEq genA]

genElem :: Gen a -> Gen (Op a (Elem a))
genElem genA =
  Gen.recursive
    Gen.choice
    [OElem <$> genA]
    [ OFromMaybe
      <$> genElem genA
      <*> (OFst <$> (OUncons <$> genList genA))
    ]

genList :: Gen a -> Gen (Op a (List a))
genList genA =
  Gen.recursive
    Gen.choice
    [pure ONil]
    [ genCons
    , genAppend
    , genMux
    ]
  where
    sub1 = genList genA
    sub2 = (,) <$> genList genA <*> genList genA

    genCons = OCons <$> genElem genA <*> sub1

    genAppend = uncurry OAppend <$> sub2

    genMux = do
      b <- genBool genA
      uncurry (OMux b) <$> sub2

genEq :: Gen a -> Gen (Op a Bool)
genEq genA = OEq <$> genList genA <*> genList genA

---------------------------------------------------------------------
-- Interpreting Op

opList :: Eq a => Op a t -> AsList t
opList =
  \case
    -- Generic functions
    OTrue -> True
    OFalse -> False
    OFst t -> fst (opList t)
    OSnd t -> snd (opList t)
    OElem a -> a
    OFromMaybe a m -> Maybe.fromMaybe (opList a) (opList m)

    -- Constructors
    ONil -> []
    OCons a l -> opList a : opList l
    OAppend l r -> opList l ++ opList r
    OMux b l r -> if opList b then opList l else opList r

    -- Operations
    OUncons l ->
      let l' = opList l in
      case List.uncons l' of
        Just (hd, tl) -> (Just hd, tl)
        Nothing -> (Nothing, l')
    OLength l -> fromIntegral @Int @Integer (length (opList l))  -- safe
    OEq l r -> opList l == opList r

opSeq ::
  WI.IsExprBuilder sym =>
  Eq a =>
  sym ->
  Op a t ->
  IO (AsSeq sym t)
opSeq sym =
  \case
    -- Generic functions
    OTrue -> pure True
    OFalse -> pure False
    OFst t -> fst <$> opSeq sym t
    OSnd t -> snd <$> opSeq sym t
    OElem a -> pure a
    OFromMaybe a m ->
      Maybe.fromMaybe
      <$> opSeq sym a
      <*> opSeq sym m

    -- Constructors
    ONil -> pure S.SymSequenceNil
    OCons a l ->
      S.SymSequenceCons
      <$> Nonce.freshNonce Nonce.globalNonceGenerator
      <*> opSeq sym a
      <*> opSeq sym l
    OAppend l r ->
      S.SymSequenceAppend
      <$> Nonce.freshNonce Nonce.globalNonceGenerator
      <*> opSeq sym l
      <*> opSeq sym r
    OMux b l r -> do
      b' <- opSeq sym b
      let b'' = if b' then WI.truePred sym else WI.falsePred sym
      S.SymSequenceMerge
        <$> Nonce.freshNonce Nonce.globalNonceGenerator
        <*> pure b''
        <*> opSeq sym l
        <*> opSeq sym r

    -- Constructors
    OUncons l -> do
      l' <- opSeq sym l
      let interpPred p x y =
            if asConstPred (Just sym) p
            then pure x
            else pure y
      pe <- S.unconsSymSequence sym interpPred l'
      case pe of
        WP.Unassigned -> pure (Nothing, l')
        WP.PE _ (hd, tl) -> -- TODO: assert pred is truePred
          pure (Just hd, tl)
    OLength s -> do
      l <- S.lengthSymSequence sym =<< opSeq sym s
      case WI.asInteger (WI.natToIntegerPure l) of
        Just l' -> pure l'
        Nothing -> error "SymSequence: symbolic length"
    OEq l r -> do
      let predEq x y =
            pure (if x == y then WI.truePred sym else WI.falsePred sym)
      let mux b x y = pure (if asConstPred (Just sym) b then x else y)
      l' <- opSeq sym l
      r' <- opSeq sym r
      p <- S.eqSymSequence sym predEq mux l' r'
      pure (asConstPred (Just sym) p)
