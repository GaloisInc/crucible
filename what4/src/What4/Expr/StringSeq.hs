{-|
Module      : What4.Expr.StringSeq
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : rdockins@galois.com

A simple datatype for collecting sequences of strings
that are to be concatenated together.

We intend to maintain several invariants. First, that
no sequence is empty; the empty string literal should
instead be the unique representative of empty strings.
Second, that string sequences do not contain adjacent
literals.  In other words, adjacent string literals
are coalesced.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module What4.Expr.StringSeq
( StringSeq
, singleton
, append
, toList
, traverseStringSeq
) where

import           Data.Kind
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F

import           Data.Parameterized.Classes
import           Data.Parameterized.TraversableFC

import           What4.BaseTypes
import           What4.Interface

data StringSeq
  (e  :: BaseType -> Type)
  (si :: StringInfo) =
  StringSeq
  { _stringSeqRepr :: StringInfoRepr si
  , stringSeq :: Seq.Seq (Either (StringLiteral si) (e (BaseStringType si)))
  }

instance TestEqualityFC StringSeq where
  testEqualityFC test (StringSeq xi xs) (StringSeq yi ys)
    | Just Refl <- testEquality xi yi
    , Seq.length xs == Seq.length ys
    = let f (Left a) (Left b)  = a == b
          f (Right a) (Right b) = isJust (test a b)
          f _ _ = False

          eq = F.and (Seq.zipWith f xs ys)

       in if eq then Just Refl else Nothing

  testEqualityFC _ _ _ = Nothing

instance TestEquality e => TestEquality (StringSeq e) where
  testEquality = testEqualityFC testEquality

instance TestEquality e => Eq (StringSeq e si) where
  x == y = isJust (testEquality x y)

instance HashableF e => HashableF (StringSeq e) where
  hashWithSaltF s0 (StringSeq si xs) =
    F.foldl (\s x -> either (hashWithSaltF s) (hashWithSaltF s) x) (hashWithSaltF s0 si) xs

instance HashableF e => Hashable (StringSeq e si) where
  hashWithSalt = hashWithSaltF

singleton :: IsExpr e => StringInfoRepr si -> e (BaseStringType si) -> StringSeq e si
singleton si x
  | Just l <- asString x = StringSeq si (Seq.singleton (Left l))
  | otherwise = StringSeq si (Seq.singleton (Right x))

append :: StringSeq e si -> StringSeq e si -> StringSeq e si
append (StringSeq si xs) (StringSeq _ ys) =
  case (Seq.viewr xs, Seq.viewl ys) of
    (xs' Seq.:> Left xlit, Left ylit Seq.:< ys')
      -> StringSeq si (xs' <> (Left (xlit <> ylit) Seq.<| ys'))

    _ -> StringSeq si (xs <> ys)

toList :: StringSeq e si -> [Either (StringLiteral si) (e (BaseStringType si))]
toList = F.toList . stringSeq

traverseStringSeq :: Applicative m =>
  (forall x. e x -> m (f x)) ->
  StringSeq e si -> m (StringSeq f si)
traverseStringSeq f (StringSeq si xs) =
  StringSeq si <$> traverse (either (pure . Left) (\x -> Right <$> f x)) xs
