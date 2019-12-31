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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module What4.Expr.StringSeq
( StringSeq
, StringSeqEntry(..)
, singleton
, append
, stringSeqAbs
, toList
, traverseStringSeq
) where

import           Data.Kind
import qualified Data.Foldable as F

import qualified Data.FingerTree as FT

import           Data.Parameterized.Classes

import           What4.BaseTypes
import           What4.Interface
import           What4.Utils.AbstractDomains
import           What4.Utils.IncrHash

-- | Annotation value for string sequences.
--   First value is the XOR hash of the sequence
--   Second value is the string abstract domain.
data StringSeqNote = StringSeqNote !IncrHash !StringAbstractValue

instance Semigroup StringSeqNote where
  StringSeqNote xh xabs <> StringSeqNote yh yabs =
    StringSeqNote (xh <> yh) (stringAbsConcat xabs yabs)

instance Monoid StringSeqNote where
  mempty = StringSeqNote mempty stringAbsEmpty
  mappend = (<>)

data StringSeqEntry e si
  = StringSeqLiteral !(StringLiteral si)
  | StringSeqTerm !(e (BaseStringType si))

instance (HasAbsValue e, HashableF e) => FT.Measured StringSeqNote (StringSeqEntry e si) where
  measure (StringSeqLiteral l) = StringSeqNote (toIncrHashWithSalt 1 l) (stringAbsSingle l)
  measure (StringSeqTerm e) = StringSeqNote (mkIncrHash (hashWithSaltF 2 e)) (getAbsValue e)

type StringFT e si = FT.FingerTree StringSeqNote (StringSeqEntry e si)

sft_hash :: (HashableF e, HasAbsValue e) => StringFT e si -> IncrHash
sft_hash ft =
  case FT.measure ft of
    StringSeqNote h _abs -> h

ft_eqBy :: FT.Measured v a => (a -> a -> Bool) -> FT.FingerTree v a -> FT.FingerTree v a -> Bool
ft_eqBy eq xs0 ys0 = go (FT.viewl xs0) (FT.viewl ys0)
 where
 go FT.EmptyL FT.EmptyL = True
 go (x FT.:< xs) (y FT.:< ys) = eq x y && go (FT.viewl xs) (FT.viewl ys)
 go _ _ = False

data StringSeq
  (e  :: BaseType -> Type)
  (si :: StringInfo) =
  StringSeq
  { _stringSeqRepr :: StringInfoRepr si
  , stringSeq :: FT.FingerTree StringSeqNote (StringSeqEntry e si)
  }

instance (TestEquality e, HasAbsValue e, HashableF e) => TestEquality (StringSeq e) where
  testEquality (StringSeq xi xs) (StringSeq yi ys)
    | Just Refl <- testEquality xi yi
    , sft_hash xs == sft_hash ys

    = let f (StringSeqLiteral a) (StringSeqLiteral b) = a == b
          f (StringSeqTerm a) (StringSeqTerm b) = isJust (testEquality a b)
          f _ _ = False

       in if ft_eqBy f xs ys then Just Refl else Nothing

  testEquality _ _ = Nothing

instance (TestEquality e, HasAbsValue e, HashableF e) => Eq (StringSeq e si) where
  x == y = isJust (testEquality x y)

instance (HasAbsValue e, HashableF e) => HashableF (StringSeq e) where
  hashWithSaltF s (StringSeq _si xs) = hashWithSalt s (sft_hash xs)

instance (HasAbsValue e, HashableF e) => Hashable (StringSeq e si) where
  hashWithSalt = hashWithSaltF

singleton :: (HasAbsValue e, HashableF e, IsExpr e) => StringInfoRepr si -> e (BaseStringType si) -> StringSeq e si
singleton si x
  | Just l <- asString x = StringSeq si (FT.singleton (StringSeqLiteral l))
  | otherwise            = StringSeq si (FT.singleton (StringSeqTerm x))

append :: (HasAbsValue e, HashableF e) => StringSeq e si -> StringSeq e si -> StringSeq e si
append (StringSeq si xs) (StringSeq _ ys) =
  case (FT.viewr xs, FT.viewl ys) of
    (xs' FT.:> StringSeqLiteral xlit, StringSeqLiteral ylit FT.:< ys')
      -> StringSeq si (xs' <> (StringSeqLiteral (xlit <> ylit) FT.<| ys'))

    _ -> StringSeq si (xs <> ys)

stringSeqAbs :: (HasAbsValue e, HashableF e) => StringSeq e si -> StringAbstractValue
stringSeqAbs (StringSeq _ xs) =
  case FT.measure xs of
    StringSeqNote _ a -> a

toList :: StringSeq e si -> [StringSeqEntry e si]
toList = F.toList . stringSeq

traverseStringSeq :: (HasAbsValue f, HashableF f, Applicative m) =>
  (forall x. e x -> m (f x)) ->
  StringSeq e si -> m (StringSeq f si)
traverseStringSeq f (StringSeq si xs) =
  StringSeq si <$> F.foldl' (\m x -> (FT.|>) <$> m <*> g x) (pure FT.empty) xs
 where
 g (StringSeqLiteral l) = pure (StringSeqLiteral l)
 g (StringSeqTerm x) = StringSeqTerm <$> f x
