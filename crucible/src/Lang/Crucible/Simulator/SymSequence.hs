{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Simulator.SymSequence
( SymSequence(..)
, nilSymSequence
, consSymSequence
, appendSymSequence
, muxSymSequence
, isNilSymSequence
, lengthSymSequence
, headSymSequence
, tailSymSequence
, unconsSymSequence
, concreteizeSymSequence
) where

import           Data.Functor.Const
import           Data.Kind (Type)
import           Data.IORef
import           Data.Maybe (isJust)
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Map as MapF

import           Lang.Crucible.Types
import           What4.Interface
import           What4.Partial

------------------------------------------------------------------------
-- SymSequence

-- | A symbolic sequence of values supporting efficent merge operations.
--   Semantically, these are essentially cons-lists, and designed to
--   support access from the front only.  Nodes carry nonce values
--   that allow DAG-based traversal, which efficently supports the common
--   case where merged nodes share a common sublist.
data SymSequence sym a where
  SymSequenceNil :: SymSequence sym a

  SymSequenceCons ::
    !(Nonce GlobalNonceGenerator a) ->
    a ->
    !(SymSequence sym a) ->
    SymSequence sym a

  SymSequenceAppend ::
    !(Nonce GlobalNonceGenerator a) ->
    !(SymSequence sym a) ->
    !(SymSequence sym a) ->
    SymSequence sym a

  SymSequenceMerge ::
    !(Nonce GlobalNonceGenerator a) ->
    !(Pred sym) ->
    !(SymSequence sym a) ->
    !(SymSequence sym a) ->
    SymSequence sym a

instance Eq (SymSequence sym a) where
  SymSequenceNil == SymSequenceNil = True
  (SymSequenceCons n1 _ _) == (SymSequenceCons n2 _ _) =
    isJust (testEquality n1 n2)
  (SymSequenceMerge n1 _ _ _) == (SymSequenceMerge n2 _ _ _) =
    isJust (testEquality n1 n2)
  (SymSequenceAppend n1 _ _) == (SymSequenceAppend n2 _ _) =
    isJust (testEquality n1 n2)
  _ == _ = False

-- | Compute an if/then/else on symbolic sequences.
--   This will simply produce an internal merge node
--   except in the special case where the then and
--   else branches are sytactically identical.
muxSymSequence :: IsExprBuilder sym =>
  sym ->
  Pred sym ->
  SymSequence sym a ->
  SymSequence sym a ->
  IO (SymSequence sym a)
muxSymSequence _sym p x y
  | x == y = pure x
  | otherwise =
      do n <- freshNonce globalNonceGenerator
         pure (SymSequenceMerge n p x y)

newtype SeqCache (f :: Type -> Type)
  = SeqCache (IORef (MapF.MapF (Nonce GlobalNonceGenerator) f))

newSeqCache :: IO (SeqCache f)
newSeqCache = SeqCache <$> newIORef MapF.empty

-- | Compute the nonce of a sequence, if it has one
symSequenceNonce :: SymSequence sym a -> Maybe (Nonce GlobalNonceGenerator a)
symSequenceNonce SymSequenceNil = Nothing
symSequenceNonce (SymSequenceCons n _ _ ) = Just n
symSequenceNonce (SymSequenceAppend n _ _) = Just n
symSequenceNonce (SymSequenceMerge n _ _ _) = Just n

evalWithFreshCache ::
  ((SymSequence sym a -> IO (f a)) -> SymSequence sym a -> IO (f a)) ->
  (SymSequence sym a -> IO (f a))
evalWithFreshCache fn s =
  do c <- newSeqCache
     evalWithCache c fn s

evalWithCache ::
  SeqCache f ->
  ((SymSequence sym a -> IO (f a)) -> SymSequence sym a -> IO (f a)) ->
  (SymSequence sym a -> IO (f a))
evalWithCache (SeqCache ref) fn = loop
  where
    loop s
      | Just n <- symSequenceNonce s =
          (MapF.lookup n <$> readIORef ref) >>= \case
            Just v -> pure v
            Nothing ->
              do v <- fn loop s
                 modifyIORef ref (MapF.insert n v)
                 pure v

      | otherwise = fn loop s

-- | Generate an empty sequence value
nilSymSequence :: sym -> IO (SymSequence sym a)
nilSymSequence _sym = pure SymSequenceNil

-- | Cons a new value onto the front of a sequence
consSymSequence ::
  sym ->
  a ->
  SymSequence sym a ->
  IO (SymSequence sym a)
consSymSequence _sym x xs =
  do n <- freshNonce globalNonceGenerator
     pure (SymSequenceCons n x xs)

-- | Append two sequences
appendSymSequence ::
  sym ->
  SymSequence sym a {- ^ front sequence -} ->
  SymSequence sym a {- ^ back sequence -} ->
  IO (SymSequence sym a)

-- special cases, nil is the unit for append
appendSymSequence _ xs SymSequenceNil = pure xs
appendSymSequence _ SymSequenceNil ys = pure ys
-- special case, append of a singleton is cons
appendSymSequence sym (SymSequenceCons _ v SymSequenceNil) xs =
  consSymSequence sym v xs
appendSymSequence _sym xs ys =
  do n <- freshNonce globalNonceGenerator
     pure (SymSequenceAppend n xs ys)


-- | Test if a sequence is nil (is empty)
isNilSymSequence :: forall sym a.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  IO (Pred sym)
isNilSymSequence sym = \s -> getConst <$> evalWithFreshCache f s
  where
   f :: (SymSequence sym tp -> IO (Const (Pred sym) tp)) -> (SymSequence sym tp -> IO (Const (Pred sym) tp))
   f _loop SymSequenceNil{}  = pure (Const (truePred sym))
   f _loop SymSequenceCons{} = pure (Const (falsePred sym))
   f loop (SymSequenceAppend _ xs ys) =
     do px <- getConst <$> loop xs
        Const <$> itePredM sym px (getConst <$> loop ys) (pure (falsePred sym))
   f loop (SymSequenceMerge _ p xs ys) =
     Const <$> itePredM sym p (getConst <$> loop xs) (getConst <$> loop ys)


-- | Compute the length of a sequence
lengthSymSequence :: forall sym a.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  IO (SymNat sym)
lengthSymSequence sym = \s -> getConst <$> evalWithFreshCache f s
  where
   f :: (SymSequence sym a -> IO (Const (SymNat sym) a)) -> (SymSequence sym a -> IO (Const (SymNat sym) a))
   f _loop SymSequenceNil = Const <$> natLit sym 0
   f loop (SymSequenceCons _ _ tl) =
     do x <- getConst <$> loop tl
        one <- natLit sym 1
        Const <$> natAdd sym one x
   f loop (SymSequenceMerge _ p xs ys) =
     do x <- getConst <$> loop xs
        y <- getConst <$> loop ys
        Const <$> natIte sym p x y
   f loop (SymSequenceAppend _ xs ys) =
     do x <- getConst <$> loop xs
        y <- getConst <$> loop ys
        Const <$> natAdd sym x y


newtype SeqHead sym a = SeqHead { getSeqHead :: PartExpr (Pred sym) a }

-- | Compute the head of a sequence, if it has one
headSymSequence :: forall sym a.
  IsExprBuilder sym =>
  sym ->
  (Pred sym -> a -> a -> IO a) {- ^ mux function on values -} ->
  SymSequence sym a ->
  IO (PartExpr (Pred sym) a)
headSymSequence sym mux = \s -> getSeqHead <$> evalWithFreshCache f s
  where
   f' :: Pred sym -> a -> a -> PartialT sym IO a
   f' c x y = PartialT (\_ p -> PE p <$> mux c x y)

   f :: (SymSequence sym a -> IO (SeqHead sym a)) -> (SymSequence sym a -> IO (SeqHead sym a))
   f _loop SymSequenceNil = pure (SeqHead Unassigned)
   f _loop (SymSequenceCons _ v _) = pure (SeqHead (justPartExpr sym v))
   f loop (SymSequenceMerge _ p xs ys) =
     do mhx <- getSeqHead <$> loop xs
        mhy <- getSeqHead <$> loop ys
        SeqHead <$> mergePartial sym f' p mhx mhy

   f loop (SymSequenceAppend _ xs ys) =
     loop xs >>= \case
       SeqHead Unassigned -> loop ys
       SeqHead (PE px hx)
         | Just True <- asConstantPred px -> pure (SeqHead (PE px hx))
         | otherwise ->
             loop ys >>= \case
               SeqHead Unassigned -> pure (SeqHead (PE px hx))
               SeqHead (PE py hy) ->
                 do p <- orPred sym px py
                    SeqHead <$> runPartialT sym p (f' px hx hy)

newtype SeqUncons sym a =
  SeqUncons
  { getSeqUncons :: PartExpr (Pred sym) (a, SymSequence sym a)
  }

-- | Compute both the head and the tail of a sequence, if it is nonempty
unconsSymSequence :: forall sym a.
  IsExprBuilder sym =>
  sym ->
  (Pred sym -> a -> a -> IO a) {- ^ mux function on values -} ->
  SymSequence sym a ->
  IO (PartExpr (Pred sym) (a, SymSequence sym a))
unconsSymSequence sym mux = \s -> getSeqUncons <$> evalWithFreshCache f s
  where
   f' :: Pred sym ->
         (a, SymSequence sym a) ->
         (a, SymSequence sym a) ->
         PartialT sym IO (a, SymSequence sym a)
   f' c x y = PartialT $ \_ p -> PE p <$>
                    do h  <- mux c (fst x) (fst y)
                       tl <- muxSymSequence sym c (snd x) (snd y)
                       pure (h, tl)

   f :: (SymSequence sym a -> IO (SeqUncons sym a)) -> (SymSequence sym a -> IO (SeqUncons sym a))
   f _loop SymSequenceNil = pure (SeqUncons Unassigned)
   f _loop (SymSequenceCons _ v tl) = pure (SeqUncons (justPartExpr sym (v, tl)))
   f loop (SymSequenceMerge _ p xs ys) =
     do ux <- getSeqUncons <$> loop xs
        uy <- getSeqUncons <$> loop ys
        SeqUncons <$> mergePartial sym f' p ux uy

   f loop (SymSequenceAppend _ xs ys) =
     loop xs >>= \case
       SeqUncons Unassigned -> loop ys
       SeqUncons (PE px ux)
         | Just True <- asConstantPred px ->
             do t <- appendSymSequence sym (snd ux) ys
                pure (SeqUncons (PE px (fst ux, t)))

         | otherwise ->
             loop ys >>= \case
               SeqUncons Unassigned -> pure (SeqUncons (PE px ux))
               SeqUncons (PE py uy) ->
                 do p <- orPred sym px py
                    t <- appendSymSequence sym (snd ux) ys
                    let ux' = (fst ux, t)
                    SeqUncons <$> runPartialT sym p (f' px ux' uy)

newtype SeqTail sym tp =
  SeqTail
  { getSeqTail :: PartExpr (Pred sym) (SymSequence sym tp) }

-- | Compute the tail of a sequence, if it has one
tailSymSequence :: forall sym a.
  IsExprBuilder sym =>
  sym ->
  SymSequence sym a ->
  IO (PartExpr (Pred sym) (SymSequence sym a))
tailSymSequence sym = \s -> getSeqTail <$> evalWithFreshCache f s
  where
   f' :: Pred sym ->
         SymSequence sym a ->
         SymSequence sym a ->
         PartialT sym IO (SymSequence sym a)
   f' c x y = PartialT $ \_ p -> PE p <$> muxSymSequence sym c x y

   f :: (SymSequence sym a -> IO (SeqTail sym a)) -> (SymSequence sym a -> IO (SeqTail sym a))
   f _loop SymSequenceNil = pure (SeqTail Unassigned)
   f _loop (SymSequenceCons _ _v tl) = pure (SeqTail (justPartExpr sym tl))
   f loop (SymSequenceMerge _ p xs ys) =
     do tx <- getSeqTail <$> loop xs
        ty <- getSeqTail <$> loop ys
        SeqTail <$> mergePartial sym f' p tx ty
   f loop (SymSequenceAppend _ xs ys) =
     loop xs >>= \case
       SeqTail Unassigned -> loop ys
       SeqTail (PE px tx)
         | Just True <- asConstantPred px ->
             do t <- appendSymSequence sym tx ys
                pure (SeqTail (PE px t))

         | otherwise ->
             loop ys >>= \case
               SeqTail Unassigned -> pure (SeqTail (PE px tx))
               SeqTail (PE py ty) ->
                 do p <- orPred sym px py
                    t <- appendSymSequence sym tx ys
                    SeqTail <$> runPartialT sym p (f' px t ty)

-- | Using the given evaluation function for booleans, and an evaluation
--   function for values, compute a concrete sequence corresponding
--   to the given symbolic sequence.
concreteizeSymSequence ::
  (Pred sym -> IO Bool) {- ^ evaluation for booleans -} ->
  (a -> IO b) {- ^ evaluation for values -} ->
  SymSequence sym a -> IO [b]
concreteizeSymSequence conc eval = loop
  where
    loop SymSequenceNil = pure []
    loop (SymSequenceCons _ v tl) = (:) <$> eval v <*> loop tl
    loop (SymSequenceAppend _ xs ys) = (++) <$> loop xs <*> loop ys
    loop (SymSequenceMerge _ p xs ys) =
      do b <- conc p
         if b then loop xs else loop ys
