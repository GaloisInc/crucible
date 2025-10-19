{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- Needed for Pretty instance
{-# LANGUAGE UndecidableInstances #-}
module Lang.Crucible.Simulator.SymSequence
( SymSequence(..)
, nilSymSequence
, consSymSequence
, fromListSymSequence
, appendSymSequence
, muxSymSequence
, isNilSymSequence
, lengthSymSequence
, headSymSequence
, tailSymSequence
, unconsSymSequence
, eqSymSequence
, traverseSymSequence
, concreteizeSymSequence
, concretizeSymSequence
, prettySymSequence

  -- * Low-level evaluation primitives
, newSeqCache
, evalWithCache
, evalWithFreshCache
) where

import           Control.Monad.State
import           Data.Functor.Const
import           Data.Kind (Type)
import           Data.IORef
import           Data.Maybe (isJust)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Map as MapF
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

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
muxSymSequence ::
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

{-# SPECIALIZE
  evalWithFreshCache ::
  ((SymSequence sym a -> IO (f a)) -> SymSequence sym a -> IO (f a)) ->
  (SymSequence sym a -> IO (f a))
 #-}

evalWithFreshCache :: MonadIO m =>
  ((SymSequence sym a -> m (f a)) -> SymSequence sym a -> m (f a)) ->
  (SymSequence sym a -> m (f a))
evalWithFreshCache fn s =
  do c <- liftIO newSeqCache
     evalWithCache c fn s

{-# SPECIALIZE
  evalWithCache ::
  SeqCache f ->
  ((SymSequence sym a -> IO (f a)) -> SymSequence sym a -> IO (f a)) ->
  (SymSequence sym a -> IO (f a))
 #-}

evalWithCache :: MonadIO m =>
  SeqCache f ->
  ((SymSequence sym a -> m (f a)) -> SymSequence sym a -> m (f a)) ->
  (SymSequence sym a -> m (f a))
evalWithCache (SeqCache ref) fn = loop
  where
    loop s
      | Just n <- symSequenceNonce s =
          (MapF.lookup n <$> liftIO (readIORef ref)) >>= \case
            Just v -> pure v
            Nothing ->
              do v <- fn loop s
                 liftIO (modifyIORef ref (MapF.insert n v))
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

fromListSymSequence :: sym -> [a] -> IO (SymSequence sym a)
fromListSymSequence sym =
  \case
    [] -> nilSymSequence sym
    (x:xs) -> consSymSequence sym x =<< fromListSymSequence sym xs

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

eqSymSequence ::
  IsExprBuilder sym =>
  sym ->
  (a -> a -> IO (Pred sym)) {- ^ equality function on values -} ->
  (Pred sym -> a -> a -> IO a) {- ^ mux function on values -} ->
  SymSequence sym a ->
  SymSequence sym a ->
  IO (Pred sym)
eqSymSequence sym eq mux s s' =
  go =<< eqSymSequencePrefix sym eq mux s s'
  where
    go =
      \case
        NotPrefix -> pure (falsePred sym)
        LeftLonger {} -> pure (falsePred sym)
        RightLonger {} -> pure (falsePred sym)
        Equal p -> pure p
        Ite p l r -> do
          l' <- go l
          r' <- go r
          i <- itePred sym p l' r'
          pure i

data AsPrefixResult sym a
  = LeftLonger (Pred sym) (SymSequence sym a)
  | RightLonger (Pred sym) (SymSequence sym a)
  | Equal (Pred sym)
  | Ite (Pred sym) (AsPrefixResult sym a) (AsPrefixResult sym a)
  | NotPrefix

reverseAsPrefixResult ::
  IsExprBuilder sym =>
  sym ->
  AsPrefixResult sym a ->
  IO (AsPrefixResult sym a)
reverseAsPrefixResult sym =
  \case
    LeftLonger p s -> pure (RightLonger p s)
    RightLonger p s -> pure (LeftLonger p s)
    Equal p -> pure (Equal p)
    NotPrefix -> pure NotPrefix
    Ite p l r -> do
      p' <- notPred sym p
      pure (Ite p' r l)

andAsPrefixResult ::
  IsExprBuilder sym =>
  sym ->
  Pred sym ->
  AsPrefixResult sym a ->
  IO (AsPrefixResult sym a)
andAsPrefixResult sym l =
  \case
    LeftLonger r rest -> do
      p <- andPred sym l r
      pure (LeftLonger p rest)
    RightLonger r rest -> do
      p <- andPred sym l r
      pure (RightLonger p rest)
    Equal r -> do
      p <- andPred sym l r
      pure (Equal p)
    NotPrefix -> pure NotPrefix
    Ite p l' r' -> do
      l'' <- andAsPrefixResult sym l l'
      r'' <- andAsPrefixResult sym l r'
      pure (Ite p l'' r'')

eqSymSequencePrefix ::
  IsExprBuilder sym =>
  sym ->
  (a -> a -> IO (Pred sym)) {- ^ equality function on values -} ->
  (Pred sym -> a -> a -> IO a) {- ^ mux function on values -} ->
  SymSequence sym a ->
  SymSequence sym a ->
  IO (AsPrefixResult sym a)
eqSymSequencePrefix sym eq mux l r =
  case (l, r) of
    (SymSequenceNil, SymSequenceNil) -> pure (Equal (truePred sym))
    (SymSequenceNil, SymSequenceCons {}) -> pure (RightLonger (truePred sym) r)
    (SymSequenceCons {}, SymSequenceNil) -> pure (LeftLonger (truePred sym) l)
    (SymSequenceMerge n _ _ _, SymSequenceMerge n' _ _ _) | n == n' ->
      pure (Equal (truePred sym))
    (SymSequenceMerge _ p t f, _) ->
      eqIte p t f r
    (_, SymSequenceMerge _ p t f) ->
      eqIte p t f l
    (SymSequenceCons n _ _, SymSequenceCons n' _ _) | n == n' ->
      pure (Equal (truePred sym))
    (SymSequenceCons _ x rest, SymSequenceCons _ x' rest') -> do
      heads <- eq x x'
      case asConstantPred heads of
        Just False -> pure NotPrefix
        _ -> do
          tails <- eqSymSequencePrefix sym eq mux rest rest'
          andAsPrefixResult sym heads tails
    (SymSequenceAppend n _ _, SymSequenceAppend n' _ _) | n == n' ->
      pure (Equal (truePred sym))
    (SymSequenceAppend _ us vs, SymSequenceAppend _ xs ys) ->
      eqAppend us vs xs ys
    (SymSequenceNil, SymSequenceAppend _ xs ys) -> do
      nilXs <- isNilSymSequence sym xs
      nilYs <- isNilSymSequence sym ys
      isNil <- andPred sym nilXs nilYs
      -- pure (Equal isNil)
      -- pure (RightLonger isNil r)
      pure (Ite isNil (Equal (truePred sym)) (RightLonger (truePred sym) r))
    (SymSequenceAppend {}, SymSequenceNil) ->
      reverseAsPrefixResult sym =<<
        eqSymSequencePrefix sym eq mux r l  -- above case
    (SymSequenceCons _ x xs, SymSequenceAppend {}) -> do
      mS <- unconsSymSequence sym mux r
      case mS of
        Unassigned -> pure NotPrefix
        PE ok (y, ys) -> do
          heads <- eq x y
          valid <- andPred sym ok heads
          tails <- eqSymSequencePrefix sym eq mux xs ys
          andAsPrefixResult sym valid tails
    (SymSequenceAppend {}, SymSequenceCons {}) ->
      reverseAsPrefixResult sym =<<
        eqSymSequencePrefix sym eq mux r l  -- above case
  where
    eqIte p t f s = do
      t' <- eqSymSequencePrefix sym eq mux t s
      f' <- eqSymSequencePrefix sym eq mux f s
      pure (Ite p t' f')

    eqAppend us vs xs ys =
      eqSymSequencePrefix sym eq mux us xs >>=
        appendPfx us vs xs ys

    appendPfx us vs xs ys =
      \case
        NotPrefix ->
          eqSymSequencePrefix sym eq mux l ys
        Equal heads -> do
          tails <- eqSymSequencePrefix sym eq mux vs ys
          andAsPrefixResult sym heads tails
        LeftLonger heads us' -> do
          vs' <- appendSymSequence sym us' vs
          tails <- eqSymSequencePrefix sym eq mux vs' ys
          andAsPrefixResult sym heads tails
        RightLonger heads xs' ->  do
          ys' <- appendSymSequence sym xs' ys
          tails <- eqSymSequencePrefix sym eq mux vs ys'
          andAsPrefixResult sym heads tails
        Ite p t f -> do
          t' <- appendPfx us vs xs ys t
          f' <- appendPfx us vs xs ys f
          pure (Ite p t' f')

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


{-# SPECIALIZE
  traverseSymSequence ::
  sym ->
  (a -> IO b) ->
  SymSequence sym a ->
  IO (SymSequence sym b)
 #-}

-- | Visit every element in the given symbolic sequence,
--   applying the given action, and constructing a new
--   sequence. The traversal is memoized, so any given
--   subsequence will be visited at most once.
traverseSymSequence :: forall m sym a b.
  MonadIO m =>
  sym ->
  (a -> m b) ->
  SymSequence sym a ->
  m (SymSequence sym b)
traverseSymSequence sym f = \s -> getConst <$> evalWithFreshCache fn s
  where
   fn :: (SymSequence sym a -> m (Const (SymSequence sym b) a)) ->
         (SymSequence sym a -> m (Const (SymSequence sym b) a))
   fn _loop SymSequenceNil = pure (Const SymSequenceNil)
   fn loop (SymSequenceCons _ v tl) =
     do v'  <- f v
        tl' <- getConst <$> loop tl
        liftIO (Const <$> consSymSequence sym v' tl')
   fn loop (SymSequenceAppend _ xs ys) =
     do xs' <- getConst <$> loop xs
        ys' <- getConst <$> loop ys
        liftIO (Const <$> appendSymSequence sym xs' ys')
   fn loop (SymSequenceMerge _ p xs ys) =
     do xs' <- getConst <$> loop xs
        ys' <- getConst <$> loop ys
        liftIO (Const <$> muxSymSequence sym p xs' ys')


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
{-# DEPRECATED concreteizeSymSequence "Use concretizeSymSequence instead" #-} 

-- | Using the given evaluation function for booleans, and an evaluation
--   function for values, compute a concrete sequence corresponding
--   to the given symbolic sequence.
concretizeSymSequence ::
  (Pred sym -> IO Bool) {- ^ evaluation for booleans -} ->
  (a -> IO b) {- ^ evaluation for values -} ->
  SymSequence sym a ->
  IO (Seq b)
concretizeSymSequence conc eval = loop
  where
    loop SymSequenceNil = pure Seq.empty
    loop (SymSequenceCons _ v tl) = (Seq.<|) <$> eval v <*> loop tl
    loop (SymSequenceAppend _ xs ys) = (Seq.><) <$> loop xs <*> loop ys
    loop (SymSequenceMerge _ p xs ys) =
      do b <- conc p
         if b then loop xs else loop ys

instance (IsExpr (SymExpr sym), PP.Pretty a) => PP.Pretty (SymSequence sym a) where
  pretty = prettySymSequence PP.pretty

-- | Given a pretty printer for elements,
--   print a symbolic sequence.
prettySymSequence :: IsExpr (SymExpr sym) =>
  (a -> Doc ann) ->
  SymSequence sym a ->
  Doc ann
prettySymSequence ppa s = if Map.null bs then x else letlayout
  where
    occMap = computeOccMap s mempty
    (x,bs) = runState (prettyAux ppa occMap s) mempty
    letlayout = PP.vcat
      ["let" PP.<+> (PP.align (PP.vcat [ letbind n d | (n,d) <- Map.toList bs ]))
      ," in" PP.<+> x
      ]
    letbind n d = ppSeqNonce n PP.<+> "=" PP.<+> PP.align d

computeOccMap ::
  SymSequence sym a ->
  Map (Nonce GlobalNonceGenerator a) Integer ->
  Map (Nonce GlobalNonceGenerator a) Integer
computeOccMap = loop
  where
    visit n k m
      | Just i <- Map.lookup n m = Map.insert n (i+1) m
      | otherwise = k (Map.insert n 1 m)

    loop SymSequenceNil = id
    loop (SymSequenceCons n _ tl) = visit n (loop tl)
    loop (SymSequenceAppend n xs ys) = visit n (loop xs . loop ys)
    loop (SymSequenceMerge n _ xs ys) = visit n (loop xs . loop ys)

ppSeqNonce :: Nonce GlobalNonceGenerator a -> Doc ann
ppSeqNonce n = "s" <> PP.viaShow (indexValue n)

prettyAux ::
  IsExpr (SymExpr sym) =>
  (a -> Doc ann) ->
  Map (Nonce GlobalNonceGenerator a) Integer ->
  SymSequence sym a ->
  State (Map (Nonce GlobalNonceGenerator a) (Doc ann)) (Doc ann)
prettyAux ppa occMap = goTop
  where
    goTop SymSequenceNil = pure (PP.list [])
    goTop (SymSequenceCons _ v tl) = pp [] [v] [tl]
    goTop (SymSequenceAppend _ xs ys) = pp [] [] [xs,ys]
    goTop (SymSequenceMerge _ p xs ys) =
      do xd <- pp [] [] [xs]
         yd <- pp [] [] [ys]
         pure $ {- PP.group $ -} PP.hang 2 $ PP.vsep
           [ "if" PP.<+> printSymExpr p
           , "then" PP.<+> xd
           , "else" PP.<+> yd
           ]

    visit n s =
      do dm <- get
         case Map.lookup n dm of
           Just _ -> return ()
           Nothing ->
             do d <- goTop s
                modify (Map.insert n d)
         return (ppSeqNonce n)

    finalize []  = PP.list []
    finalize [x] = x
    finalize xs  = PP.sep (PP.punctuate (PP.space <> "<>") (reverse xs))

    elemSeq rs = PP.list (map ppa (reverse rs))

    addSeg segs [] seg = (seg : segs)
    addSeg segs rs seg = (seg : elemSeq rs : segs)

    -- @pp@ accumulates both "segments" of sequences (segs)
    -- and individual values (rs) to be output.  Both are
    -- in reversed order.  Segments represent sequences
    -- and must be combined with the append operator,
    -- and rs represent individual elements that must be combined
    -- with cons (or, in actuality, list syntax with brackets and commas).

    -- @pp@ works over a list of SymSequence values, which represent a worklist
    -- of segments to process.  Morally, the invariant of @pp@ is that the
    -- arguments always represent the same sequence, which is computed as
    -- @concat (reverse segs) ++ reverse rs ++ concat ss@

    pp segs [] [] = pure (finalize segs)
    pp segs rs [] = pure (finalize ( elemSeq rs : segs ))

    pp segs rs (SymSequenceNil:ss) = pp segs rs ss

    pp segs rs (s@(SymSequenceCons n v tl) : ss)
      | Just i <- Map.lookup n occMap, i > 1
      = do x <- visit n s
           pp (addSeg segs rs x) [] ss

      | otherwise
      = pp segs (v : rs) (tl : ss)

    pp segs rs (s@(SymSequenceAppend n xs ys) : ss)
      | Just i <- Map.lookup n occMap, i > 1
      = do x <- visit n s
           pp (addSeg segs rs x) [] ss

      | otherwise
      = pp segs rs (xs:ys:ss)

    pp segs rs (s@(SymSequenceMerge n _ _ _) : ss)
      = do x <- visit n s
           pp (addSeg segs rs x) [] ss
