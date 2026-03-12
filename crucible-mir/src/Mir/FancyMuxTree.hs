{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Mir.FancyMuxTree
  {-
( -- * Internal implementation types
  MirReferenceSymbol
, MirReferenceType
, pattern MirReferenceRepr
, MirReference(..)
, MirReferencePath(..)
, muxRefPath
, muxRef
, MirSlice
, pattern MirSliceRepr

  -- * MIR Syntax extension
, MIR
, MirStmt(..)
, mirExtImpl
) -} where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Reader
import qualified Data.Maybe as Maybe
import           Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map

import           Data.Parameterized.Classes

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

import           What4.Interface
import           What4.Partial
    (PartExpr, pattern Unassigned, pattern PE, justPartExpr, mergePartial, mkPE)


-- | A fancier version of MuxTree, where the value type `a` can include
-- symbolic expressions.
--
-- The value type must have a notion of a "concrete skeleton" (that is, it must
-- have an `OrdSkel` instance), such that values with matching skeletons (those
-- where `compareSkel x y == EQ`) can be muxed together.  This is effectively
-- like splitting the values into separate concrete and symbolic parts, so we
-- can handle the concrete parts with a MuxTree and the symbolic parts with
-- ordinary muxing.
--
-- Unlike with MuxTree, it is not guaranteed that the `Pred`s of a FancyMuxTree
-- cover all possibilities.  However, the process of constructing such a
-- partial FancyMuxTree will assert as a side effect that the "missing" cases
-- do not occur.  This is handled in runMuxLeafMA: if the MuxLeafT computation
-- aborts, then runMuxLeafMA asserts that the leaf is not active before
-- returning Nothing.
newtype FancyMuxTree sym a = FancyMuxTree (Map (Skeleton a) (a, Pred sym))

instance (Show a, IsSymInterface sym) => Show (FancyMuxTree sym a) where
  show (FancyMuxTree m) = show [(x, printSymExpr y) | (x, y) <- Map.elems m]


class OrdSkel t where
    compareSkel :: t -> t -> Ordering

compareSkelF :: OrdF t => t a -> t a' -> Ordering
compareSkelF x y = toOrdering $ compareF x y

compareSkelF2 :: (OrdF t, OrdF (u a)) => t a -> u a b -> t a' -> u a' b' -> Ordering
compareSkelF2 x x2 y y2 = case compareF x y of
    LTF -> LT
    EQF -> compareSkelF x2 y2
    GTF -> GT

newtype Skeleton a = Skeleton a

instance OrdSkel a => Eq (Skeleton a) where
    Skeleton x == Skeleton y = compareSkel x y == EQ

instance OrdSkel a => Ord (Skeleton a) where
    compare (Skeleton x) (Skeleton y) = compareSkel x y


viewFancyMuxTree :: FancyMuxTree sym a -> [(a, Pred sym)]
viewFancyMuxTree (FancyMuxTree m) = Map.elems m

buildFancyMuxTree :: (IsExprBuilder sym, OrdSkel a) =>
    sym ->
    -- | Mux operation on values.  This will only be called when the skeletons
    -- of the two values are `EQ`.
    (Pred sym -> a -> a -> IO a) ->
    [(a, Pred sym)] ->
    IO (FancyMuxTree sym a)
buildFancyMuxTree sym mux xs_ = FancyMuxTree <$> go Map.empty xs_
  where
    go m [] = return m
    go m ((x, p):xs) = case asConstantPred p of
        Just True -> go (Map.insert (Skeleton x) (x, truePred sym) m) xs
        Just False -> go m xs
        Nothing -> do
            m' <- Map.alterF (\old -> case old of
                Nothing -> return $ Just (x, p)
                Just (y, q) -> do
                    xy <- mux p x y
                    pq <- orPred sym p q
                    return $ Just (xy, pq)) (Skeleton x) m
            go m' xs

-- | A generalization of Crucible's 'assert' and 'addFailedAssertion' functions,
-- so that assertions and failures incurred in 'FancyMuxTree' or
-- "Mir.Intrinsics" operations do not necessarily need to affect the Crucible
-- symbolic execution state.
--
-- For instance, this is useful in the override matching procedure in SAW's MIR
-- backend, where SAW tests out many possible overrides before choosing one to
-- execute. The "Mir.Intrinsics" operations called during override matching are
-- run in a monad where 'maAssert' and 'maFail' map to the override matching
-- infrastructure's assertion and failure operations, so that SAW can use that
-- information to pick the correct override, while not modifying the Crucible
-- state for the function currently being verified unless that particular
-- override is picked.
--
-- The 'IsSymBackend' and 'MonadIO' constraints are just for convenience, to
-- avoid having to also specify @(IsSymBackend sym bak, MonadIO m)@ almost every
-- time we write @MonadAssert sym bak m@.
class (IsSymBackend sym bak, MonadIO m) => MonadAssert sym bak m where
    maAssert :: bak -> Pred sym -> SimErrorReason -> m ()
    maFail :: bak -> SimErrorReason -> m a

-- | Since @crucible-mir@ symbolic execution takes place mainly in 'IO', the
-- 'maAssert' and 'maFail' operations are interpreted as Crucible's 'assert' and
-- 'addFailedAssertion' operations when used in the 'IO' monad. This minimizes
-- noise when using 'MonadAssert' functions for their primary purpose of
-- @crucible-mir@ symbolic execution.
--
-- To use a different interpretation for 'maAssert' and 'maFail', make an
-- instance of 'MonadAssert' for another monad, and call 'maAssert' and 'maFail'
-- from that monad. Make sure you don't call them from within 'liftIO', as that
-- will use this instance instead.
instance IsSymBackend sym bak => MonadAssert sym bak IO where
    maAssert = assert
    maFail = addFailedAssertion

-- | Helper monad for processing the leaves of a `FancyMuxTree`.  It provides
-- two operations:
--
--  1. The computation can access the `leafPredicate` of the current leaf,
--     allowing it to make side effects or assertions conditional on the
--     current leaf being the active one.
--  2. The computation can abort, indicating that the desired operation can't
--     proceed on the current leaf.
newtype MuxLeafT sym m a =
    MuxLeafT { unMuxLeafT :: ReaderT (Pred sym) (ExceptT SimErrorReason m) a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTrans (MuxLeafT sym) where
    lift = MuxLeafT . lift . lift

instance Monad m => MonadFail (MuxLeafT sym m) where
    fail s = MuxLeafT $ lift $ throwE $ GenericSimError s

runMuxLeafT :: MuxLeafT sym m a -> Pred sym -> m (Either SimErrorReason a)
runMuxLeafT (MuxLeafT f) p = runExceptT $ runReaderT f p

-- | Run a 'MuxLeafT' operation in a 'MonadAssert' monad, where abortion of the
-- computation results in a 'maAssert' of the negation of the leaf predicate.
runMuxLeafMA :: MonadAssert sym bak m =>
    bak -> MuxLeafT sym m a -> Pred sym -> m (Maybe a)
runMuxLeafMA bak f p =
  let sym = backendGetSym bak in
  runMuxLeafT f p >>= \case
    Left msg -> do
        p' <- liftIO $ notPred sym p
        maAssert bak p' msg
        return Nothing
    Right x -> return $ Just x

-- | Run a MuxLeafT sub-computation under a more restrictive predicate.  If `f`
-- aborts, this function will `leafAssert` the negation of `p`.
subMuxLeafMA :: MonadAssert sym bak m =>
    bak -> MuxLeafT sym m a -> Pred sym -> MuxLeafT sym m (Maybe a)
subMuxLeafMA bak f p = do
    let sym = backendGetSym bak
    q <- leafPredicate
    pq <- liftIO $ andPred sym p q
    res <- lift $ runMuxLeafT f pq
    case res of
        Left msg -> do
            p' <- liftIO $ notPred sym p
            leafAssert bak p' msg
            return Nothing
        Right x -> return $ Just x

leafPredicate :: Monad m => MuxLeafT sym m (Pred sym)
leafPredicate = MuxLeafT ask

leafAssert :: MonadAssert sym bak m =>
    bak -> Pred sym -> SimErrorReason -> MuxLeafT sym m ()
leafAssert bak p msg = do
    let sym = backendGetSym bak
    q <- leafPredicate
    qp <- liftIO $ impliesPred sym q p
    lift $ maAssert bak qp msg

leafAbort :: Monad m => SimErrorReason -> MuxLeafT sym m a
leafAbort msg = MuxLeafT $ lift $ throwE msg

leafReadPartExpr :: MonadAssert sym bak m =>
    bak -> PartExpr (Pred sym) v -> SimErrorReason -> MuxLeafT sym m v
leafReadPartExpr _ Unassigned msg = leafAbort msg
leafReadPartExpr bak (PE p v) msg = do
    leafAssert bak p msg
    return v

-- | Set a PartExpr to a new value, conditional on the current leaf being
-- active.
leafUpdatePartExpr :: (IsSymBackend sym bak, MonadIO m) =>
    bak -> (Pred sym -> a -> a -> m a) ->
    a -> PartExpr (Pred sym) a -> MuxLeafT sym m (PartExpr (Pred sym) a)
leafUpdatePartExpr _bak _mux x Unassigned = mkPE <$> leafPredicate <*> pure x
leafUpdatePartExpr bak mux x (PE q y) = do
    let sym = backendGetSym bak
    p <- leafPredicate
    case asConstantPred p of
        Just True -> return $ mkPE (truePred sym) x
        Just False -> return $ PE q y
        Nothing -> do
            pq <- liftIO $ orPred sym p q
            xy <- lift $ mux p x y
            return $ mkPE pq xy

-- | Set a PartExpr to Unassigned, conditional on the current leaf being
-- active.
leafClearPartExpr :: (IsSymBackend sym bak, MonadIO m) =>
    bak -> PartExpr (Pred sym) a -> MuxLeafT sym m (PartExpr (Pred sym) a)
leafClearPartExpr _bak Unassigned = return Unassigned
leafClearPartExpr bak (PE q x) = do
    let sym = backendGetSym bak
    p <- leafPredicate
    pq <- liftIO $ andPred sym q =<< notPred sym p
    return $ mkPE pq x

toFancyMuxTree :: (IsExprBuilder sym) => sym -> a -> FancyMuxTree sym a
toFancyMuxTree sym x = FancyMuxTree $ Map.singleton (Skeleton x) (x, truePred sym)

-- | Transform the state `z` by applying `f` for each potential value of the
-- `FancyMuxTree`.  If `f` aborts on some value, the previous state is kept
-- unchanged.
foldFancyMuxTree :: MonadAssert sym bak m =>
    bak -> (b -> a -> MuxLeafT sym m b) -> b -> FancyMuxTree sym a -> m b
foldFancyMuxTree bak f z t = foldM g z $ viewFancyMuxTree t
  where
    g acc (x, p) = maybe acc id <$> runMuxLeafMA bak (f acc x) p

foldZipFancyMuxTree :: MonadAssert sym bak m =>
    bak -> (c -> a -> b -> MuxLeafT sym m c) -> c ->
    FancyMuxTree sym a -> FancyMuxTree sym b -> m c
foldZipFancyMuxTree bak f z tx ty =
    foldM g z $ zip (viewFancyMuxTree tx) (viewFancyMuxTree ty)
  where
    sym = backendGetSym bak
    g acc ((x, p), (y, q)) = do
        pq <- liftIO $ andPred sym p q
        maybe acc id <$> runMuxLeafMA bak (f acc x y) pq

-- | Map `f` over the potential values of the `FancyMuxTree`.  If `f` aborts,
-- then the input value will not have a corresponding entry in the output.
mapFancyMuxTree :: (MonadAssert sym bak m, OrdSkel b) =>
    bak -> (Pred sym -> b -> b -> IO b) ->
    (a -> MuxLeafT sym m b) -> FancyMuxTree sym a -> m (FancyMuxTree sym b)
mapFancyMuxTree bak mux f t = do
    let sym = backendGetSym bak
    ys <- Maybe.catMaybes <$>
        mapM (\(x,p) -> runMuxLeafMA bak (f x >>= \y -> return (y, p)) p) (viewFancyMuxTree t)
    liftIO $ buildFancyMuxTree sym mux ys

collapseFancyMuxTree :: MonadAssert sym bak m =>
    bak -> (Pred sym -> a -> a -> IO a) -> FancyMuxTree sym a -> m (Maybe a)
collapseFancyMuxTree bak mux t = readFancyMuxTree bak return mux t

collapseFancyMuxTree' :: MonadAssert sym bak m =>
    bak -> (Pred sym -> a -> a -> IO a) ->
    FancyMuxTree sym a -> m a
collapseFancyMuxTree' bak mux t = readFancyMuxTree' bak return mux t

collapsePartialFancyMuxTree :: MonadAssert sym bak m =>
    bak-> (Pred sym -> a -> a -> IO a) -> FancyMuxTree sym a -> m (PartExpr (Pred sym) a)
collapsePartialFancyMuxTree bak mux t = readPartialFancyMuxTree bak return mux t

-- Perform a "read" operation on a FancyMuxTree, by reading each leaf with `f`
-- and combining the results with `mux`.
readFancyMuxTree :: MonadAssert sym bak m =>
    bak ->
    (a -> MuxLeafT sym m b) ->
    (Pred sym -> b -> b -> IO b) ->
    FancyMuxTree sym a -> m (Maybe b)
readFancyMuxTree bak f mux t = foldFancyMuxTree bak go Nothing t
  where
    go Nothing x = Just <$> f x
    go (Just old) x = do
        y <- f x
        p <- leafPredicate
        liftIO $ Just <$> mux p y old

readFancyMuxTree' :: MonadAssert sym bak m =>
    bak ->
    (a -> MuxLeafT sym m b) ->
    (Pred sym -> b -> b -> IO b) ->
    FancyMuxTree sym a -> m b
readFancyMuxTree' bak f mux t = readFancyMuxTree bak f mux t >>= \my -> case my of
    Just y -> return y
    Nothing -> maFail bak $ GenericSimError $
        "attempted to read empty mux tree"

readPartialFancyMuxTree :: MonadAssert sym bak m =>
    bak ->
    (a -> MuxLeafT sym m b) ->
    (Pred sym -> b -> b -> IO b) ->
    FancyMuxTree sym a -> m (PartExpr (Pred sym) b)
readPartialFancyMuxTree bak f mux t = foldFancyMuxTree bak go Unassigned t
  where
    sym = backendGetSym bak

    go old x = do
        p <- leafPredicate
        y <- f x
        lift $ mergePartial sym mux' p (justPartExpr sym y) old
    mux' p x y = liftIO $ mux p x y

zipFancyMuxTrees :: MonadAssert sym bak m =>
    bak ->
    (a -> b -> MuxLeafT sym m c) ->
    (Pred sym -> c -> c -> m c) ->
    FancyMuxTree sym a -> FancyMuxTree sym b -> m (Maybe c)
zipFancyMuxTrees bak f mux tx ty = foldZipFancyMuxTree bak go Nothing tx ty
  where
    go Nothing x y = Just <$> f x y
    go (Just old) x y = do
        z <- f x y
        p <- leafPredicate
        lift $ Just <$> mux p z old

zipFancyMuxTrees' :: MonadAssert sym bak m =>
    bak ->
    (a -> b -> MuxLeafT sym m c) ->
    (Pred sym -> c -> c -> m c) ->
    FancyMuxTree sym a -> FancyMuxTree sym b -> m c
zipFancyMuxTrees' bak f mux tx ty = zipFancyMuxTrees bak f mux tx ty >>= \my -> case my of
    Just y -> return y
    Nothing -> liftIO $ addFailedAssertion bak $ GenericSimError $
        "attempted to read empty mux tree"

mergeFancyMuxTree :: (IsExprBuilder sym, OrdSkel a, MonadIO m) =>
    sym -> (Pred sym -> a -> a -> m a) ->
    Pred sym -> FancyMuxTree sym a -> FancyMuxTree sym a -> m (FancyMuxTree sym a)
mergeFancyMuxTree sym mux p (FancyMuxTree xm) (FancyMuxTree ym) = do
    p' <- liftIO $ notPred sym p
    FancyMuxTree <$> Map.mergeA
        (Map.traverseMaybeMissing $ filterLeaf p)
        (Map.traverseMaybeMissing $ filterLeaf p')
        (Map.zipWithMaybeAMatched mergeLeaf)
        xm ym

  where
    filterLeaf p_ _k (x, q) = do
        pq <- liftIO $ andPred sym p_ q
        case asConstantPred pq of
            Just False -> return Nothing
            _ -> return $ Just (x, pq)

    mergeLeaf _k (x, q) (y, r) = do
        qr <- liftIO $ itePred sym p q r
        case asConstantPred qr of
            Just False -> return Nothing
            _ -> do
                xy <- mux p x y
                return $ Just (xy, qr)
