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
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
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

import           GHC.Natural
import           GHC.TypeLits
import           Control.Applicative (Alternative)
import           Control.Lens hiding (Empty, (:>), Index, view)
import           Control.Monad
import           Control.Monad.Fail
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Reader
import           Data.Kind(Type)
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import           Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.String
import qualified Data.Vector as V

import qualified Text.Regex as Regex
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.TH.GADT as U
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as N

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Extension.Safety(AssertionClassifier,NoAssertionClassifier,HasStructuredAssertions(..))
import           Lang.Crucible.CFG.Generator hiding (dropRef)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Panic
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree hiding (FnState)
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Utils.MuxTree

import           What4.Concrete (ConcreteVal(..), concreteType)
import           What4.Interface
import           What4.Partial
    (PartExpr, pattern Unassigned, pattern PE, maybePartExpr, justPartExpr, joinMaybePE,
        mergePartial, mkPE)
import           What4.Utils.MonadST

import           Mir.DefId
import           Mir.Mir
import           Mir.PP

import           Debug.Trace

import           Unsafe.Coerce


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
-- do not occur.  This is handled in runMuxLeafIO: if the MuxLeafT computation
-- aborts, then runMuxLeafIO asserts that the leaf is not active before
-- returning Nothing.
newtype FancyMuxTree sym a = FancyMuxTree (Map (Skeleton a) (a, Pred sym))


class OrdSkel t where
    compareSkel :: t -> t -> Ordering

class OrdSkel1 (t :: k1 -> *) where
    compareSkel1 :: t a -> t a' -> Ordering

class OrdSkel2 (t :: k1 -> k2 -> *) where
    compareSkel2 :: t a b -> t a' b' -> Ordering

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

buildFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, OrdSkel a) =>
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

runMuxLeafIO :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> MuxLeafT sym m a -> Pred sym -> m (Maybe a)
runMuxLeafIO sym f p = runMuxLeafT f p >>= \mx -> case mx of
    Left msg -> liftIO $ do
        p' <- notPred sym p
        assert sym p' msg
        return Nothing
    Right x -> return $ Just x

-- | Run a MuxLeafT computation on `truePred sym`, turning it back into a
-- computation in the parent monad.
runMuxLeafIO' :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> MuxLeafT sym m a -> m a
runMuxLeafIO' sym f = runMuxLeafT f (truePred sym) >>= \mx -> case mx of
    Left msg -> liftIO $ addFailedAssertion sym msg
    Right x -> return x

-- | Run a MuxLeafT sub-computation under a more restrictive predicate.  If `f`
-- aborts, this function will `leafAssert` the negation of `p`.
subMuxLeafIO :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> MuxLeafT sym m a -> Pred sym -> MuxLeafT sym m (Maybe a)
subMuxLeafIO sym f p = do
    q <- leafPredicate
    pq <- liftIO $ andPred sym p q
    res <- lift $ runMuxLeafT f pq
    case res of
        Left msg -> do
            p' <- liftIO $ notPred sym p
            leafAssert sym p' msg
            return Nothing
        Right x -> return $ Just x

leafPredicate :: Monad m => MuxLeafT sym m (Pred sym)
leafPredicate = MuxLeafT ask

leafAssert :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> Pred sym -> SimErrorReason -> MuxLeafT sym m ()
leafAssert sym p msg = do
    q <- leafPredicate
    liftIO $ do
        qp <- impliesPred sym q p
        assert sym qp msg

-- The `sym` argument is kept in the signature for compatibility with
-- `addFailedAssertion`.  It's unused because the assertion isn't created until
-- `runMuxLeafIO`, which has its own access to `sym`.
leafAbort :: Monad m => sym -> SimErrorReason -> MuxLeafT sym m a
leafAbort _sym msg = MuxLeafT $ lift $ throwE msg

leafReadPartExpr :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> PartExpr (Pred sym) v -> SimErrorReason -> MuxLeafT sym m v
leafReadPartExpr sym Unassigned msg = leafAbort sym msg
leafReadPartExpr sym (PE p v) msg = do
    leafAssert sym p msg
    return v

-- | Set a PartExpr to a new value, conditional on the current leaf being
-- active.
leafUpdatePartExpr :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> (Pred sym -> a -> a -> m a) ->
    a -> PartExpr (Pred sym) a -> MuxLeafT sym m (PartExpr (Pred sym) a)
leafUpdatePartExpr _sym _mux x Unassigned = mkPE <$> leafPredicate <*> pure x
leafUpdatePartExpr sym mux x (PE q y) = do
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
leafClearPartExpr :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> PartExpr (Pred sym) a -> MuxLeafT sym m (PartExpr (Pred sym) a)
leafClearPartExpr _sym Unassigned = return Unassigned
leafClearPartExpr sym (PE q x) = do
    p <- leafPredicate
    pq <- liftIO $ andPred sym q =<< notPred sym p
    return $ mkPE pq x

toFancyMuxTree :: (IsExprBuilder sym) => sym -> a -> FancyMuxTree sym a
toFancyMuxTree sym x = FancyMuxTree $ Map.singleton (Skeleton x) (x, truePred sym)

-- | Transform the state `z` by applying `f` for each potential value of the
-- `FancyMuxTree`.  If `f` aborts on some value, the previous state is kept
-- unchanged.
foldFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> (b -> a -> MuxLeafT sym m b) -> b -> FancyMuxTree sym a -> m b
foldFancyMuxTree sym f z t = foldM g z $ viewFancyMuxTree t
  where
    g acc (x, p) = maybe acc id <$> runMuxLeafIO sym (f acc x) p

foldZipFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> (c -> a -> b -> MuxLeafT sym m c) -> c ->
    FancyMuxTree sym a -> FancyMuxTree sym b -> m c
foldZipFancyMuxTree sym f z tx ty =
    foldM g z $ zip (viewFancyMuxTree tx) (viewFancyMuxTree ty)
  where
    g acc ((x, p), (y, q)) = do
        pq <- liftIO $ andPred sym p q
        maybe acc id <$> runMuxLeafIO sym (f acc x y) pq

-- | Map `f` over the potential values of the `FancyMuxTree`.  If `f` aborts,
-- then the input value will not have a corresponding entry in the output.
mapFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, OrdSkel b) =>
    sym -> (Pred sym -> b -> b -> IO b) ->
    (a -> MuxLeafT sym IO b) -> FancyMuxTree sym a -> IO (FancyMuxTree sym b)
mapFancyMuxTree sym mux f t = do
    ys <- Maybe.catMaybes <$>
        mapM (\(x,p) -> runMuxLeafIO sym (f x >>= \y -> return (y, p)) p) (viewFancyMuxTree t)
    buildFancyMuxTree sym mux ys

collapseFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> (Pred sym -> a -> a -> m a) -> FancyMuxTree sym a -> m (Maybe a)
collapseFancyMuxTree sym mux t = readFancyMuxTree sym return mux t

collapseFancyMuxTree' :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> (Pred sym -> a -> a -> m a) ->
    FancyMuxTree sym a -> m a
collapseFancyMuxTree' sym mux t = readFancyMuxTree' sym return mux t

collapsePartialFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym -> (Pred sym -> a -> a -> m a) -> FancyMuxTree sym a -> m (PartExpr (Pred sym) a)
collapsePartialFancyMuxTree sym mux t = readPartialFancyMuxTree sym return mux t

-- Perform a "read" operation on a FancyMuxTree, by reading each leaf with `f`
-- and combining the results with `mux`.
readFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym ->
    (a -> MuxLeafT sym m b) ->
    (Pred sym -> b -> b -> m b) ->
    FancyMuxTree sym a -> m (Maybe b)
readFancyMuxTree sym f mux t = foldFancyMuxTree sym go Nothing t
  where
    go Nothing x = Just <$> f x
    go (Just old) x = do
        y <- f x
        p <- leafPredicate
        lift $ Just <$> mux p y old

readFancyMuxTree' :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym ->
    (a -> MuxLeafT sym m b) ->
    (Pred sym -> b -> b -> m b) ->
    FancyMuxTree sym a -> m b
readFancyMuxTree' sym f mux t = readFancyMuxTree sym f mux t >>= \my -> case my of
    Just y -> return y
    Nothing -> liftIO $ addFailedAssertion sym $ GenericSimError $
        "attemted to read empty mux tree"

readPartialFancyMuxTree :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym ->
    (a -> MuxLeafT sym m b) ->
    (Pred sym -> b -> b -> m b) ->
    FancyMuxTree sym a -> m (PartExpr (Pred sym) b)
readPartialFancyMuxTree sym f mux t = foldFancyMuxTree sym go Unassigned t
  where
    go old x = do
        p <- leafPredicate
        y <- f x
        lift $ mergePartial sym mux' p (justPartExpr sym y) old
    mux' p x y = lift $ mux p x y

zipFancyMuxTrees :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym ->
    (a -> b -> MuxLeafT sym m c) ->
    (Pred sym -> c -> c -> m c) ->
    FancyMuxTree sym a -> FancyMuxTree sym b -> m (Maybe c)
zipFancyMuxTrees sym f mux tx ty = foldZipFancyMuxTree sym go Nothing tx ty
  where
    go Nothing x y = Just <$> f x y
    go (Just old) x y = do
        z <- f x y
        p <- leafPredicate
        lift $ Just <$> mux p z old

zipFancyMuxTrees' :: (IsExprBuilder sym, IsBoolSolver sym, MonadIO m) =>
    sym ->
    (a -> b -> MuxLeafT sym m c) ->
    (Pred sym -> c -> c -> m c) ->
    FancyMuxTree sym a -> FancyMuxTree sym b -> m c
zipFancyMuxTrees' sym f mux tx ty = zipFancyMuxTrees sym f mux tx ty >>= \my -> case my of
    Just y -> return y
    Nothing -> liftIO $ addFailedAssertion sym $ GenericSimError $
        "attemted to read empty mux tree"

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
