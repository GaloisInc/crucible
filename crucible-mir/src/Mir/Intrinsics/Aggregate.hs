{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- TODO(#1786): refine exports
module Mir.Intrinsics.Aggregate
  ( MirAggregate (..),
    MirAggregateEntry (..),
    MirAggregateSymbol,
    MirAggregateType,
    pattern MirAggregateRepr,
    MirAggregateFam,
    muxMirAggregateEntry,
    muxMirAggregate,
    mirAgTypedCandidates,
    liftIteFnMaybe,
    agNoValueAtOffsetSimError,
    agNoValueAtSymbolicOffsetSimError,
    readMirAggregateWithSymOffset,
    adjustMirAggregateWithSymOffset,
    offsetInSpans,
    foldRuns,
    addToRun,
    mkRun,
    Run (..),
    mirAggregate_entries,
    mirAggregate_insert,
    writeMirAggregateWithSymOffset,
    mirAggregate_lookup,
    resizeMirAggregate,
    mirAggregate_split,
    mirAggregate_split3,
    mirAggregate_chunk,
    mirAggregate_toChunks,
    mirAggregate_concat,
    mirAggregate_fromChunks,
    concreteAllocSize,
    mirAggregate_uninitIO,
    mirAggregate_zstSim,
    mirAggregate_zstIO,
    mirAggregate_replicateIO,
    mirAggregate_resizeIO,
    mirAggregate_getIO,
    mirAggregate_setIO,
  )
where

import GHC.Stack (callStack)
import GHC.TypeLits
  ( ErrorMessage (ShowType, Text, (:<>:)),
    TypeError,
  )

import Control.Monad (foldM, forM, forM_, liftM, unless, when)
import Control.Monad.Except (MonadError (..), runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans (lift)

import Data.BitVector.Sized qualified as BV
import Data.Either (fromRight)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.Kind (Type)
import Data.Maybe qualified as Maybe
import Data.Parameterized (knownRepr)
import Data.Parameterized.Context (Ctx, EmptyCtx, pattern Empty)
import Data.Parameterized.SymbolRepr (knownSymbol)
import Data.Type.Equality (testEquality, pattern Refl)

import Lang.Crucible.Backend
  ( IsSymBackend,
    IsSymInterface,
    addFailedAssertion,
    backendGetSym,
    readPartExpr,
  )
import Lang.Crucible.Panic (panic)
import Lang.Crucible.Simulator.Intrinsics (IntrinsicClass (..), IntrinsicTypes, typeError)
import Lang.Crucible.Simulator.OverrideSim (OverrideSim)
import Lang.Crucible.Simulator.RegMap (RegValue, muxRegForType)
import Lang.Crucible.Simulator.SimError (SimErrorReason (..))
import Lang.Crucible.Types
  ( BaseBoolType,
    CrucibleType,
    IntrinsicType,
    MaybeType,
    TypeRepr (..),
  )

import What4.Concrete (fromConcreteBV)
import What4.Interface (IsExprBuilder (..), Pred, SymExpr, asAffineVar, asBV, asConstantPred)
import What4.Partial (PartExpr, justPartExpr, mergePartial, pattern PE, pattern Unassigned)

import Mir.FancyMuxTree
  ( MonadAssert,
    MuxLeafT,
    leafAbort,
    leafAssert,
    leafReadPartExpr,
    subMuxLeafMA,
  )
import Mir.Intrinsics.Size (UsizeType, wordLit)
import Mir.Mir (OpSize (..))

--------------------------------------------------------------
-- A MirAggregateType is a collection of elements of any type, with each entry
-- covering a specific range of logical bytes.

-- | A block of memory representing an aggregate value, such as a struct,
-- tuple, or array.  A `MirAggregate` value has a size in bytes and a set of
-- entries.  Each entry covers some range of bytes within the aggregate and
-- associates a `RegValue` with that range.  Entries are nonoverlapping, they
-- never extend past the size of the overall aggregate, and their byte ranges
-- and types are concrete (but their values may be symbolic).
--
-- The set of entries in a `MirAggregate` is not determined by its type (note
-- that `MirAggregate` doesn't take a `CtxRepr` or similar type index).
-- Instead, each `MirAggregate` begins empty, and entries are added to it
-- dynamically.  To keep the implementation simple, new entries are not allowed
-- to partially overlap old ones - they must either be disjoint from all
-- existing entries, or fully overwrite an existing entry.  Read operations
-- must also touch exactly one entry.
data MirAggregate sym where
  MirAggregate ::
    -- | Total size in bytes.  No entry can extend beyond this limit.
    !Word ->
    -- | Maps byte offset to an entry starting at that offset.
    !(IntMap (MirAggregateEntry sym)) ->
    MirAggregate sym

-- | A single entry in a `MirAggregate`.  The start of the covered byte range
-- is not stored here; instead, it's used as the key in the `MirAggregate`'s
-- `IntMap`.  This stores the size of the entry in bytes (which determines the
-- end of the range), the type of value, and a symbolic value of that type.
-- The value is wrapped in `MaybeRepr` / `PartExpr` so that the output of a mux
-- operation on `MirAggregate`s can have entries that are only conditionally
-- initialized.
data MirAggregateEntry sym where
  MirAggregateEntry :: forall sym tp.
    -- | Size in bytes
    !Word ->
    !(TypeRepr tp) ->
    !(RegValue sym (MaybeType tp)) ->
    MirAggregateEntry sym

instance IsSymInterface sym => Show (MirAggregateEntry sym) where
  show (MirAggregateEntry sz tpr _rv) =
    "(MirAggregateEntry " ++ show sz ++ " " ++ show tpr ++ " <regvalue>)"

type MirAggregateSymbol = "MirAggregate"
type MirAggregateType = IntrinsicType MirAggregateSymbol EmptyCtx

pattern MirAggregateRepr :: () => tp' ~ MirAggregateType => TypeRepr tp'
pattern MirAggregateRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MirAggregateSymbol) -> Just Refl) Empty
 where MirAggregateRepr = IntrinsicRepr (knownSymbol @MirAggregateSymbol) Empty

type family MirAggregateFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MirAggregateFam sym EmptyCtx = MirAggregate sym
  MirAggregateFam sym ctx = TypeError
    ('Text "MirAggregateType expects no arguments, but was given" :<>: 'ShowType ctx)

instance IsSymInterface sym => IntrinsicClass sym MirAggregateSymbol where
  type Intrinsic sym MirAggregateSymbol ctx = MirAggregateFam sym ctx

  muxIntrinsic sym tys _nm Empty = muxMirAggregate sym tys
  muxIntrinsic _sym _tys nm ctx = typeError nm ctx

muxMirAggregateEntry :: forall sym.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Word ->
  Pred sym ->
  Maybe (MirAggregateEntry sym) ->
  Maybe (MirAggregateEntry sym) ->
  IO (MirAggregateEntry sym)
muxMirAggregateEntry sym itefns offset c mEntry1 mEntry2 =
  case (mEntry1, mEntry2) of
    (Nothing, Nothing) -> panic "muxMirAggregateEntry" ["requires at least one entry"]
    (Just entry1, Nothing) -> goOneSided c entry1
    (Nothing, Just entry2) -> do
      c' <- notPred sym c
      goOneSided c' entry2
    (Just entry1, Just entry2) -> goTwoSided entry1 entry2
  where
    goOneSided :: Pred sym -> MirAggregateEntry sym -> IO (MirAggregateEntry sym)
    goOneSided activeCond (MirAggregateEntry sz tpr rv) = do
      rv' <- muxRegForType sym itefns (MaybeRepr tpr) activeCond rv Unassigned
      return $ MirAggregateEntry sz tpr rv'

    goTwoSided :: MirAggregateEntry sym -> MirAggregateEntry sym -> IO (MirAggregateEntry sym)
    goTwoSided (MirAggregateEntry sz tpr rv1) (MirAggregateEntry sz' tpr' rv2) = do
      when (sz' /= sz) $
        die $ "entry size " ++ show sz ++ " != " ++ show sz'
      Refl <- case testEquality tpr tpr' of
        Just x -> return x
        Nothing -> die $ "type mismatch: " ++ show tpr ++ " != " ++ show tpr'
      rv' <- muxRegForType sym itefns (MaybeRepr tpr) c rv1 rv2
      return $ MirAggregateEntry sz tpr rv'

    die :: String -> IO a
    die msg = fail $ "bad MirAggregate merge: offset " ++ show offset ++ ": " ++ msg

muxMirAggregate :: forall sym.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Pred sym ->
  MirAggregate sym ->
  MirAggregate sym ->
  IO (MirAggregate sym)
muxMirAggregate sym itefns c (MirAggregate sz1 m1) (MirAggregate sz2 m2) = do
  when (sz1 /= sz2) $ do
    fail $ "bad MirAggregate merge: size " ++ show sz1 ++ " != " ++ show sz2
  m' <- sequence $ IntMap.mergeWithKey
    (\offset entry1 entry2 -> Just $ muxEntries offset (Just entry1) (Just entry2))
    (IntMap.mapWithKey $ \offset entry1 -> muxEntries offset (Just entry1) Nothing)
    (IntMap.mapWithKey $ \offset entry2 -> muxEntries offset Nothing (Just entry2))
    m1 m2
  return $ MirAggregate sz1 m'
  where
    muxEntries off e1 e2 = muxMirAggregateEntry sym itefns off' c e1 e2
      where off' = fromIntegral off

-- | Return the @(offset, byteWidth, regValue)@ tuple for each entry whose type
-- is @tpr@. When performing a typed access, these are all the entries that the
-- access could apply to.
--
-- Results are returned in ascending order by offset.
mirAgTypedCandidates ::
  forall sym tp.
  TypeRepr tp ->
  MirAggregate sym ->
  [(Word, Word, RegValue sym (MaybeType tp))]
mirAgTypedCandidates tpr (MirAggregate _ m) =
  Maybe.mapMaybe
    (\(o, MirAggregateEntry byteWidth tpr' rv) ->
      case testEquality tpr tpr' of
        Just Refl -> Just (fromIntegral o, byteWidth, rv)
        Nothing -> Nothing)
    (IntMap.toAscList m)


-- | Lift @iteFn@ from type @tp@ to type @MaybeType tp@.
liftIteFnMaybe ::
  forall sym tp.
  IsSymInterface sym =>
  sym ->
  TypeRepr tp ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  Pred sym ->
  RegValue sym (MaybeType tp) ->
  RegValue sym (MaybeType tp) ->
  IO (RegValue sym (MaybeType tp))
liftIteFnMaybe sym _tpr iteFn c x y =
  mergePartial sym (\c' x' y' -> lift $ iteFn c' x' y') c x y

agNoValueAtOffsetSimError :: (Integral a, Show a) => a -> Word -> SimErrorReason
agNoValueAtOffsetSimError off sz =
  ReadBeforeWriteSimError $
    "no value at offset " ++ show off ++ ", in aggregate of size " ++ show sz

agNoValueAtSymbolicOffsetSimError :: Word -> SimErrorReason
agNoValueAtSymbolicOffsetSimError sz =
  ReadBeforeWriteSimError $
    "no value at offset <symbolic>, in aggregate of size " ++ show sz

readMirAggregateWithSymOffset ::
  forall sym bak m tp.
  MonadAssert sym bak m =>
  bak ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  RegValue sym UsizeType ->
  OpSize ->
  TypeRepr tp ->
  MirAggregate sym ->
  MuxLeafT sym m (RegValue sym tp)
readMirAggregateWithSymOffset bak iteFn off readSize tpr ag@(MirAggregate totalSize m)
  | MirAggregateRepr <- tpr =
      readSubaggregateWithSymOffset bak iteFn readSize off ag
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
      case IntMap.lookup off' m of
        Nothing -> leafAbort $ agNoValueAtOffsetSimError off' totalSize
        Just (MirAggregateEntry _ tpr' rv)
          | Just Refl <- testEquality tpr tpr' ->
              leafReadPartExpr bak rv $ agNoValueAtOffsetSimError off' totalSize
          | otherwise -> leafAbort $ GenericSimError $
              "wrong type at offset " ++ show off' ++ ": got " ++ show tpr'
                ++ ", but the requested type is " ++ show tpr

  | otherwise =
      case candidates of
        -- Normally the final "else" branch returns the last candidate.  But if
        -- there are no candidates, we have no element to return, so we have to
        -- special-case it.
        [] -> leafAbort $ GenericSimError $
          -- This error is a bit vague, but since `candidates` only contains
          -- entries that match `tpr`, we don't have a more precise answer.
          "no value or wrong type: the requested type is " ++ show tpr
        (_o0, _w0, rv0) : candidates' -> do
          -- The candidates come from `mirAgTypedCandidates`, which promises to
          -- return elements in ascending order by offset, which satisfies
          -- `offsetInSpan`'s precondition.
          offsetValid <- offsetInSpans sym off (map (\(o, w, _) -> (o, o + w)) candidates)
          leafAssert bak offsetValid $ GenericSimError $
            "no value or wrong type: the requested type is " ++ show tpr
          rv <- liftIO $ foldM
            (\acc (o, _w, rv) -> do
              -- If `off == o`, return `rv`, else `acc`
              offsetEq <- bvEq sym off =<< offsetLit o
              iteFn' offsetEq rv acc)
            rv0 candidates'
          leafReadPartExpr bak rv $ agNoValueAtSymbolicOffsetSimError totalSize

  where
    sym = backendGetSym bak
    candidates = mirAgTypedCandidates tpr ag
    offsetLit = wordLit sym
    iteFn' = liftIteFnMaybe sym tpr iteFn

readSubaggregateWithSymOffset ::
  forall sym bak m.
  MonadAssert sym bak m =>
  bak ->
  (Pred sym -> MirAggregate sym -> MirAggregate sym -> IO (MirAggregate sym)) ->
  OpSize ->
  RegValue sym UsizeType ->
  MirAggregate sym ->
  MuxLeafT sym m (MirAggregate sym)
readSubaggregateWithSymOffset bak iteFn readSize off ag@(MirAggregate sz _)
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
      let err e = leafAbort $ GenericSimError $ "readSubaggregateWithSymOffset: " <> e
      either err pure (readConcrete off' ag)
  | otherwise = do
      liftIO $ foldM
        (\ag' candidateOff -> do
          isTheOffset <- bvEq sym off =<< offsetLit candidateOff
          iteFn isTheOffset (fromRight ag' $ readConcrete candidateOff ag') ag')
        ag
        (init [0 .. sz])
  where
    snd3 (_, x, _) = x
    sym = backendGetSym bak
    offsetLit = wordLit sym

    readConcrete off' ag' = do
      case readSize of
        All ->
          snd <$> mirAggregate_split off' ag'
        Width width ->
          snd3 <$> mirAggregate_split3 off' (off' + width) ag'


adjustMirAggregateWithSymOffset ::
  forall sym bak tp.
  (IsSymBackend sym bak) =>
  bak ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  RegValue sym UsizeType ->
  TypeRepr tp ->
  (RegValue sym tp -> MuxLeafT sym IO (RegValue sym tp)) ->
  MirAggregate sym ->
  MuxLeafT sym IO (MirAggregate sym)
adjustMirAggregateWithSymOffset bak iteFn off tpr f ag@(MirAggregate totalSize m)
  | MirAggregateRepr <- tpr =
      adjustSubaggregateWithSymOffset bak iteFn off f ag
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
      MirAggregateEntry sz tpr' rvPart <- case IntMap.lookup off' m of
        Just x -> return x
        Nothing -> leafAbort $ agNoValueAtOffsetSimError off' totalSize
      Refl <- case testEquality tpr tpr' of
        Just x -> return x
        Nothing -> leafAbort $ GenericSimError $
          "type mismatch at offset " ++ show off' ++ ": got " ++ show tpr'
            ++ ", but the requested type is " ++ show tpr
      rv <- leafReadPartExpr bak rvPart $ agNoValueAtOffsetSimError off' totalSize
      rv' <- f rv
      let rvPart' = justPartExpr sym rv'
      let entry' = MirAggregateEntry sz tpr rvPart'
      let m' = IntMap.insert off' entry' m
      return $ MirAggregate totalSize m'

  | otherwise = do
      let f' rvPart = do
            rv <- leafReadPartExpr bak rvPart $ agNoValueAtSymbolicOffsetSimError totalSize
            rv' <- f rv
            return $ justPartExpr sym rv'

      xs <- forM candidates $ \(o, _w, rvPart) -> do
        hit <- liftIO $ bvEq sym off =<< offsetLit o
        mRvPart' <- subMuxLeafMA bak (f' rvPart) hit
        rvPart'' <- case mRvPart' of
          Just rvPart' -> liftIO $ iteFn' hit rvPart' rvPart
          Nothing -> return rvPart
        return ((o, rvPart''), hit)

      -- `off` must refer to some existing offset with type `tpr`.  Using
      -- `adjust` to create new entries is not allowed.
      hitAny <- offsetInSpans sym off (map (\(o, w, _) -> (o, o + w)) candidates)
      leafAssert bak hitAny $ GenericSimError $
        "no value or wrong type: the requested type is " ++ show tpr

      let newEntryRvs = IntMap.fromAscList $ map (\((o, rv), _) -> (fromIntegral o, rv)) xs
      let newEntries = IntMap.intersectionWith
            (\(MirAggregateEntry sz tpr' _) rv ->
              case testEquality tpr' tpr of
                Just Refl -> MirAggregateEntry sz tpr rv
                Nothing ->
                  panic "adjustMirAggregateWithSymOffset"
                    ["`candidates`/`xs` should only contain entries of type `tpr`"])
            m newEntryRvs
      let m' = IntMap.union newEntries m
      return $ MirAggregate totalSize m'

  where
    sym = backendGetSym bak
    candidates = mirAgTypedCandidates tpr ag
    offsetLit = wordLit sym
    iteFn' = liftIteFnMaybe sym tpr iteFn

adjustSubaggregateWithSymOffset ::
  forall sym bak.
  (IsSymBackend sym bak) =>
  bak ->
  (Pred sym -> MirAggregate sym -> MirAggregate sym -> IO (MirAggregate sym)) ->
  RegValue sym UsizeType ->
  (MirAggregate sym -> MuxLeafT sym IO (MirAggregate sym)) ->
  MirAggregate sym ->
  MuxLeafT sym IO (MirAggregate sym)
adjustSubaggregateWithSymOffset bak iteFn off f ag@(MirAggregate sz _)
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off =
      adjustConcrete off'
  | otherwise = do
      foldM
        (\ag' candidateOff -> do
          isTheOffset <- liftIO $ bvEq sym off =<< offsetLit candidateOff
          subAg <- adjustConcrete candidateOff
          liftIO $ iteFn isTheOffset subAg ag')
        ag
        (init [0 .. sz])
  where
    adjustConcrete off' = do
      case mirAggregate_split off' ag of
        Right (MirAggregate leftSz leftAg, r@(MirAggregate rightSz _rightAg)) -> do
          MirAggregate rightSz' rightAg' <- f r
          let rightAg'' = IntMap.mapKeysMonotonic (\o -> o + fromIntegral off') rightAg'
          when (rightSz /= rightSz') $
            panic "adjustSubaggregateWithSymOffset"
              [ "adjusting function changed aggregate size"
              , "was " <> show rightSz <> ", became " <> show rightSz'
              ]
          unless (IntMap.disjoint leftAg rightAg'') $
            panic "adjustSubaggregateWithSymOffset"
              [ "aggregates weren't disjoint" ]
          pure $ MirAggregate (leftSz + rightSz) (rightAg'' <> leftAg)
        Left err -> leafAbort $ GenericSimError $
          "adjustSubaggregateWithSymOffset: " <> err

    sym = backendGetSym bak
    offsetLit = wordLit sym

-- | Given a list of valid entry spans @(fromOffset, toOffset)@ in this
-- aggregate, create a predicate that the provided offset appears among their
-- @fromOffset@ values.
--
-- Precondition: the candidate spans are sorted in ascending order by
-- starting offset.
offsetInSpans ::
  forall sym m.
  (IsSymInterface sym, MonadIO m) =>
  sym ->
  RegValue sym UsizeType ->
  [(Word, Word)] ->
  MuxLeafT sym m (SymExpr sym BaseBoolType)
offsetInSpans sym off spans = liftIO $ do
  -- Consider this struct:
  -- ```rs
  -- #[repr(C)]
  -- struct Foo {
  --   a: u16,
  --   b: [u8; 2],
  --   c: u16,
  --   d: [u8; 2],
  --   e: [u16; 3],
  -- }
  -- ```
  --
  -- We have a symbolic offset (`off`) and a concrete type (`tpr`), and need
  -- to determine whether an element of type `tpr` exists at `off` in the
  -- aggregate.
  --
  -- Suppose `tpr` is `u16`, and that the aggregate representing the struct
  -- has been flattened. The type-correct offsets of `u16`s are those of `a`
  -- (0), `c` (4), and each element of `e` (8, 10, and 12).
  --
  -- We start by partitioning these offsets into contiguous `runs` (of which
  -- there is one, from 8 to 14, exclusive of 14) and discrete `offsets` (of
  -- which there are two, 0 and 4).
  let (offsets, runs) = foldRuns spans

  -- For `offsets`, we construct a simplistic predicate: for each offset, is
  -- `off` equal to it? For our example, this will yield the predicate
  -- (`off` == 0 || `off` == 4).
  offsetsPred <- orPredBy (\o -> bvEq sym off =<< wordLit sym o) offsets

  -- For `runs`, we construct a more efficient predicate: for each run, is
  -- `off` within the bounds of the run, and does the stride (i.e. the width
  -- of a single `u16`) evenly divide it? For our example, this will yield
  -- the predicate (`off` >= 8 && `off` < 14 && `off` % 2 == 0). See
  -- `runPred`, below.
  runsPred <- orPredBy runPred runs

  -- If either predicate holds, the offset is a valid index into this
  -- aggregate.
  orPred sym runsPred offsetsPred
  where
    orPredBy :: (a -> IO (Pred sym)) -> [a] -> IO (Pred sym)
    orPredBy f xs = do
      xsPreds <- mapM f xs
      foldM (orPred sym) (falsePred sym) xsPreds

    -- Whether `off` appears in the given `Run` of aggregate elements.
    runPred :: Run -> IO (Pred sym)
    runPred run = do
      -- Note that we're able to use the unique stride as a proxy for element
      -- type width, since the widths of `Run` elements are exactly those of the
      -- original aggregate entry widths.
      let tyWidth = rStride run

      -- off >= rFrom
      afterBeginning <- bvUge sym off =<< wordLit sym (rFrom run)

      -- off < rTo (not `<=` because `rTo` is exclusive)
      beforeEnd <- bvUlt sym off =<< wordLit sym (rTo run)

      inBounds <- andPred sym afterBeginning beforeEnd

      -- (off - rFrom) `mod` tyWidth == 0
      relativeOff <- bvSub sym off =<< wordLit sym (rFrom run)
      atTyBoundary <- case asAffineVar relativeOff of
        -- When `asAffineVar relativeOff` is `Just (c, r, o)`, then we know that
        -- `relativeOff == c * r + o`, with `c` and `o` being concrete. Putting
        -- `relativeOff` in this form lets us try to check divisibility
        -- concretely: if `c % tyWidth == 0` and `o % tyWidth == 0`, then
        -- `(c * r + o) % tyWidth == 0`.
        --
        -- Since we often generate indexing expressions by multiplying an index
        -- by an element size, this optimization applies often enough to be
        -- useful.
        Just (fromConcreteBV -> c, _r, fromConcreteBV -> o)
          | let tyWidthBV = BV.mkBV knownRepr (toInteger tyWidth),
            BV.BV 0 <- BV.urem c tyWidthBV,
            BV.BV 0 <- BV.urem o tyWidthBV ->
              pure $ truePred sym
        -- If the expression wasn't in an affine form, resort to a symbolic
        -- divisibility check instead.
        _ -> do
          offModWidth <- bvUrem sym relativeOff =<< wordLit sym tyWidth
          bvEq sym offModWidth =<< wordLit sym 0

      andPred sym inBounds atTyBoundary

-- | Given a sorted list of element "spans", represented as @(fromOffset,
-- toOffset)@ pairs (where an element's bytes occupy all offsets in the
-- half-open range @[fromOffset, toOffset)@), find and return all contiguous
-- sequences of two or more elements of the same width and the @fromOffset@s all
-- other elements.
--
-- For example, @foldRuns [(0, 2), (4, 8), (8, 10), (10, 12), (12, 14)]@
-- should yield @([0, 4], [Run {rFrom = 8, rTo = 14, rStride = 2}])@. The
-- last three spans are adjacent to one another and are the same width, so
-- they are folded into a `Run` (to 14, exclusive of 14). The first two
-- spans are not contiguous, so they are returned as discrete offsets.
foldRuns :: [(Word, Word)] -> ([Word], [Run])
foldRuns spans =
  let (offsets, runs) = foldRuns' [] [] spans
    in (reverse offsets, reverse runs)
  where
    foldRuns' :: [Word] -> [Run] -> [(Word, Word)] -> ([Word], [Run])
    foldRuns' offsets runs spans_ =
      case (runs, spans_) of
        -- Done
        (_, []) ->
          (offsets, runs)
        -- Add to an existing run
        (r : rs, s : ss)
          | Just r' <- addToRun r s ->
              foldRuns' offsets (r' : rs) ss
        -- Add a new run
        (_, s1 : s2 : ss)
          | Just r <- mkRun s1 s2 ->
              foldRuns' offsets (r : runs) ss
        -- Add a new offset
        (_, (sFrom, _) : ss) ->
          foldRuns' (sFrom : offsets) runs ss

-- | Attempt to add the given span to the end of the given run.
addToRun :: Run -> (Word, Word) -> Maybe Run
addToRun run (sFrom, sTo)
  | rTo run == sFrom,
    rStride run == sTo - sFrom =
      Just (Run (rFrom run) sTo (rStride run))
  | otherwise =
      Nothing

-- | Attempt to make a new run from two spans, yielding a run if they are the
-- same width and are adjacent.
mkRun :: (Word, Word) -> (Word, Word) -> Maybe Run
mkRun (s1From, s1To) s2 =
  addToRun (Run s1From s1To (s1To - s1From)) s2

-- | Represents a contiguous "run" of aggregate elements of the same width.
data Run = Run
  { -- | Starting at (and inclusive of) this position
    rFrom :: !Word,
    -- | Ending at (and exclusive of) this position
    rTo :: !Word,
    -- | The spacing between the elements in this run
    rStride :: !Word
  }
  deriving (Show)


mirAggregate_entries :: sym -> MirAggregate sym -> [(Word, MirAggregateEntry sym)]
mirAggregate_entries _sym (MirAggregate _totalSize m) =
  [(fromIntegral off, entry) | (off, entry) <- IntMap.toList m]

foldMWithKey :: Monad m => (b -> Int -> a -> m b) -> b -> IntMap a -> m b
foldMWithKey f z m = IntMap.foldlWithKey' f' (pure z) m
  where
    f' accM key val = do
      acc <- accM
      f acc key val

mirAggregate_insert ::
  (IsSymInterface sym) =>
  Word ->
  MirAggregateEntry sym ->
  MirAggregate sym ->
  Either String (MirAggregate sym)
mirAggregate_insert outerAgOff (MirAggregateEntry entrySz MirAggregateRepr entryP) outerAg = case entryP of
  Unassigned -> pure outerAg
  PE p (MirAggregate innerAgSz innerAgEntries) -> case asConstantPred p of
    _ | innerAgSz /= entrySz -> Left $
      "mirAggregate_insert: when adding a `MirAggregate` as an entry, " <>
      "the `MirAggregateEntry`-derived size was " <> show entrySz <> ", " <>
      "but the `MirAggregate` value had size " <> show innerAgSz
    Just False ->
      pure outerAg
    Just True -> do
      let addEntry ag (fromIntegral -> entryOff) entry =
            mirAggregate_insert (outerAgOff + entryOff) entry ag
      foldMWithKey addEntry outerAg innerAgEntries
    -- Note: this case doesn't seem to show up in practice, but if it does,
    -- consider lifting this function to a monadic context in which it can
    -- manipulate predicates, so that it can add entries the conjunction of
    -- their own individual predicates and the overarching entry's predicate,
    -- `entryP`.
    Nothing -> Left $
      "mirAggregate_insert: unsupported: `MirAggregate` as entry with symbolic predicate"
mirAggregate_insert off entry@(MirAggregateEntry sz tpr _) (MirAggregate totalSize m) = do
  -- For now, we require that either there are no entries overlapping the byte
  -- range `off .. off + sz`, or there is an entry covering exactly that range
  -- whose type matches `tpr`.  In the future we could relax this by deleting
  -- existing entries that are fully covered by the new one (though this could
  -- cause trouble when the old and new `MirAggregate` get muxed together).
  case IntMap.lookupLT (fromIntegral $ off + sz) m of
    Nothing -> return ()
    Just (fromIntegral -> off', MirAggregateEntry sz' tpr' _)
      | off' == off -> do
          case testEquality tpr tpr' of
            Nothing -> die $ "type mismatch at offset " ++ show off ++ ": "
              ++ show tpr ++ " != " ++ show tpr'
            Just _ -> return ()
          when (sz /= sz') $
            die $ "size mismatch at offset " ++ show off ++ ": "
              ++ show sz ++ " != " ++ show sz'
      -- Existing entry's range comes entirely before the new one, so there is
      -- no overlap.
      | off' + sz' <= off -> return ()
      | otherwise -> die $ "partial overlap: " ++ show off ++ ".." ++ show (off + sz)
          ++ " vs " ++ show off' ++ ".." ++ show (off' + sz')
  -- New entry must not extend past `0 .. totalSize`.
  when (off + sz > totalSize) $
    die $ "entry out of range: covers " ++ show off ++ ".." ++ show (off + sz)
      ++ ", but total size is " ++ show totalSize
  -- All checks passed - insert the new entry
  return $ MirAggregate totalSize $ IntMap.insert (fromIntegral off) entry m
  where
    die msg = Left $ "bad MirAggregate insert: " ++ msg

writeMirAggregateWithSymOffset ::
  forall sym bak tp.
  (IsSymBackend sym bak) =>
  bak ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  RegValue sym UsizeType ->
  OpSize ->
  TypeRepr tp ->
  RegValue sym tp ->
  MirAggregate sym ->
  MuxLeafT sym IO (MirAggregate sym)
writeMirAggregateWithSymOffset bak iteFn off writeSize tpr val ag
  -- Concrete case: insert a new entry or overwrite an existing one with
  -- `mirAggregate_insert`.
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
    entry <- case (writeSize, tpr) of
      (All, MirAggregateRepr) -> do
        let MirAggregate subAgSz _ = val
        pure $ MirAggregateEntry subAgSz tpr $ justPartExpr sym val
      (All, _) ->
        die "unsupported: writing non-aggregate value of unknown/unspecified size"
      (Width w, _) ->
        pure $ MirAggregateEntry w tpr $ justPartExpr sym val
    case mirAggregate_insert off' entry ag of
      Left err -> leafAbort $ GenericSimError err
      Right ag' -> return ag'
  -- Symbolic case: overwrite an existing entry with `adjustMirAggregateWithSymOffset`.
  -- Creating a new entry at a symbolic offset is not allowed.
  | otherwise = do
      adjustMirAggregateWithSymOffset bak iteFn off tpr (\_oldVal -> return val) ag

  where
    sym = backendGetSym bak
    die msg = leafAbort $ GenericSimError $ "writeMirAggregateWithSymOffset: " <> msg

-- | Look up a value in a `MirAggregate`.  This returns @Right maybeVal@ if it
-- finds a value at the requested offset, @Right Unassigned@ if the offset is
-- valid but there's no entry there, and @Left errorMessage@ if offset is
-- invalid (in the middle of some entry) or the type @tpr@ is incorrect.
mirAggregate_lookup ::
  Word ->
  TypeRepr tp ->
  MirAggregate sym ->
  Either String (RegValue sym (MaybeType tp))
mirAggregate_lookup off tpr (MirAggregate totalSize m) = do
  case IntMap.lookupLE (fromIntegral off) m of
    _ | off >= totalSize ->
      die $ "offset " ++ show off ++ " is out of range "
        ++ "for aggregate total size " ++ show totalSize
    Nothing -> Right Unassigned
    Just (fromIntegral -> off', MirAggregateEntry sz' tpr' rv)
      | off' == off -> do
          case testEquality tpr tpr' of
            Nothing -> die $ "type mismatch at offset " ++ show off ++ ": "
              ++ show tpr ++ " != " ++ show tpr'
            Just Refl -> Right rv
      -- Existing entry's range comes entirely before the new one, so there is
      -- no overlap (and no value at `off`).
      | off' + sz' <= off -> Right Unassigned
      | otherwise -> die $ "partial overlap: " ++ show off
          ++ " vs " ++ show off' ++ ".." ++ show (off' + sz')
  where
    die msg = Left $ "bad MirAggregate lookup: " ++ msg

-- | Resize a `MirAggregate`.  If the new size is larger, the extra space will
-- be left uninitialized.  If the new size is smaller, any entries that extend
-- past the new end point will be discarded.
resizeMirAggregate ::
  MirAggregate sym ->
  Word ->
  MirAggregate sym
resizeMirAggregate (MirAggregate totalSize m) newSize
  | newSize >= totalSize = MirAggregate newSize m
  | otherwise = MirAggregate newSize m'
  where
    m' = IntMap.filterWithKey
      (\off (MirAggregateEntry sz _ _) -> fromIntegral off + sz <= newSize)
      m

-- | Split a `MirAggregate` in two at a given offset.  The first output
-- contains all the entries below the split point, and the second contains all
-- the entries above.  Offsets in the second output are shifted downward, so an
-- entry at @off@ in the input will be at offset zero in the second output.
--
-- Returns `Left` if any entry spans the split point, or if the split point is
-- out of range.
mirAggregate_split ::
  Word ->
  MirAggregate sym ->
  Either String (MirAggregate sym, MirAggregate sym)
mirAggregate_split off (MirAggregate totalSize m) = do
  when (off > totalSize) $ Left $
    "offset " ++ show off ++ " out of bounds for aggregate of size " ++ show totalSize
  let (m1, m2) = splitLE (fromIntegral off) m
  -- Last entry in `m1` must not go past `off`
  case IntMap.lookupMax m1 of
    Just (entryOff, MirAggregateEntry entrySz _ _)
      | fromIntegral entryOff + entrySz > off -> Left $
        "entry of size " ++ show entrySz ++ " at " ++ show entryOff
          ++ " spans split boundary at " ++ show off
    _ -> return ()
  -- Adjust offsets downward, so an entry at `off` in the input aggregate will
  -- be at 0 in the second output.
  let m2' = IntMap.mapKeysMonotonic (\x -> x - fromIntegral off) m2
  return (MirAggregate off m1, MirAggregate (totalSize - off) m2')
  where
    -- | Like `IntMap.split`, but the maps contain keys @< k@ and @>= k@,
    -- instead of @< k@ and @> k@.
    splitLE :: Int -> IntMap a -> (IntMap a, IntMap a)
    splitLE k m' =
      let (before, exact, after) = IntMap.splitLookup k m'
          after' = case exact of
            Just v -> IntMap.insert k v after
            Nothing -> after
      in (before, after')

-- | Split a `MirAggregate` into three parts: the part below @off1@, the part
-- between @off1@ and @off2@, and the part above @off2@.  Offsets in the upper
-- parts are shifted down, so entries at @0@/@off1@/@off2@ in the input will
-- each be at offset zero in their respective outputs.
--
-- Returns `Left` if either offset is out of bounds, if @off1 > off2@, or if an
-- entry in the input aggregate spans across either of the two split points.
mirAggregate_split3 ::
  Word ->
  Word ->
  MirAggregate sym ->
  Either String (MirAggregate sym, MirAggregate sym, MirAggregate sym)
mirAggregate_split3 off1 off2 ag = do
  (ag12, ag3) <- mirAggregate_split off2 ag
  (ag1, ag2) <- mirAggregate_split off1 ag12
  return (ag1, ag2, ag3)

-- | Extract a chunk from a `MirAggregate`.  This returns a new `MirAggregate`
-- containing only the entries that fall between the start and the end of the
-- chunk.  Returns `Left` if some entries cross the chunk boundary, or if the
-- chunk extends beyond the end of the input aggregate.
--
-- We expect the input to not contain any zero-sized entries, but this is not
-- enforced.  In the current implementation, zero-sized entries at the start
-- of the chunk will be included in the chunk, but zero-sized entries at the
-- end will not.  Eventually we'd like to enforce the invariant that
-- `MirAggregate`s never contain zero-sized entries at all, at which point this
-- detail will be irrelevant.
mirAggregate_chunk ::
  -- | The starting offset of the chunk
  Word ->
  -- | The size of the chunk in bytes
  Word ->
  MirAggregate sym ->
  Either String (MirAggregate sym)
mirAggregate_chunk off chunkSize ag@(MirAggregate totalSize _) = do
  when (off > totalSize) $ Left $
    "offset " ++ show off ++ " out of bounds for aggregate of size " ++ show totalSize
  -- Check for `off + chunkSize > totalSize`, avoiding overflow.
  when (chunkSize > totalSize - off) $ Left $
    "chunk size " ++ show chunkSize ++ " at offset " ++ show off
      ++ " is too big for aggregate of size " ++ show totalSize
  (_, chunkAg, _) <- mirAggregate_split3 off (off + chunkSize) ag
  return chunkAg

-- | Split a `MirAggregate` into an array of equal-sized chunks.
mirAggregate_toChunks ::
  IsSymInterface sym =>
  sym ->
  -- | Starting offset within the input aggregate
  Word ->
  -- | Size in bytes of each chunk
  Word ->
  -- | Number of chunks to produce
  Word ->
  -- | Input aggregate
  MirAggregate sym ->
  Either String (MirAggregate sym)
mirAggregate_toChunks sym off chunkSize numChunks ag = do
  entries <- forM (init [0 .. numChunks]) $ \i -> do
    chunk <- mirAggregate_chunk (off + i * chunkSize) chunkSize ag
    return (fromIntegral $ i * chunkSize,
      MirAggregateEntry chunkSize MirAggregateRepr (justPartExpr sym chunk))
  return $ MirAggregate (numChunks * chunkSize) (IntMap.fromAscList entries)

-- | Concatenate two `MirAggregate`s, producing a new aggregate with all the
-- entries of the first followed by all the entries of the second.  The entries
-- of the second aggregate are offset by the size of the first.
mirAggregate_concat ::
  MirAggregate sym ->
  MirAggregate sym ->
  MirAggregate sym
mirAggregate_concat (MirAggregate totalSize1 m1) (MirAggregate totalSize2 m2) =
  let m' = m1 <> IntMap.mapKeysMonotonic (+ fromIntegral totalSize1) m2
  in MirAggregate (totalSize1 + totalSize2) m'

-- | Merge an array of chunks into a single `MirAggregate`.  Each entry of
-- the input aggregate should be a `MirAggregate`; the entries of that
-- sub-aggregate will be placed in the output starting at an offset computed
-- from the offset of the sub-aggregate.  Returns `Left` if some aggregates in
-- the input would cover overlapping ranges.
--
-- Returns `Left` if any of the sub-aggregates has a zero-sized entry at the
-- end of its range (i.e. with @off == totalSize@).  This check can be removed
-- once we properly enforce the invariant that `MirAggregate`s must not contain
-- zero-sized entries.
mirAggregate_fromChunks ::
  forall sym.
  IsSymInterface sym =>
  sym ->
  -- | Input aggregate
  MirAggregate sym ->
  IO (Either String (MirAggregate sym))
mirAggregate_fromChunks sym chunkedAg@(MirAggregate chunkedTotalSize _) = runExceptT $ do
  let chunkedEntries = mirAggregate_entries sym chunkedAg
  -- For each initialized chunk, we collect:
  -- 1. The offset of the chunk within the outer aggregate
  -- 2. The "outer size" of the chunk, meaning the size of its entry within the
  --    outer aggregate
  -- 3. The predicate under which the chunk is initialized (each chunk, like
  --    any aggregate entry, may be conditionally uninitialized)
  -- 4. The map of offsets and entries within the aggrgegate.
  chunkParts <- do
    let f :: MonadError String m => (Word, MirAggregateEntry sym) ->
          m (Maybe (Word, Word, Pred sym, IntMap (MirAggregateEntry sym)))
        f (off, MirAggregateEntry chunkEntrySize tpr rv) = do
          case tpr of
            MirAggregateRepr ->
              case rv of
                Unassigned -> return Nothing
                PE outerPred (MirAggregate chunkAgSize m) ->
                  if chunkEntrySize /= chunkAgSize
                    then panic "mirAggregate_fromChunks"
                          ["chunk entry size " <> show chunkEntrySize <> " does not match its aggregate's size " <> show chunkAgSize ]
                    else return $ Just (off, chunkAgSize, outerPred, m)
            _ -> throwError $
              "expected all chunks to be MirAggregateRepr, but got " ++ show tpr
                ++ " (size " ++ show chunkEntrySize ++ ") at offset " ++ show off
    liftM Maybe.catMaybes $ mapM f chunkedEntries

  -- Check for disjointness.  `chunkParts` is sorted by starting offset, so we
  -- can just compare pairs of consecutive elements.
  forM_ (zip chunkParts (Prelude.drop 1 chunkParts)) $
    \((off1, sz1, _, _), (off2, sz2, _, _)) -> do
      when (off1 > off2 || off2 - off1 < sz1) $ panic "mirAggregate_fromChunks"
        [ "overlapping chunks"
        , "at " ++ show off1 ++ " .. " ++ show (off1 + sz1)
        , "and " ++ show off2 ++ " .. " ++ show (off2 + sz2)
        ]

  ms <- forM chunkParts $ \(off, sz, outerPred, m) -> do
    -- Check that there are no zero-sized entries at the end.
    when (IntMap.member (fromIntegral sz) m) $ throwError $
      "unsupported zero-sized entry at chunk end, in chunk at " ++ show off

    -- Check that the chunk doesn't extend past the expected end of the
    -- combined aggregate.
    let start = off
    let end = start + sz
    when (end > chunkedTotalSize) $ throwError $
      "chunk at " ++ show off ++ " extends past end: covers "
        ++ show start ++ " .. " ++ show end
        ++ " in output of size " ++ show chunkedTotalSize

    -- Entries within each aggregate are valid only if the outer aggregate is
    -- itself valid.
    let restrictPred :: MonadIO m => PartExpr (Pred sym) a ->
          m (PartExpr (Pred sym) a)
        restrictPred Unassigned = return Unassigned
        restrictPred (PE innerPred rv) = do
          restrictedPred <- liftIO $ andPred sym outerPred innerPred
          return $ PE restrictedPred rv
    m' <- forM m $ \(MirAggregateEntry sz' tpr rv) ->
      MirAggregateEntry sz' tpr <$> restrictPred rv

    -- Adjust offsets.
    return $ IntMap.mapKeysMonotonic (+ fromIntegral start) m'

  let combinedM = mconcat ms
  return $ MirAggregate chunkedTotalSize combinedM

concreteAllocSize ::
    IsSymBackend sym bak =>
    bak ->
    RegValue sym UsizeType ->
    IO Integer
concreteAllocSize bak szSym =
    case asBV szSym of
        Just x -> return (BV.asUnsigned x)
        Nothing -> addFailedAssertion bak $ Unsupported callStack $
            "Attempted to create allocation of symbolic size"

mirAggregate_uninitIO ::
    IsSymBackend sym bak =>
    bak ->
    RegValue sym UsizeType ->
    IO (RegValue sym MirAggregateType)
mirAggregate_uninitIO bak szSym = do
  sz <- concreteAllocSize bak szSym
  return $ MirAggregate (fromIntegral sz) mempty

-- | Construct a 'MirAggregate' value representing a zero-sized type (ZST) such
-- as an empty tuple or array.
mirAggregate_zstSim :: OverrideSim p sym ext rtp args ret (MirAggregate sym)
mirAggregate_zstSim = liftIO mirAggregate_zstIO

-- | Construct a 'MirAggregate' value representing a zero-sized type (ZST) such
-- as an empty tuple or array.
mirAggregate_zstIO :: IO (MirAggregate sym)
mirAggregate_zstIO = pure $ MirAggregate 0 mempty

mirAggregate_replicateIO ::
    IsSymBackend sym bak =>
    bak ->
    Word ->
    TypeRepr tp ->
    RegValue sym tp ->
    RegValue sym UsizeType ->
    IO (RegValue sym MirAggregateType)
mirAggregate_replicateIO bak elemSz elemTpr elemVal lenSym = do
  let sym = backendGetSym bak
  len <- concreteAllocSize bak lenSym
  let totalSize = fromIntegral len * elemSz
  let ag = MirAggregate totalSize mempty
  let entries =
        [(fromIntegral i * elemSz,
          MirAggregateEntry elemSz elemTpr (justPartExpr sym elemVal))
        | i <- init [0 .. len]]
  let insert ag' (off, entry) = mirAggregate_insert off entry ag'
  case foldM insert ag entries of
    Right ag' ->
      pure ag'
    Left err ->
      addFailedAssertion bak $ GenericSimError $ "mirAggregate_replicateIO: " <> err

mirAggregate_resizeIO ::
    IsSymBackend sym bak =>
    bak ->
    RegValue sym MirAggregateType ->
    RegValue sym UsizeType ->
    IO (RegValue sym MirAggregateType)
mirAggregate_resizeIO bak ag szSym = do
  sz <- concreteAllocSize bak szSym
  return $ resizeMirAggregate ag (fromIntegral sz)

mirAggregate_getIO ::
    IsSymBackend sym bak =>
    bak ->
    Word ->
    Word ->
    TypeRepr tp ->
    MirAggregate sym ->
    IO (RegValue sym tp)
mirAggregate_getIO bak off sz MirAggregateRepr ag =
  case mirAggregate_split3 off (off + sz) ag of
    Right (_toLeft, mid, _toRight) -> pure mid
    Left err -> addFailedAssertion bak $ GenericSimError $ "mirAggregate_getIO: " <> err
mirAggregate_getIO bak off sz tpr (MirAggregate _ m) = do
  -- TODO: deduplicate logic between this and readMirAg* concrete case?
  MirAggregateEntry sz' tpr' rvPart <- case IntMap.lookup (fromIntegral off) m of
    Just x -> return x
    Nothing -> addFailedAssertion bak $ ReadBeforeWriteSimError $
      "getIO " ++ show off ++ " " ++ show sz ++ " " ++ show tpr ++ " " ++ show m ++ ": no entry at offset " ++ show off
  Refl <- case testEquality tpr tpr' of
    Just x -> return x
    Nothing -> addFailedAssertion bak $ GenericSimError $
      "type mismatch at offset " ++ show off ++ ": " ++ show tpr ++ " != " ++ show tpr'
  when (sz /= sz') $
    addFailedAssertion bak $ GenericSimError $
      "size mismatch at offset " ++ show off ++ ": " ++ show sz ++ " != " ++ show sz'
  rv <- readPartExpr bak rvPart $ ReadBeforeWriteSimError $
    "uninitialized entry at offset " ++ show off
  return rv

mirAggregate_setIO ::
    IsSymBackend sym bak =>
    bak ->
    Word ->
    Word ->
    TypeRepr tp ->
    RegValue sym tp ->
    MirAggregate sym ->
    IO (MirAggregate sym)
mirAggregate_setIO bak off sz tpr rv ag = do
  let sym = backendGetSym bak
  -- Entries are partial, but `mirAggregate_set` always inserts `Just`.  The
  -- `Nothing` case arises only from muxing.
  let rv' = justPartExpr sym rv
  let entry = MirAggregateEntry sz tpr rv'
  case mirAggregate_insert off entry ag of
    Left err -> fail err
    Right ag' -> return ag'
