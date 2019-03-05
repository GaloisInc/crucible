{-|
Module      : What4.Expr.UnaryBV
Copyright   : (c) Galois, Inc 2015-2016
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module defines a data structure for representing a symbolic bitvector
using a form of "unary" representation.

The idea behind this representation is that we associate a predicate to
each possible value of the bitvector that is true if the symbolic value
is less than or equal to the possible value.

As an example, if we had the unary term 'x' equal to
"{ 0 -> false, 1 -> p, 2 -> q, 3 -> t }", then 'x' cannot be '0', has the
value '1' if 'p' is true, the value '2' if 'q & not p' is true, and '3' if
'not q' is true.  By construction, we should have that 'p => q'.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
#if MIN_VERSION_base(4,9,0)
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
module What4.Expr.UnaryBV
  ( UnaryBV
  , width
  , size
  , traversePreds
  , constant
  , asConstant
  , unsignedEntries
  , unsignedRanges
  , evaluate
  , sym_evaluate
  , instantiate
  , domain
    -- * Operations
  , add
  , neg
  , mux
  , eq
  , slt
  , ult
  , uext
  , sext
  , trunc
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad
import           Data.Bits
import           Data.Hashable
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import qualified GHC.TypeNats as Type

import           What4.BaseTypes
import           What4.Interface
import           What4.Utils.BVDomain (BVDomain)
import qualified What4.Utils.BVDomain as BVD

import qualified Data.Map.Strict as Map

type IntMap = Map.Map Integer

-- | @splitLeq k m@ returns a pair @(l,h)@ where @l@ contains
-- all the bindings with a key less than or equal to @k@, and
-- @h@ contains the ones greater than @k@.
splitLeq :: Integer -> IntMap a -> (IntMap a, IntMap a)
splitLeq k m =
  case Map.splitLookup k m of
    (l, Nothing, h) -> (l,h)
    (l, Just v, h) -> (Map.insert k v l, h)

-- | Split a map into a lower bound, midpoint, and upperbound if non-empty.
splitEntry :: IntMap a -> Maybe (IntMap a, (Integer, a), IntMap a)
splitEntry m0 = go (Map.splitRoot m0)
  where go [] = Nothing
        go [m] =
          case Map.minViewWithKey m of
            Nothing -> Nothing
            Just (p, h) -> Just (Map.empty, p, h)
        go (l:m:h) =
          case Map.minViewWithKey m of
            Nothing -> go (l:h)
            Just (p, m') | Map.null m' -> Just (l, p, Map.unions h)
                         | otherwise   -> Just (l, p, Map.unions (m':h))

-- | This function eliminates entries where the predicate has the same
-- value.
stripDuplicatePreds :: Eq p => [(Integer,p)] -> [(Integer,p)]
stripDuplicatePreds ((l,p):(h,q):r)
  | p == q = stripDuplicatePreds ((l,p):r)
  | otherwise = (l,p):stripDuplicatePreds ((h,q):r)
stripDuplicatePreds [p] = [p]
stripDuplicatePreds [] = []

------------------------------------------------------------------------
-- UnaryBV

-- | A unary bitvector encoding where the map contains predicates
-- such as @u^.unaryBVMap^.at i@ holds iff the value represented by @u@
-- is less than or equal to @i@.
--
-- The map stored in the representation should always have a single element,
-- and the largest integer stored in the map should be associated with a
-- predicate representing "true".  This means that if the map contains only
-- a single binding, then it represents a constant.
data UnaryBV p (n::Type.Nat)
   = UnaryBV { width :: !(NatRepr n)
             , unaryBVMap :: !(IntMap p)
             }

-- | Returns the number of distinct values that this could be.
size :: UnaryBV p n -> Int
size x = Map.size (unaryBVMap x)

traversePreds :: Traversal (UnaryBV p n) (UnaryBV q n) p q
traversePreds f (UnaryBV w m) = UnaryBV w <$> traverse f m

instance Eq p => TestEquality (UnaryBV p) where
  testEquality x y = do
    Refl <- testEquality (width x) (width y)
    if unaryBVMap x == unaryBVMap y then
      Just Refl
    else
      Nothing

instance Hashable p => Hashable (UnaryBV p n) where
  hashWithSalt s0 u = Map.foldlWithKey' go s0 (unaryBVMap u)
    where go s k e = hashWithSalt (hashWithSalt s k) e

-- | Create a unary bitvector term from a constant.
constant :: IsExprBuilder sym
          => sym
          -> NatRepr n
          -> Integer
          -> UnaryBV (Pred sym) n
constant sym w v = UnaryBV w (Map.singleton v' (truePred sym))
  where v' = toUnsigned w v

-- | Create a unary bitvector term from a constant.
asConstant :: IsExpr p => UnaryBV (p BaseBoolType) w -> Maybe Integer
asConstant x
  | size x == 1, [(v,_)] <- Map.toList (unaryBVMap x) = Just v
  | otherwise = Nothing

-- | @unsignedRanges v@ returns a set of predicates and ranges
-- where we know that for each entry @(p,l,h)@ and each value
-- @i : l <= i & i <= h@:
--   @p@ iff. @v <= i@
unsignedRanges :: UnaryBV p n
               -> [(p, Integer, Integer)]
unsignedRanges v =
    case Map.toList (unaryBVMap v) of
      [] -> error "internal: unsignedRanges given illegal UnaryBV"
      l -> go l
  where w :: Integer
        w = maxUnsigned (width v)

        next :: [(Integer,p)] -> Integer
        next ((h,_):_) = h-1
        next [] = w

        go :: [(Integer, p)] -> [(p, Integer, Integer)]
        go [] = []
        go ((l,p):rest) = (p,l,next rest) : go rest

unsignedEntries :: (1 <= n)
                => UnaryBV p n
                -> [(Integer, p)]
unsignedEntries b = Map.toList (unaryBVMap b)

-- | Evaluate a unary bitvector as an integer given an evaluation function.
evaluate :: Monad m => (p -> m Bool) -> UnaryBV p n -> m Integer
evaluate f0 u = go f0 (unaryBVMap u) (maxUnsigned (width u))
  where go :: Monad m => (p -> m Bool) -> IntMap p -> Integer -> m Integer
        go f m bnd =
          case splitEntry m of
            Nothing -> return bnd
            Just (l,(k,v),h) -> do
              b <- f v
              case b of
                -- value <= k
                True -> go f l k
                -- value > k
                False -> go f h bnd

-- | Evaluate a unary bitvector given an evaluation function.
--
-- This function is used to convert a unary bitvector into some other representation
-- such as a binary bitvector or vector of bits.
--
-- It is polymorphic over the result type 'r', and requires functions for manipulating
-- values of type 'r' to construct it.
sym_evaluate :: (Applicative m, Monad m)
             => (Integer -> m r)
                -- ^ Function for mapping an integer to its bitvector
                -- representation.
             -> (p -> r -> r -> m r)
                -- ^ Function for performing an 'ite' expression on 'r'.
             -> UnaryBV p n
                -- ^ Unary bitvector to evaluate.
             -> m r
sym_evaluate cns0 ite0 u = go cns0 ite0 (unaryBVMap u) (maxUnsigned (width u))
  where go :: (Applicative m, Monad m)
           => (Integer -> m r)
           -> (p -> r -> r -> m r)
           -> IntMap p
           -> Integer
           -> m r
        go cns ite m bnd =
          case splitEntry m of
            Nothing -> cns bnd
            Just (l,(k,v),h) -> do
              join $ ite v <$> go cns ite l k <*> go cns ite h bnd

-- | This function instantiates the predicates in a unary predicate with new predicates.
--
-- The mapping 'f' should be monotonic, that is for all predicates 'p' and 'q,
-- such that 'p |- q', 'f' should satisfy the constraint that 'f p |- f q'.
instantiate :: (Applicative m, Eq q) => (p -> m q) -> UnaryBV p w -> m (UnaryBV q w)
instantiate f u = fin <$> traverse f (unaryBVMap u)
  where fin m = UnaryBV { width = width u
                        , unaryBVMap = Map.fromDistinctAscList l
                        }
          where l = stripDuplicatePreds (Map.toList m)

-- | Return potential values for abstract domain.
domain :: forall p n
        . (1 <= n)
       => BVD.BVDomainParams
       -> (p -> Maybe Bool)
       -> UnaryBV p n
       -> BVDomain n
domain params f u = BVD.fromAscEltList params (width u) (go (unaryBVMap u))
  where go :: IntMap p -> [Integer]
        go m =
          case splitEntry m of
            Nothing -> []
            Just (l,(k,v),h) -> do
              case f v of
                -- value <= k
                Just True -> k:go l
                -- value > k
                Just False -> go h
                Nothing -> go l ++ (k:go h)

------------------------------------------------------------------------
-- Operations

-- | This merges two maps used for a unary bitvector int a single map that
-- combines them.
--
-- 'mergeWithKey sym cfn x y' should return a map 'z' such that for all constants
-- 'c', 'z = c' iff 'cfn (x = c) (y = c)'.
mergeWithKey :: forall sym
              . IsExprBuilder sym
             => sym
             -> (Pred sym -> Pred sym -> IO (Pred sym))
             -> IntMap (Pred sym)
             -> IntMap (Pred sym)
             -> IO (IntMap (Pred sym))
mergeWithKey sym f x y =
    go Map.empty (falsePred sym) (Map.toList x)
                 (falsePred sym) (Map.toList y)
  where go :: IntMap (Pred sym)
           -> Pred sym
           -> [(Integer, Pred sym)]
           -> Pred sym
           -> [(Integer, Pred sym)]
           -> IO (IntMap (Pred sym))
        -- Force "m" to be evaluated"
        go m _ _ _ _ | seq m $ False = error "go bad"
        go m x_prev x_a@((x_k,x_p):x_r) y_prev y_a@((y_k,y_p):y_r) =
          case compare x_k y_k of
            LT -> do
              p <- f x_p y_prev
              go (Map.insert x_k p m) x_p x_r y_prev y_a
            GT -> do
              p <- f x_prev y_p
              go (Map.insert y_k p m) x_prev x_a y_p y_r
            EQ -> do
              p <- f x_p y_p
              go (Map.insert x_k p m) x_p x_r y_p y_r
        go m _ [] _ y_a = do
          go1 m (truePred sym `f`) y_a
        go m _ x_a _ [] = do
          go1 m (`f` truePred sym) x_a

        go1 m fn ((y_k,y_p):y_r) = do
          p <- fn y_p
          go1 (Map.insert y_k p m) fn y_r
        go1 m _ [] =
          return m

-- | @mux sym c x y@ returns value equal to if @c@ then @x@ else @y@.
-- The number of entries in the return value is at most @size x@
-- + @size y@.
mux :: forall sym n
     . (1 <= n, IsExprBuilder sym)
    => sym
    -> Pred sym
    -> UnaryBV (Pred sym) n
    -> UnaryBV (Pred sym) n
    -> IO (UnaryBV (Pred sym) n)
mux sym c x y = fmap (UnaryBV (width x)) $
  mergeWithKey sym
               (itePred sym c)
               (unaryBVMap x)
               (unaryBVMap y)

-- | Return predicate that holds if bitvectors are equal.
eq :: (1 <= n, IsExprBuilder sym)
   => sym
   -> UnaryBV (Pred sym) n
   -> UnaryBV (Pred sym) n
   -> IO (Pred sym)
eq sym0 x0 y0 =
    let (x_k, x_p) = Map.findMin (unaryBVMap x0)
     in go sym0 (falsePred sym0) x_k x_p (unaryBVMap x0) (unaryBVMap y0)
  where go :: IsExprBuilder sym
            => sym
            -> Pred sym
            -> Integer
            -> Pred sym
            -> IntMap (Pred sym)
            -> IntMap (Pred sym)
            -> IO (Pred sym)
        go sym r x_k x_p x y
          | Just (y_k, y_p) <- Map.lookupGE x_k y =
            case x_k == y_k of
              False -> do
                go sym r y_k y_p y x
              True -> do
                let x_lt = maybe (falsePred sym) snd (Map.lookupLT x_k x)
                let y_lt = maybe (falsePred sym) snd (Map.lookupLT x_k y)
                x_is_eq <- andPred sym x_p =<< notPred sym x_lt
                y_is_eq <- andPred sym y_p =<< notPred sym y_lt
                r' <- orPred sym r =<< andPred sym x_is_eq y_is_eq
                case Map.lookupGE (x_k+1) x of
                  Just (x_k', x_p') -> go sym r' x_k' x_p' x y
                  Nothing -> return r'
        go _ r _ _ _ _ = return r

-- | @compareLt sym x y@ returns predicate that holds
-- if for any @k@, @x < k & not (y <= k)@.
compareLt :: forall sym
           . IsExprBuilder sym
          => sym
          -> IntMap (Pred sym)
          -> IntMap (Pred sym)
          -> IO (Pred sym)
compareLt sym x y
    | Map.null y = return (falsePred sym)
    | otherwise  = go (falsePred sym) 0
  where go :: Pred sym -- ^ Return predicate for cases where x is less than minimum.
           -> Integer  -- ^ Minimum value to consider for x.
           -> IO (Pred sym)
        go r min_x
            -- Let x_k0 be min entry in x to consider next.
          | Just (x_k, _) <- Map.lookupGE min_x x
            -- Get smallest entry in y that is larger than x_k.
          , Just (y_k, _) <- Map.lookupGT x_k y
            -- Lookup largest predicate in x for value that is less then y_k.
          , Just (x_k_max, x_p) <- Map.lookupLT y_k x = do

            -- We know the following:
            -- 1. min_x <= x_k <= x_k_max < y_k.
            -- 2. y > x_k => y >= y_k
            -- 3. x < y_k => x_p

            -- Get predicate asserting x < y_k && not (y <= x_k)
            -- Get predicate asserting x < y_k && y > x_k
            x_and_y_lt_x_k <-
              case Map.lookupLT y_k y of
                Nothing -> return $ x_p
                Just (_,y_lt_y_k) -> andPred sym x_p =<< notPred sym y_lt_y_k

            r' <- orPred sym r x_and_y_lt_x_k
            go r' (x_k_max+1)

        go r _ = andPred sym (snd (Map.findMax y)) r

-- | Return predicate that holds if first value is less than other.
ult :: (1 <= n, IsExprBuilder sym)
    => sym
    -> UnaryBV (Pred sym) n
    -> UnaryBV (Pred sym) n
    -> IO (Pred sym)
ult sym x y = compareLt sym (unaryBVMap x) (unaryBVMap y)

-- | Return predicate that holds if first value is less than other.
slt :: (1 <= n, IsExprBuilder sym)
    => sym
    -> UnaryBV (Pred sym) n
    -> UnaryBV (Pred sym) n
    -> IO (Pred sym)
slt sym x y = do
  let mid = maxSigned (width x)

  -- Split map so that we separate the values that will remain positive
  -- from the values that will be negative.
  let (x_pos,x_neg) = splitLeq mid (unaryBVMap x)

  -- Split map so that we separate the values that will remain positive
  -- from the values that will be negative.
  let (y_pos,y_neg) = splitLeq mid (unaryBVMap y)

  x_is_neg <-
    if Map.null x_pos then
      return $ truePred sym
    else
      notPred sym (snd (Map.findMax x_pos))

  pos_case <- compareLt sym x_pos y_pos
  neg_case <- andPred sym x_is_neg =<< compareLt sym x_neg y_neg
  orPred sym pos_case neg_case

splitOnAddOverflow :: Integer -> UnaryBV p n -> (IntMap p, IntMap p)
splitOnAddOverflow v x = assert (0 <= v && v <= limit) $
                           splitLeq overflow_limit (unaryBVMap x)
    where limit = maxUnsigned (width x)
          overflow_limit = limit - v

completeList :: IsExprBuilder sym
             => sym
             -> IntMap (Pred sym) -- ^ Map to merge into
             -> (Integer -> Integer) -- ^ Monotonic function to update keys with
             -> (Pred sym -> IO (Pred sym)) -- ^ Function on predicate.
             -> IntMap (Pred sym)
             -> IO (IntMap (Pred sym))
completeList sym x keyFn predFn m0 = do
  let m1 = Map.mapKeysMonotonic keyFn m0
  m2 <- traverse predFn m1
  mergeWithKey sym (orPred sym) x m2

addConstant :: forall sym n
             . (1 <= n, IsExprBuilder sym)
            => sym
            -> IntMap (Pred sym)
            -> Pred sym
            -> Integer
            -> Pred sym
            -> UnaryBV (Pred sym) n
            -> IO (IntMap (Pred sym))
addConstant sym m0 x_lt x_val x_leq y = do
  let w = width y

  let (y_low, y_high) = splitOnAddOverflow x_val y

  m1 <- completeList sym m0 (x_val +) (andPred sym x_leq) y_low

  -- Add entries when we don't overflow.
  -- If no overflow then continue
  case Map.null y_high of
    True -> return m1
    False -> do
      -- See if there are any entries that do not overflow.
      -- Compute amount of offset to apply to y_val
      let x_off = x_val-2^natValue w
      -- Generate predicate asserting that y overflows and x == x_val
      x_eq <- andPred sym x_leq =<< notPred sym x_lt
      p <-
        case Map.null y_low of
          True -> return $ x_eq
          False -> andPred sym x_eq =<< notPred sym (snd (Map.findMax y_low))
      -- Complete next entries
      completeList sym m1 (x_off +) (andPred sym p) y_high

-- | Add two bitvectors.
--
-- The number of integers in the result will be at most the product of the sizes
-- of the individual bitvectors.
add :: forall sym n
     . (1 <= n, IsExprBuilder sym)
    => sym
    -> UnaryBV (Pred sym) n
    -> UnaryBV (Pred sym) n
    -> IO (UnaryBV (Pred sym) n)
add sym x y = go_x Map.empty (falsePred sym) (unsignedEntries x)
  where w = width x
        go_x :: IntMap (Pred sym)
             -> Pred sym
             -> [(Integer, Pred sym)]
             -> IO (UnaryBV (Pred sym) n)
        go_x m0 _ [] = do
          return $! UnaryBV w m0
        go_x m0 x_lt ((x_val,x_leq):remaining) = do
          m2 <- addConstant sym m0 x_lt x_val x_leq y
          go_x m2 x_leq remaining

-- | Negate a bitvector.
-- The size of the result will be equal to the size of the input.
neg :: forall sym n
     . (1 <= n, IsExprBuilder sym)
    => sym
    -> UnaryBV (Pred sym) n
    -> IO (UnaryBV (Pred sym) n)
neg sym x
  | Map.null (unaryBVMap x) = error "Illegal unary value"
  | otherwise =
    case Map.deleteFindMin (unaryBVMap x) of
      -- Special case for constant 0.
      ((0,_), m) | Map.null m -> return x
      -- Treat 0 case specially, then recurse on remaining elements.
      ((0,x_p), m) -> go [(0, x_p)] x_p             (Map.toDescList m)
      -- Value can't be 0, so just recurse on all ements.
      _ ->            go []         (falsePred sym) (Map.toDescList (unaryBVMap x))
  where w = width x
        -- Iterate through remaining pairs in descending order.
        go :: [(Integer, Pred sym)]
              -- ^ Entries in descending order
           -> Pred sym -- ^ Predicate for first false.
           -> [(Integer, Pred sym)]
              -- ^ Remaining elements in descending order.
           -> IO (UnaryBV (Pred sym) n)
        go m p ((x_k,_) : r@((_,y_p):_)) = seq m $ do
          let z_k = toUnsigned w (negate x_k)
          q <- orPred sym p =<< notPred sym y_p
          let pair = (z_k,q)
          let m' = pair : m
          seq z_k $ seq pair $ seq m' $ do
          go m' p r
        go m _ [(x_k,_)] = seq m $ do
          let z_k = toUnsigned w (negate x_k)
          let q = truePred sym
          return $! UnaryBV w (Map.fromDistinctAscList (reverse ((z_k,q) : m)))
        go _ _ [] = error "Illegal value return in UnaryBV.neg"

-- | Perform a unsigned extension
uext :: (1 <= u, u+1 <= r) => UnaryBV p u -> NatRepr r -> UnaryBV p r
uext x w' = UnaryBV w' (unaryBVMap x)

-- | Perform a signed extension
sext :: (1 <= u, u+1 <= r) => UnaryBV p u -> NatRepr r -> UnaryBV p r
sext x w' = UnaryBV w' (Map.union neg_entries l)
  where w = width x
        mid = maxSigned w
        (l,h) = splitLeq mid (unaryBVMap x)

        diff = 2^natValue w' - 2^natValue w
        neg_entries = Map.mapKeysMonotonic (+ diff) h

-- | Perform a struncation.
trunc :: forall sym u r
       . (IsExprBuilder sym, 1 <= u, u <= r)
      => sym
      -> UnaryBV (Pred sym) r
      -> NatRepr u
      -> IO (UnaryBV (Pred sym) u)
trunc sym x w
  | Just Refl <- testEquality w (width x) = return x
  | otherwise = go Map.empty (truePred sym) (unaryBVMap x)
  where go :: IntMap (Pred sym)
           -> Pred sym
           -> IntMap (Pred sym)
           -> IO (UnaryBV (Pred sym) u)
        go result toRemove remaining
          | Map.null remaining =
            return $! UnaryBV w result
          | otherwise = do
            let (k,_) = Map.findMin remaining
            -- Get base offset
            let base = k `xor` (maxUnsigned w)
            let next = base + maxUnsigned w
            let (l,h) = splitLeq next remaining

            assert (not (Map.null l)) $ do
            -- Get entries to add.
            result' <- completeList sym result (toUnsigned w) (andPred sym toRemove) l

            let (_,p) = Map.findMax l
            toRemove' <- notPred sym p
            go result' toRemove' h
