{-|
Module           : What4.Utils.LeqMap
Copyright        : (c) Galois, Inc 2015-2016
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module defines a strict map.

It is similiar to Data.Map.Strict, but provides some additional operations
including splitEntry, splitLeq, fromDistinctDescList.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
module What4.Utils.LeqMap
  ( LeqMap
  , toList
  , findMin
  , findMax
  , null
  , empty
  , mapKeysMonotonic
  , union
  , fromDistinctAscList
  , fromDistinctDescList
  , toDescList
  , deleteFindMin
  , deleteFindMax
  , minViewWithKey
  , filterGt
  , filterLt
  , insert
  , lookupLE
  , lookupLT
  , lookupGE
  , lookupGT
  , keys
  , mergeWithKey
  , singleton
  , foldlWithKey'
  , size
  , splitEntry
  , splitLeq
  ) where

import Control.Applicative hiding (empty)
import Prelude hiding (lookup, null)
import Data.Traversable (foldMapDefault)

data MaybeS a = NothingS | JustS !a

type Size = Int

data LeqMap k p
   = Bin {-# UNPACK #-} !Size !k !p !(LeqMap k p) !(LeqMap k p)
   | Tip

bin :: k -> p -> LeqMap k p -> LeqMap k p -> LeqMap k p
bin k x l r = Bin (size l + size r + 1) k x l r

balanceL :: k -> p -> LeqMap k p -> LeqMap k p -> LeqMap k p
balanceL k x l r =
  case l of
    Bin ls lk lx ll lr | ls > max 1 (delta*size r)  ->
      case lr of
        Bin lrs lrk lrx lrl lrr | lrs >= ratio* size ll ->
          bin lrk lrx (bin lk lx ll  lrl) (bin k  x  lrr r)
        _ -> bin lk lx ll (bin k x lr r)
    _ -> bin k x l r

-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
balanceR :: k -> p -> LeqMap k p -> LeqMap k p -> LeqMap k p
balanceR k x l r = case l of
  Tip -> case r of
           Tip -> Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin 2 k x Tip r
           (Bin _ rk rx Tip rr@(Bin{})) -> Bin 3 rk rx (Bin 1 k x Tip Tip) rr
           (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) -> Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
             | rls < ratio*rrs -> Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
             | otherwise -> Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr rr)

  (Bin ls _ _ _ _) -> case r of
           Tip -> Bin (1+ls) k x l Tip

           (Bin rs rk rx rl rr)
              | rs > delta*ls  -> case (rl, rr) of
                   (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
                     | rls < ratio*rrs -> Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                     | otherwise -> Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                   (_, _) -> error "Failure in Data.Map.balanceR"
              | otherwise -> Bin (1+ls+rs) k x l r

delta,ratio :: Int
delta = 3
ratio = 2

insertMax :: k -> p -> LeqMap k p -> LeqMap k p
insertMax kx x t =
  case t of
    Tip -> singleton kx x
    Bin _ ky y l r -> balanceR ky y l (insertMax kx x r)

insertMin :: k -> p -> LeqMap k p -> LeqMap k p
insertMin kx x t =
  case t of
    Tip -> singleton kx x
    Bin _ ky y l r -> balanceL ky y (insertMin kx x l) r


link :: k -> p -> LeqMap k p -> LeqMap k p -> LeqMap k p
link kx x Tip r  = insertMin kx x r
link kx x l Tip  = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL < sizeR  = balanceL kz z (link kx x l lz) rz
  | delta*sizeR < sizeL  = balanceR ky y ly (link kx x ry r)
  | otherwise            = bin kx x l r

instance (Ord k, Eq p) => Eq (LeqMap k p) where
  x == y = size x == size y && toList x == toList y


instance Functor (LeqMap k) where
  fmap _ Tip = Tip
  fmap f (Bin s k a l r) = Bin s k (f a) (fmap f l) (fmap f r)

instance Foldable (LeqMap k) where
  foldMap = foldMapDefault

instance Traversable (LeqMap k) where
  traverse _ Tip = pure Tip
  traverse f (Bin s k a l r) = Bin s k <$> f a <*> traverse f l <*> traverse f r


-- | Return the empty map
empty :: LeqMap k p
empty = Tip

singleton :: k -> p -> LeqMap k p
singleton k a = Bin 1 k a Tip Tip

size :: LeqMap k p -> Int
size Tip = 0
size (Bin s _ _ _ _) = s

null :: LeqMap k p -> Bool
null Tip = True
null Bin{} = False

findMax :: LeqMap k p -> (k,p)
findMax Tip = error "findMax of empty map."
findMax (Bin _ k0 a0 _ r0) = go k0 a0 r0
  where go :: k -> p -> LeqMap k p -> (k,p)
        go _ _ (Bin _ k a _ r) = go k a r
        go k a Tip = (k, a)

findMin :: LeqMap k p -> (k,p)
findMin Tip = error "findMin of empty map."
findMin (Bin _ k0 a0 l0 _) = go k0 a0 l0
  where go :: k -> p -> LeqMap k p -> (k,p)
        go _ _ (Bin _ k a l _) = go k a l
        go k a Tip = (k, a)

toList :: LeqMap k p -> [(k,p)]
toList Tip = []
toList (Bin _ k a l r) = toList l ++ ((k,a):toList r)

mapKeysMonotonic :: (k1 -> k2) -> LeqMap k1 p -> LeqMap k2 p
mapKeysMonotonic _ Tip = Tip
mapKeysMonotonic f (Bin s k a l r) =
  Bin s (f k) a (mapKeysMonotonic f l) (mapKeysMonotonic f r)

splitLeq :: Ord k => k -> LeqMap k p -> (LeqMap k p, LeqMap k p)
splitLeq k m = seq k $
  case m of
    Tip -> (Tip, Tip)
    Bin _ kx x l r ->
      case compare k kx of
        LT ->
          let (ll, lr) = splitLeq k l
              r' = link kx x lr r
           in seq r' (ll, r')
        GT ->
          let (rl, rr) = splitLeq k r
              l' = link kx x l rl
           in seq l' (l', rr)
        EQ ->
          let l' = insertMax kx x l
           in seq l' (l', r)
{-# INLINABLE splitLeq #-}

splitEntry :: LeqMap k p -> Maybe (LeqMap k p, (k, p), LeqMap k p)
splitEntry Tip = Nothing
splitEntry (Bin _ k a l r) = Just (l, (k, a), r)

insert :: Ord k => k -> p -> LeqMap k p -> LeqMap k p
insert = go
  where
    go :: Ord k => k -> p -> LeqMap k p -> LeqMap k p
    go kx x _ | seq kx $ seq x $ False = error "insert bad"
    go kx x Tip = singleton kx x
    go kx x (Bin sz ky y l r) =
      case compare kx ky of
        LT -> balanceL ky y (go kx x l) r
        GT -> balanceR ky y l (go kx x r)
        EQ -> Bin sz kx x l r

lookupLE_Just :: Ord k => k -> k -> p -> LeqMap k p -> (k, p)
lookupLE_Just _ ky y Tip = (ky,y)
lookupLE_Just k ky y (Bin _ kx x l r) =
  case compare kx k of
    LT -> lookupLE_Just k kx x r
    GT -> lookupLE_Just k ky y l
    EQ -> (kx, x)
{-# INLINABLE lookupLE_Just #-}

lookupGE_Just :: Ord k => k -> k -> p -> LeqMap k p -> (k, p)
lookupGE_Just _ ky y Tip = (ky,y)
lookupGE_Just k ky y (Bin _ kx x l r) =
  case compare kx k of
    LT -> lookupGE_Just k ky y r
    GT -> lookupGE_Just k kx x l
    EQ -> (kx, x)
{-# INLINABLE lookupGE_Just #-}

lookupLT_Just :: Ord k => k -> k -> p -> LeqMap k p -> (k, p)
lookupLT_Just _ ky y Tip = (ky,y)
lookupLT_Just k ky y (Bin _ kx x l r) =
  case kx < k of
    True  -> lookupLT_Just k kx x r
    False -> lookupLT_Just k ky y l
{-# INLINABLE lookupLT_Just #-}

lookupGT_Just :: Ord k => k -> k -> p -> LeqMap k p -> (k, p)
lookupGT_Just _ ky y Tip = (ky,y)
lookupGT_Just k ky y (Bin _ kx x l r) =
  case kx > k of
    True  -> lookupGT_Just k kx x l
    False -> lookupGT_Just k ky y r
{-# INLINABLE lookupGT_Just #-}

-- | Find largest element that is less than or equal to key (if any).
lookupLE :: Ord k => k -> LeqMap k p -> Maybe (k,p)
lookupLE k0 m0 = seq k0 (goNothing k0 m0)
  where goNothing :: Ord k => k -> LeqMap k p -> Maybe (k,p)
        goNothing _ Tip = Nothing
        goNothing k (Bin _ kx x l r) =
          case compare kx k of
            LT -> Just $ lookupLE_Just k kx x r
            GT -> goNothing k l
            EQ -> Just (kx, x)
{-# INLINABLE lookupLE #-}

-- | Find largest element that is at least key (if any).
lookupGE :: Ord k => k -> LeqMap k p -> Maybe (k,p)
lookupGE k0 m0 = seq k0 (goNothing k0 m0)
  where goNothing :: Ord k => k -> LeqMap k p -> Maybe (k,p)
        goNothing _ Tip = Nothing
        goNothing k (Bin _ kx x l r) =
          case compare kx k of
            LT -> goNothing k r
            GT -> Just $ lookupGE_Just k kx x l
            EQ -> Just (kx, x)
{-# INLINABLE lookupGE #-}

-- | Find less than element that is less than key (if any).
lookupLT :: Ord k => k -> LeqMap k p -> Maybe (k,p)
lookupLT k0 m0 = seq k0 (goNothing k0 m0)
  where goNothing :: Ord k => k -> LeqMap k p -> Maybe (k,p)
        goNothing _ Tip = Nothing
        goNothing k (Bin _ kx x l r) =
          case kx < k of
            True -> Just $ lookupLT_Just k kx x r
            False -> goNothing k l
{-# INLINABLE lookupLT #-}

-- | Find less than element that is less than key (if any).
lookupGT :: Ord k => k -> LeqMap k p -> Maybe (k,p)
lookupGT k0 m0 = seq k0 (goNothing k0 m0)
  where goNothing :: Ord k => k -> LeqMap k p -> Maybe (k,p)
        goNothing _ Tip = Nothing
        goNothing k (Bin _ kx x l r) =
          case kx > k of
            True -> Just $ lookupGT_Just k kx x l
            False -> goNothing k r
{-# INLINABLE lookupGT #-}

filterMGt :: Ord k => MaybeS k -> LeqMap k p -> LeqMap k p
filterMGt NothingS t = t
filterMGt (JustS b0) t = filterGt b0 t
{-# INLINABLE filterMGt #-}

filterGt :: Ord k => k -> LeqMap k p -> LeqMap k p
filterGt b t = seq b $ do
  case t of
    Tip -> Tip
    Bin _ kx x l r ->
      case compare b kx of
        LT -> link kx x (filterGt b l) r
        GT -> filterGt b r
        EQ -> r
{-# INLINABLE filterGt #-}

filterMLt :: Ord k => MaybeS k -> LeqMap k p -> LeqMap k p
filterMLt NothingS t = t
filterMLt (JustS b) t = filterLt b t
{-# INLINABLE filterMLt #-}

filterLt :: Ord k => k -> LeqMap k p -> LeqMap k p
filterLt b t = seq b $ do
  case t of
    Tip -> Tip
    Bin _ kx x l r ->
      case compare kx b of
        LT -> link kx x l (filterLt b r)
        EQ -> l
        GT -> filterLt b l
{-# INLINABLE filterLt #-}

trim :: Ord k => MaybeS k -> MaybeS k -> LeqMap k p -> LeqMap k p
trim NothingS   NothingS   t = t
trim (JustS lk) NothingS   t = greater lk t
trim NothingS   (JustS hk) t = lesser hk t
trim (JustS lk) (JustS hk) t = middle lk hk t
{-# INLINABLE trim #-}

-- | @lesser hi m@ returns all entries in @m@ less than @hi@.
lesser :: Ord k => k -> LeqMap k p -> LeqMap k p
lesser hi (Bin _ k _ l _) | hi <= k = lesser hi l
lesser _ t' = t'
{-# INLINABLE lesser #-}

mgt :: Ord k => k -> MaybeS k -> Bool
mgt _ NothingS = True
mgt k (JustS y) = k > y

middle :: Ord k => k -> k -> LeqMap k p -> LeqMap k p
middle lo hi (Bin _ k _ _ r) | k <= lo = middle lo hi r
middle lo hi (Bin _ k _ l _) | k >= hi = middle lo hi l
middle _  _  t' = t'
{-# INLINABLE middle #-}

greater :: Ord k => k -> LeqMap k p -> LeqMap k p
greater lo (Bin _ k _ _ r) | k <= lo = greater lo r
greater _  t' = t'

union :: Ord k => LeqMap k p -> LeqMap k p -> LeqMap k p
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnion NothingS NothingS t1 t2
{-# INLINABLE union #-}

insertR :: Ord k => k -> p -> LeqMap k p -> LeqMap k p
insertR = go
  where
    go :: Ord k => k -> p -> LeqMap k p -> LeqMap k p
    go kx x _ | seq kx $ seq x $ False = error "insert bad"
    go kx x Tip = singleton kx x
    go kx x t@(Bin _ ky y l r) =
      case compare kx ky of
        LT -> balanceL ky y (go kx x l) r
        GT -> balanceR ky y l (go kx x r)
        EQ -> t
{-# INLINABLE insertR #-}


-- left-biased hedge union
hedgeUnion :: Ord k => MaybeS k -> MaybeS k -> LeqMap k p -> LeqMap k p -> LeqMap k p
hedgeUnion _   _   t1  Tip = t1
hedgeUnion blo bhi Tip (Bin _ kx x l r) =
  link kx x (filterMGt blo l) (filterMLt bhi r)
hedgeUnion _   _   t1  (Bin _ kx x Tip Tip) =
  insertR kx x t1  -- According to benchmarks, this special case increases
                   -- performance up to 30%. It does not help in difference or intersection.
hedgeUnion blo bhi (Bin _ kx x l r) t2 =
  link kx x (hedgeUnion blo bmi l (trim blo bmi t2))
            (hedgeUnion bmi bhi r (trim bmi bhi t2))
  where bmi = JustS kx
{-# INLINABLE hedgeUnion #-}

foldlWithKey' :: (a -> k -> b -> a) -> a -> LeqMap k b -> a
foldlWithKey' _ z Tip = z
foldlWithKey' f z (Bin _ kx x l r) =
  foldlWithKey' f (f (foldlWithKey' f z l) kx x) r

keys :: LeqMap k p -> [k]
keys Tip = []
keys (Bin _ kx _ l r) = keys l ++ (kx:keys r)

minViewWithKey :: LeqMap k p -> Maybe ((k,p), LeqMap k p)
minViewWithKey Tip = Nothing
minViewWithKey t@Bin{} = Just (deleteFindMin t)

deleteFindMin :: LeqMap k p -> ((k,p),LeqMap k p)
deleteFindMin t
  = case t of
      Bin _ k x Tip r -> ((k,x),r)
      Bin _ k x l r   -> let (km,l') = deleteFindMin l in (km,balanceR k x l' r)
      Tip             -> (error "LeqMap.deleteFindMin: can not return the minimal element of an empty map", Tip)

deleteFindMax :: LeqMap k p -> ((k,p),LeqMap k p)
deleteFindMax t
  = case t of
      Bin _ k x l Tip -> ((k,x),l)
      Bin _ k x l r   -> let (km,r') = deleteFindMax r in (km,balanceL k x l r')
      Tip             -> (error "LeqMap.deleteFindMax: can not return the maximal element of an empty map", Tip)

mergeWithKey :: forall a b c
              . (a -> b -> IO c)
             -> (a -> IO c)
             -> (b -> IO c)
             -> LeqMap Integer a
             -> LeqMap Integer b
             -> IO (LeqMap Integer c)
mergeWithKey f0 g1 g2 = go
  where

    go Tip t2 = traverse g2 t2
    go t1 Tip = traverse g1 t1
    go t1 t2 | size t1 <= size t2 = hedgeMerge NothingS NothingS NothingS t1 NothingS t2
             | otherwise = mergeWithKey (flip f0) g2 g1 t2 t1

    hedgeMerge :: MaybeS Integer
               -> MaybeS Integer
               -> MaybeS a
               -> LeqMap Integer a
               -> MaybeS b
               -> LeqMap Integer b
               -> IO (LeqMap Integer c)
    hedgeMerge mlo mhi a _ b _ | seq mlo $ seq mhi $ seq a $ seq b $ False = error "hedgeMerge"
    hedgeMerge _   _  _ t1 mb Tip = do
      case mb of
        NothingS -> traverse g1 t1
        JustS b -> traverse (`f0` b) t1

    hedgeMerge blo bhi ma Tip _ (Bin _ kx x l r) = do
      case ma of
        NothingS ->
          link kx <$> g2 x
                  <*> traverse g2 (filterMGt blo l)
                  <*> traverse g2 (filterMLt bhi r)
        JustS a ->
          link kx <$> f0 a x
                  <*> traverse (f0 a) (filterMGt blo l)
                  <*> traverse (f0 a) (filterMLt bhi r)
    hedgeMerge blo bhi a (Bin _ kx x l r) mb t2 = do
      let bmi = JustS kx
      case lookupLE kx t2 of
        Just (ky,y) | ky `mgt` blo -> do
          l' <- hedgeMerge blo bmi a l mb (trim blo bmi t2)
          x' <- f0 x y
          r' <- hedgeMerge bmi bhi (JustS x) r (JustS y) (trim bmi bhi t2)
          return $! link kx x' l' r'
        _ -> do
          case mb of
            NothingS -> do
              l' <- traverse g1 l
              x' <- g1 x
              r' <- hedgeMerge bmi bhi (JustS x) r mb (trim bmi bhi t2)
              return $! link kx x' l' r'
            JustS b -> do
              l' <- traverse (`f0` b) l
              x' <- f0 x b
              r' <- hedgeMerge bmi bhi (JustS x) r mb (trim bmi bhi t2)
              return $! link kx x' l' r'
{-# INLINE mergeWithKey #-}


foldlWithKey :: (a -> k -> b -> a) -> a -> LeqMap k b -> a
foldlWithKey f z = go z
  where
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
{-# INLINE foldlWithKey #-}

toDescList :: LeqMap k p -> [(k,p)]
toDescList = foldlWithKey (\xs k x -> (k,x):xs) []

fromDistinctAscList :: [(k,p)] -> LeqMap k p
fromDistinctAscList [] = Tip
fromDistinctAscList ((kx0, x0) : xs0) = x0 `seq` go 0 (Bin 1 kx0 x0 Tip Tip) xs0
  where
    go :: Int -> LeqMap k p -> [(k,p)] -> LeqMap k p
    go _ t [] = t
    go s l ((kx, x) : xs) = case create s xs of
                              (r, ys) -> x `seq` go (s + 1) (link kx x l r) ys

    -- @create k l@ extracts at most @2^k@ elements from @l@ and creates a map.
    -- The remaining elements (if any) are returned as well.
    create :: Int -> [(k, p)] -> (LeqMap k p, [(k,p)])
    -- Reached end of list.
    create _ [] = (Tip, [])
    -- Extract single element
    create 0 ((kx,x) : xs') = x `seq` (Bin 1 kx x Tip Tip, xs')
    create s xs
      | otherwise =
        case create (s - 1) xs of
          res@(_, []) -> res
          (l, (ky, y):ys) ->
            case create (s - 1) ys of
              (r, zs) -> y `seq` (link ky y l r, zs)

-- | Create a map from a list of keys in descending order.
fromDistinctDescList :: [(k,p)] -> LeqMap k p
fromDistinctDescList [] = Tip
fromDistinctDescList ((kx0, x0) : xs0) = x0 `seq` go 0 (Bin 1 kx0 x0 Tip Tip) xs0
  where
    go :: Int -> LeqMap k p -> [(k,p)] -> LeqMap k p
    go _ t [] = t
    go s r ((kx, x) : xs) = case create s xs of
                              (l, ys) -> x `seq` go (s + 1) (link kx x l r) ys

    -- @create k l@ extracts at most @2^k@ elements from @l@ and creates a map.
    -- The remaining elements (if any) are returned as well.
    create :: Int -> [(k, p)] -> (LeqMap k p, [(k,p)])
    -- Reached end of list.
    create _ [] = (Tip, [])
    -- Extract single element
    create 0 ((kx,x) : xs') = x `seq` (Bin 1 kx x Tip Tip, xs')
    create s xs
      | otherwise =
        case create (s - 1) xs of
          res@(_, []) -> res
          (r, (ky, y):ys) ->
            case create (s - 1) ys of
              (l, zs) -> y `seq` (link ky y l r, zs)
