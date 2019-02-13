{-|
Copyright   : (c) Galois Inc, 2015-2017
License     : BSD3
Maintainer  : jhendrix@galois.com

Defines a simple way of representing sets of bitvector values for
abstract interpretation purposes.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
#if MIN_VERSION_base(4,9,0)
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
module What4.Utils.BVDomain.Map
  ( BVDomainParams(..)
  , defaultBVDomainParams
  , BVDomain
  , isValidBVDomain
    -- * Projection functions
  , asSingleton
  , ubounds
  , sbounds
  , eq
  , slt
  , ult
  , testBit
  , domainsOverlap
  , ranges
    -- * Operations
  , empty
  , any
  , singleton
  , range
  , fromAscEltList
  , concat
  , select
  , negate
  , add
  , mul
  , udiv
  , urem
  , sdiv
  , srem
  , union
  , shl
  , lshr
  , ashr
  , zext
  , sext
  , What4.Utils.BVDomain.Map.not
  , and
  , or
  , xor
  ) where

import           Control.Exception (assert)
import           Control.Lens ((&))
import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import qualified Data.Foldable as Fold
import           Data.List hiding (and, any, concat, or, union)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.NatRepr
import           Data.Set (Set)
import qualified Data.Set as Set
import           Numeric.Natural
import           GHC.TypeNats

import           Prelude hiding (any, concat, negate, and, or)

-- | @halfRange n@ returns @2^(n-1)@.
halfRange :: NatRepr w -> Integer
halfRange w = bit (widthVal w - 1)

-- | @rangeSize n@ returns @2^n@.
rangeSize :: NatRepr w -> Integer
rangeSize w = bit (widthVal w)

------------------------------------------------------------------------
-- ModRange

-- | This is used to represent contiguous or the complement of contiguous ranges.
data ModRange
  = InclusiveRange !Integer !Integer
    -- ^ @InclusiveRange l h@ denotes the range [l..h]
  | ExclusiveRange !Integer !Integer
    -- ^ @ExclusiveRange l h@ denotes the range @union [0..l] [h..maxUnsigned w]@
  | AnyRange
    -- ^ @AnyRange@ special case to denote any value.

-- | Given lower and upper bound integer bounds this looks at the allowed bitvector
-- values of a given width through inspecting low and high bits.
modRange :: NatRepr w -> Integer -> Integer -> ModRange
modRange w lbound ubound
    -- If the upper bits are the same, then truncation is fine.
    | high_ubound == high_lbound =
        InclusiveRange low_lbound low_ubound
      --  If high_ubound is one more than low_lbound, and there is a gap between
      -- the least bits of the upper bound and the least bits of the lower bound
      -- then split to two cases.
    | high_ubound == high_lbound + 1, low_ubound + 1 < low_lbound =
        ExclusiveRange low_ubound low_lbound
      -- Otherwise return all elements.
    | otherwise = AnyRange
  where high_lbound = lbound `shiftR` widthVal w
        high_ubound = ubound `shiftR` widthVal w
        low_lbound  = maxUnsigned w .&. lbound
        low_ubound  = maxUnsigned w .&. ubound

------------------------------------------------------------------------
-- BVDomain Parameters

-- | Parameters for a domain
newtype BVDomainParams
  = DP { rangeLimit :: Int
         -- ^ Maximum number of discrete ranges that we track.
       }

-- | Default allows two discrete ranges (this is useful for signed and unsigned.
defaultBVDomainParams :: BVDomainParams
defaultBVDomainParams = DP { rangeLimit = 2 }

------------------------------------------------------------------------
-- BVDomain definition

newtype BVDomain (w :: Nat)
   = BVDomain { -- | Map from lower bounds to upper bound for that range.
                --
                -- * Each key in the map should be less than or equal to the
                --   associated value.
                -- * Each key should be non-negative.
                -- * Each value should be at most @maxNat w@.
                -- * The ranges are normalized so that no distinct ranges
                --   are overlapping or contiguous.  Effectively, this means
                --   each key after the first should be greater than the
                --   bound values that occur before in an in-order traversal.
                domainRanges :: (Map Integer Integer)
              }

-- | Checks the invariants that should be maintained by BVDomain.
isValidBVDomain :: NatRepr w -> BVDomain w -> Bool
isValidBVDomain w d =
    case Map.toList (domainRanges d) of
      [] -> True
      ((l,h):r) -> l >= 0 && h >= l && go h r
  where go :: Integer -> [(Integer,Integer)] -> Bool
        go last_high [] = last_high <= maxUnsigned w
        -- Check that adjacent ranges are not contiguous.
        go last_high ((l,h):r) = last_high+1 < l && l <= h && go h r

------------------------------------------------------------------------
-- Projection functions

-- | Convert domain to list of ranges.
ranges :: NatRepr w -> BVDomain w -> [(Integer, Integer)]
ranges _w d = toList d

-- | Convert domain to list of ranges.
toList :: BVDomain w -> [(Integer, Integer)]
toList d = Map.toList (domainRanges d)

-- | Return elements in domain from least to greatest.
domainElts :: BVDomain w -> [Integer]
domainElts d = do
  (l,h) <- toList d
  [l..h]

-- | Return number of elements in domain.
count :: BVDomain w -> Integer
count d = sum (uncurry rangeWidth <$> toList d)
  where rangeWidth l h = h - l + 1

-- | Return the number of elements in the domain.
rangeCount :: BVDomain w -> Integer
rangeCount d = toInteger (Map.size (domainRanges d))

-- | Return True if this domain includes every value.
isEmpty :: BVDomain w -> Bool
isEmpty d = Map.null (domainRanges d)

-- | Return True if this domain includes every value.
isAny :: NatRepr w -> BVDomain w -> Bool
isAny w d =
  case toList d of
    [(0,h)] -> h == maxUnsigned w
    _ -> False

-- | Return value if this is a singleton.
asSingleton :: BVDomain w -> Maybe Integer
asSingleton d =
  case toList d of
    [(l,h)] | l == h -> Just l
    _ -> Nothing

-- | Get largest element in domain less than or equal to given value.
domainLE :: Integer -- ^ Value to lookup.
         -> BVDomain w
         -> Maybe Integer
domainLE v d = getBound <$> Map.lookupLE v (domainRanges d)
  where getBound (_, h) = min h v

-- | Get largest element in domain less than given value.
domainLT :: Integer -- ^ Value to lookup.
         -> BVDomain w
         -> Maybe Integer
domainLT v d = domainLE (v-1) d

-- | Get smallest element in domain greater-than-or-equal to value if one exists.
domainGE :: Integer -> BVDomain w -> Maybe Integer
domainGE v d =
  case Map.lookupLE v (domainRanges d) of
    -- First check to see if value is in earlier range.
    Just (_, h) | v <= h -> Just v
    -- Otherwise get first value in next range.
    _ -> fst <$> Map.lookupGE v (domainRanges d)

-- | Return the minimum unsigned value in domain or @Nothing@ if domain is empty.
domainUnsignedMin :: BVDomain w -> Maybe Integer
domainUnsignedMin d | isEmpty d = Nothing
                    | otherwise = Just $! fst (Map.findMin (domainRanges d))

-- | Return the maximum unsigned value in domain or @Nothing@ if domain is empty.
domainUnsignedMax :: BVDomain w -> Maybe Integer
domainUnsignedMax d | isEmpty d = Nothing
                    | otherwise = Just $! snd (Map.findMax (domainRanges d))

-- | Return minimal value signed value contained in domain.
domainSignedMin :: NatRepr w -> BVDomain w -> Maybe Integer
domainSignedMin w d
  | Just neg_l <- domainGE (halfRange w) d =
    Just $! neg_l - rangeSize w
  | otherwise = domainUnsignedMin d

-- | Return the maximum signed value in the domain or @Nothing@ if domain is empty.
domainSignedMax :: (1 <= w) => NatRepr w -> BVDomain w -> Maybe Integer
domainSignedMax w d
    -- There is a positive value.
  | Just pos_l <- domainLT (halfRange w) d =  Just pos_l
  | otherwise = (\v -> v - rangeSize w) <$> domainUnsignedMax d

-- | Return signed bounds for domain.
sbounds :: (1 <= w) => NatRepr w -> BVDomain w -> Maybe (Integer, Integer)
sbounds w d = (,) <$> domainSignedMin w d <*> domainSignedMax w d

-- | Return unsigned bounds for domain.
ubounds :: (1 <= w) => NatRepr w -> BVDomain w -> Maybe (Integer, Integer)
ubounds _ d = (,) <$> domainUnsignedMin d <*> domainUnsignedMax d

instance Show (BVDomain w) where
  show d = "fromList " ++ show (toList d)

-- | Return true if domains contain a common element.
domainsOverlap :: BVDomain w -> BVDomain w -> Bool
domainsOverlap xd yd = go (toList xd) (toList yd)
  where go [] _ = False
        go _ [] = False
        go x0@((xl,xh):x) y0@((yl,yh):y)
          | xh < yl = go x y0
          | yh < xl = go x0 y
          | otherwise = True

eq :: BVDomain w -> BVDomain w -> Maybe Bool
eq x y | Just xv <- asSingleton x, Just yv <- asSingleton y = Just (xv == yv)
       | domainsOverlap x y == False = Just False
       | otherwise = Nothing

-- | Check if all elements in one domain are less than all elements in other.
slt :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> Maybe Bool
slt w x y
  | Just x_max <- domainSignedMax w x
  , Just y_min <- domainSignedMin w y
  , x_max < y_min
  = Just True
slt w x y
  | Just x_min <- domainSignedMin w x
  , Just y_max <- domainSignedMax w y
  , x_min >= y_max
  = Just False
slt _ _ _ = Nothing

-- | Check if all elements in one domain are less than all elements in other.
ult :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> Maybe Bool
ult _ x y
  | Just x_max <- domainUnsignedMax x
  , Just y_min <- domainUnsignedMin y
  , x_max < y_min
  = Just True
ult _ x y
  | Just x_min <- domainUnsignedMin x
  , Just y_max <- domainUnsignedMax y
  , x_min >= y_max
  = Just False
ult _ _ _ = Nothing

-- | Return true if bits in domain are set.
testBit :: NatRepr w
        -> BVDomain w
        -> Natural -- ^ Index of bit (least-significant bit has index 0)
        -> Maybe Bool
testBit w d i = assert (i < natValue w) $
    case uncurry testRange <$> toList d of
      (mb@Just{}:r) | all (== mb) r -> mb
      _ -> Nothing
  where j = fromIntegral i
        testRange :: Integer -> Integer -> Maybe Bool
        testRange l h | (l `shiftR` j) == (h `shiftR` j) =
                        Just (l `Bits.testBit` j)
                      | otherwise = Nothing

------------------------------------------------------------------------
-- Internal Methods

-- | A GapMap is a data structure used to identify which ranges to
-- combine when the number of discrete ranges in the BVDomain exceeds
-- the limit defined by the parameters.
--
-- In particular, it maps the integer size of each gap between contiguous
-- range entries to the set of end addresses whose subsequent gap has
-- the given size.
type GapMap = Map Integer (Set Integer)

-- | @deleteGapEntry h l gm@ deletes the gap from @h@ to @l@ from @gm@.
deleteGapEntry :: Integer -> Integer -> GapMap -> GapMap
deleteGapEntry h_prev l gm = Map.adjust (Set.delete l) (l - h_prev) gm

-- | Inserts a new gap into the map
insertGapEntry :: Integer -- ^ Upper bound before start of gap.
               -> Integer -- ^ Lower bound that ends gap.
               -> GapMap
               -> GapMap
insertGapEntry h_prev l gm = Map.alter (Just . f) sz gm
  where sz = l - h_prev
        f = maybe (Set.singleton l) (Set.insert l)

-- | @deleteGapRange l h m gm@ deletes any gap before the entry @l@ from @gm@.
deleteGapRange :: Integer -> Integer -> Map Integer Integer -> GapMap -> GapMap
deleteGapRange l h m gm =
  case (Map.lookupLT l m, Map.lookupGT h m) of
    (Just (_,h_prev), Just (l_next,_)) ->
      gm & deleteGapEntry h_prev l
         & deleteGapEntry h l_next
         & insertGapEntry h_prev l_next
    (Nothing, Just (l_next,_)) ->
      gm & deleteGapEntry h l_next
    (Just (_,h_prev), Nothing) ->
      gm & deleteGapEntry h_prev l
    (Nothing, Nothing) -> assert (Map.null gm)
      gm

-- | @insertGapRange l h m gm@ inserts gaps arrisign from inserting @l@ @h@ into ranges.
insertGapRange :: Integer -> Integer -> Map Integer Integer -> GapMap -> GapMap
insertGapRange l h m gm =
  case (Map.lookupLT l m, Map.lookupGT h m) of
    (Just (_,h_prev), Just (l_next, _)) ->
      gm & deleteGapEntry h_prev l_next
         & insertGapEntry h_prev l
         & insertGapEntry h l_next
    (Nothing, Just (l_next, _)) ->
      gm & insertGapEntry h l_next
    (Just (_,h_prev), Nothing) ->
      gm & insertGapEntry h_prev l
    (Nothing, Nothing) ->
      gm

gapsToMerge ::  GapMap -> [Integer]
gapsToMerge = concatMap Set.toList . Map.elems

-- | Intermediate BV domain results before merging the results.
data InterBVDomain
   = InterBVDomain { interGaps :: !GapMap
                   , interMap  :: !(Map Integer Integer)
                   }
  deriving (Show)

emptyInterBVDomain :: InterBVDomain
emptyInterBVDomain =
  InterBVDomain { interGaps = Map.empty
                , interMap = Map.empty
                }

-- | Create bounded BV domain with given size from the interBVdomain
boundedBVDomain :: String -- ^ Name of function calling this
                -> BVDomainParams -- ^ Maximum size of BVDomain range
                -> NatRepr w
                -> InterBVDomain
                -> BVDomain w
boundedBVDomain _nm params _w input = BVDomain { domainRanges = d }
  where gm = interGaps input
        m0 = interMap input
        cnt = rangeLimit params
        d = foldl' f m0 (take (Map.size m0 - cnt) (gapsToMerge gm))
        f :: Map Integer Integer
          -> Integer -- ^ Lower bound of range to delete
          -> Map Integer Integer
        f m l = Map.insert l_prev h $ Map.delete l m
          where Just (l_prev,_) = Map.lookupLT l m
                Just h = Map.lookup l m

-- | @insertRange l h d@ inserts the range [l,h] into @d@.
insertRange :: Integer
            -> Integer
            -> InterBVDomain
            -> InterBVDomain
insertRange l h inputs = seq l $ seq h $ seq inputs $
  case Map.lookupLE (h+1) (interMap inputs) of
    -- Look for overlapping range to delete.
    Just (l_prev, h_prev)
      -- Check to see if current range subsumes new range.
      | l_prev <= l && h <= h_prev -> inputs
        -- Check to see if they overlap.
      | h_prev + 1 >= l ->
        let l' = min l l_prev
            h' = max h h_prev
            inputs' = InterBVDomain
                      { interGaps =
                          deleteGapRange l_prev h_prev (interMap inputs) (interGaps inputs)
                      , interMap =
                          Map.delete l_prev (interMap inputs)
                      }
         in insertRange l' h' inputs'
    _ ->
      InterBVDomain { interGaps = insertGapRange l h (interMap inputs) (interGaps inputs)
                    , interMap  = Map.insert l h (interMap inputs)
                    }

------------------------------------------------------------------------
-- Internal operations

-- | Convert unsigned ranges to signed ranges
toSignedRanges :: (1 <= w) => NatRepr w -> BVDomain w -> [(Integer,Integer)]
toSignedRanges w d = concatMap go (toList d)
  where go :: (Integer,Integer) -> [(Integer,Integer)]
        go (l,h)
            -- both l and h represent nonnegative numbers
          | h <= maxSigned w = [(l,h)]
            -- only h is negative, split the range
          | l <= maxSigned w = [(l, maxSigned w), (minSigned w, h - rangeSize w)]
            -- both l and h are negative
          | otherwise = [(l - rangeSize w, h - rangeSize w)]

-- | Return list of signed ranges in domain.
signedToUnsignedRanges :: NatRepr w -> [(Integer,Integer)] -> [(Integer,Integer)]
signedToUnsignedRanges w l0 = concatMap go l0
  where go :: (Integer,Integer) -> [(Integer,Integer)]
        go (l,h)
            -- both l and h are negative
          | h < 0 = [(toUnsigned w l, toUnsigned w h)]
            -- only l is negative, split the range
          | l < 0 = [(toUnsigned w l, maxUnsigned w), (0,h)]
            -- both positive
          | otherwise = [(l,h)]


------------------------------------------------------------------------
-- Operations

-- | Return true if this is a non-empty range.
validRange :: NatRepr w -> Integer -> Integer -> Bool
validRange w l h = 0 <= l && l <= h && h <= maxUnsigned w

checkRanges :: NatRepr w -> [(Integer, Integer)] -> Bool
checkRanges w l = all (uncurry (validRange w)) l

-- | @range w l u@ returns domain containing all bitvectors formed
-- from the @w@ low order bits of some @i@ in @[l,u]@.  Note that per
-- @testBit@, the least significant bit has index @0@.
range :: (1 <= w) => NatRepr w -> Integer -> Integer -> BVDomain w
range w li ui =
  case modRange w li ui of
    InclusiveRange l u ->
      BVDomain { domainRanges = Map.singleton l u
               }
    ExclusiveRange l u ->
      BVDomain { domainRanges = Map.fromList [(0,l), (u,maxUnsigned w)]
               }
    AnyRange ->
      BVDomain { domainRanges = Map.singleton 0 (maxUnsigned w)
               }

-- | Return the empty domain.
empty :: (1 <= w) => NatRepr w -> BVDomain w
empty _ = BVDomain { domainRanges = Map.empty
                   }

-- | Represents all values
any :: (1 <= w) => NatRepr w -> BVDomain w
any w = BVDomain { domainRanges = Map.singleton 0 (maxUnsigned w)
                 }

-- | Create a bitvector domain representing the integer.
singleton :: (1 <= w) => NatRepr w -> Integer -> BVDomain w
singleton w v
  | 0 <= v && v <= maxUnsigned w = BVDomain { domainRanges = Map.singleton v v }
  | otherwise = error "singleton given invalid input."

-- | From an ascending list of elements.
-- The elements are assumed to be distinct.
fromAscEltList :: forall w
                  . (1 <= w)
                  => BVDomainParams
                  -> NatRepr w
                  -> [Integer]
                  -> BVDomain w
fromAscEltList params w l = fromList "asc" params w (fmap (\x -> (x,x)) l)

-- | Create a domain from a list of ranges.
fromList :: (1 <= w)
         => String
         -> BVDomainParams
         -> NatRepr w
         -> [(Integer, Integer)]
         -> BVDomain w
fromList nm params w rgs
  | Prelude.not (checkRanges w rgs) =
      error $ nm ++ " provided invalid values to range with width " ++ show w ++ "\n  "
         ++ show rgs
  | otherwise = boundedBVDomain nm params w $
    Fold.foldl' (\p (l,h) -> insertRange l h p) emptyInterBVDomain rgs

-- | Create a BVdomain from a list of ranges.
--
-- Let @res = modList nm params u ranges@, then for each pair
-- @(l,h)@ in @ranges@, there is a @x \in [l,h]@ then @(x mod 2^n)@
-- should be inn @res@.
modList :: forall u
          .  1 <= u
          => String
          -> BVDomainParams
          -> NatRepr u
          -> [(Integer,Integer)]
             -- List of ranges

          -> BVDomain u
modList nm params w rgs
    -- If the width exceeds maxInt, then just return anything (otherwise we can't even shift.
  | natValue w > fromIntegral (maxBound :: Int) = any w
  | otherwise =
    -- This entries over each range, and returns either @Nothing@ if
    -- the range contains all elements or the range.
    let mapRange :: [(Integer, Integer)]
                 -> [(Integer, Integer)]
                 -> BVDomain u
        mapRange processed [] = fromList nm params w processed
        mapRange processed ((lbound, ubound):next) =
          case modRange w lbound ubound of
            InclusiveRange low_lbound low_ubound ->
              mapRange ((low_lbound, low_ubound):processed) next
            ExclusiveRange low_ubound low_lbound ->
                mapRange ((0, low_ubound) : (low_lbound, rangeSize w - 1) : processed)
                         next
            AnyRange -> any w
     in mapRange [] rgs

-- | @concat x y@ returns domain where each element in @x@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @x@, and the least significant bits are @y@.
concat :: BVDomainParams
          -> NatRepr u
          -> BVDomain u
          -> NatRepr v
          -> BVDomain v
          -> BVDomain (u+v)
concat params wx x wy y = do
  let w = addNat wx wy
  let y_width_max = maxUnsigned wy
  let x_shift v = v `shiftL` widthVal wy
  let singletonRange v = (x_shift v + y_min, x_shift v + y_max)
        where Just y_min = domainUnsignedMin y
              Just y_max = domainUnsignedMax y
  case testLeq (knownNat :: NatRepr 1) w of
    Nothing -> error "internal: BVDomain.concat given bad width."
    Just LeqProof
      | isEmpty x -> empty w
      | isEmpty y -> empty w
      | isAny wy y -> fromList "concat" params w $ do
        (l,h) <- toList x
        return (x_shift l, x_shift h .|. y_width_max)
      | count x * rangeCount y <= toInteger (rangeLimit params) ->
        fromList "concat2" params w $ do
          v <- domainElts x
          (ly,hy) <- toList y
          return (x_shift v + ly, x_shift v + hy)

      | count x <= toInteger (rangeLimit params) ->
        fromList "concat3" params w $ do
          singletonRange <$> domainElts x

      | otherwise -> fromList "concat4" params w $ do
        (l,h) <- toList x
        let r | l == h    = singletonRange l
              | otherwise = (x_shift l, x_shift h + y_width_max)
        return r


-- | @select i n d@ selects @n@ bits starting from index @i@ from @d@.
select
  :: (1 <= n, i + n <= w)
  => BVDomainParams
  -> NatRepr i
  -> NatRepr n
  -> BVDomain w
  -> BVDomain n
select params i n x
  | Just Refl <- testEquality i (knownNat @0)
  = modList "select" params n (toList x)
  | otherwise = any n -- TODO

negate :: (1 <= w) => BVDomainParams -> NatRepr w -> BVDomain w -> BVDomain w
negate params w d = fromList "negate" params w r
  where r = concatMap go (toList d)
        sz = rangeSize w
        neg v = sz - v
        go (0,0) = [(0,0)]
        go (0,h) = [(0,0), (neg h, sz-1)]
        go (l,h) = [(neg h, neg l)]

add :: (1 <= w) => BVDomainParams -> NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
add params w x y = modList "add" params w $ do
  (xl,xh) <- toList x
  (yl,yh) <- toList y
  pure (xl + yl, xh + yh)

mul :: (1 <= w) => BVDomainParams -> NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
mul params w x y = modList "mul" params w $ do
  (xl,xh) <- toList x
  (yl,yh) <- toList y
  pure (xl * yl, xh * yh)

udiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
udiv w _x _y = any w -- TODO

urem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
urem w x y
  | Just (ylo,yhi) <- ubounds w y, 0 < ylo
  = let hi = case ubounds w x of
               Just (_,xhi) -> min (yhi - 1) xhi
               Nothing      -> (yhi - 1)
     in range w 0 hi

  | otherwise = any w

sdiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
sdiv w _x _y = any w -- TODO

srem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
srem w x y
  | Just (ylo,yhi) <- sbounds w y, 0 < ylo
  , Just (xlo,xhi) <- sbounds w x, 0 <= xlo
  = range w 0 (min (yhi - 1) xhi)

  | Just (ylo,yhi) <- sbounds w y, 0 < ylo
  , Just (xlo,xhi) <- sbounds w x, xhi < 0
  = range w (max (-(yhi - 1)) xlo) 0

  -- TODO, we could probably add ranges for negative denominators as well

  | otherwise = any w

-- | Return union of two domains.
union :: (1 <= w)
      => BVDomainParams
      -> NatRepr w
      -> BVDomain w
      -> BVDomain w
      -> BVDomain w
union params w x y = fromList "union" params w $ toList x ++ toList y

shl :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
shl w _x _y = any w -- TODO

lshr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
lshr w _x _y = any w -- TODO

ashr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
ashr w _x _y = any w -- TODO

zext :: (1 <= w, w+1 <= u) => BVDomain w -> NatRepr u -> BVDomain u
zext x _ = BVDomain (domainRanges x)

sext :: forall w u. (1 <= w, w+1 <= u) =>
  BVDomainParams ->
  NatRepr w ->
  BVDomain w ->
  NatRepr u ->
  BVDomain u
sext params w x u = do
  let wProof :: LeqProof 1 w
      wProof = LeqProof
      uProof :: LeqProof (w+1) u
      uProof = LeqProof
      fProof :: LeqProof 1 u
      fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof
  case fProof of
    LeqProof -> fromList "sext" params u $
      signedToUnsignedRanges u (toSignedRanges w x)

-- | Complement bits in range.
not :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w
not w _x = any w -- TODO

and :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
and w _x _y = any w -- TODO

or :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
or w _x _y = any w -- TODO

xor :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
xor w _x _y = any w -- TODO
