{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Utils.BVDomain.Map
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
  , trunc
  , not
  , and
  , or
  , xor
  ) where

import Control.Exception (assert)
import Control.Lens ((&), over, both)
import qualified Data.Bits as Bits
import Data.Bits hiding (testBit, xor)
import qualified Data.Foldable as Fold
import Data.List hiding (and, any, concat, or, union)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Parameterized.NatRepr

import GHC.TypeLits

import Prelude hiding (any, concat, negate, not, and, or)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), (<*>))
#endif

-- | @halfRange n@ returns @2^(n-1)@.
halfRange :: NatRepr w -> Integer
halfRange w = 2^(natValue w - 1)

rangeSize :: NatRepr w -> Integer
rangeSize w = 2^(natValue w)

------------------------------------------------------------------------
-- BVDomain Parameters

-- | Parameters for a domain
newtype BVDomainParams = DP { rangeLimit :: Int }

defaultBVDomainParams :: BVDomainParams
defaultBVDomainParams = DP { rangeLimit = 2 }

------------------------------------------------------------------------
-- BVDomain definition

newtype BVDomain (w :: Nat)
   = BVDomain { -- | Map from lower bounds to upper bound for that range.
                -- All integers are unsigned.
                -- The ranges are normalized so that no distinct ranges
                -- are overlapping or contiguous.
                domainRanges :: (Map Integer Integer)
              }

-- | Checks the invariants that should be mainined by BVDomain.
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

domainUnsignedMin :: BVDomain w -> Maybe Integer
domainUnsignedMin d | isEmpty d = Nothing
                    | otherwise = Just $! fst (Map.findMin (domainRanges d))

domainUnsignedMax :: BVDomain w -> Maybe Integer
domainUnsignedMax d | isEmpty d = Nothing
                    | otherwise = Just $! snd (Map.findMax (domainRanges d))

-- | Return minimal value signed value contained in domain.
domainSignedMin :: NatRepr w -> BVDomain w -> Maybe Integer
domainSignedMin w d
  | Just neg_l <- domainGE (halfRange w) d =
    Just $! neg_l - rangeSize w
  | otherwise = domainUnsignedMin d

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
        -> Integer -- ^ Index of bit (least-significant bit has index 0)
        -> Maybe Bool
testBit w d i = assert (i < natValue w) $
    case uncurry testRange <$> toList d of
      (mb@Just{}:r) | all (== mb) r -> mb
      _ -> Nothing
  where j = fromInteger i
        testRange :: Integer -> Integer -> Maybe Bool
        testRange l h | (l `shiftR` j) == (h `shiftR` j) =
                        Just (l `Bits.testBit` j)
                      | otherwise = Nothing

------------------------------------------------------------------------
-- Internal Methods


-- | Maps the size of each gap to the set of end addresses for a gap
-- of that size.
type GapMap = Map Integer (Set Integer)

gapSize :: Integer -> Integer -> Integer
gapSize h_prev l = l - h_prev

-- | @deleteGapEntry h l gm@ deletes the gap from @h@ to @l@ from @gm@.
deleteGapEntry :: Integer -> Integer -> GapMap -> GapMap
deleteGapEntry h_prev l gm = Map.adjust (Set.delete l) (gapSize h_prev l) gm

insertGapEntry :: Integer -- ^ Upper bound before start of gap.
               -> Integer -- ^ Lower bound that ends gap.
               -> GapMap
               -> GapMap
insertGapEntry h_prev l gm = Map.alter (Just . f) sz gm
  where sz = gapSize h_prev l
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

-- | Create bounded BV domain with given size from gap map and range map.
boundedBVDomain :: BVDomainParams -- ^ Maximum size of BVDomain range
                -> (GapMap, Map Integer Integer)
                -> BVDomain w
boundedBVDomain params (gm,m0) = BVDomain { domainRanges = d }
  where cnt = rangeLimit params
        d = foldl' f m0 (take (Map.size m0 - cnt) (gapsToMerge gm))
        f :: Map Integer Integer
          -> Integer -- ^ Lower bound of range to delete
          -> Map Integer Integer
        f m l = m & Map.delete l
                  & Map.insert l_prev h
          where Just (l_prev,_) = Map.lookupLT l m
                Just h = Map.lookup l m

-- | @insertRange' l h d@ inserts the range [l,h] into @d@.
insertRange' :: Integer
             -> Integer
             -> (GapMap, Map Integer Integer)
             -> (GapMap, Map Integer Integer)
insertRange' l h (gm, m) = seq l $ seq h $ seq gm $ seq m $
  case Map.lookupLE (h+1) m of
    -- Look for overlapping range to delete.
    Just (l_prev, h_prev)
      -- Check to see if current range subsumes new range.
      | l_prev <= l && h <= h_prev -> (gm,m)
        -- Check to see if they overlap.
      | h_prev + 1 >= l ->
        let l' = min l l_prev
            h' = max h h_prev
            gm' = deleteGapRange l_prev h_prev m gm
            m' = Map.delete l_prev m
         in insertRange' l' h' (gm',m')
    _ -> (insertGapRange l h m gm, Map.insert l h m)


------------------------------------------------------------------------
-- Internal operations

-- | Convert unsigned ranges to signed ranges
toSignedRanges :: (1 <= w) => NatRepr w -> BVDomain w -> [(Integer,Integer)]
toSignedRanges w d = go (toList d)
  where go :: [(Integer,Integer)] -> [(Integer,Integer)]
        go [] = []
        go ((l,h):r)
          | h <= maxSigned w = (l,h):go r
          | l <= maxSigned w =
            (l, maxSigned w) : (minSigned w, h - rangeSize w) : go2 r
          | otherwise =
            go2 r
        -- Decrement each pair
        go2 :: [(Integer,Integer)] -> [(Integer,Integer)]
        go2 = fmap (\(l,h) -> (l - rangeSize w, h - rangeSize w))

-- | Return list of signed ranges in domain.
signedToUnsignedRanges :: NatRepr w -> [(Integer,Integer)] -> [(Integer,Integer)]
signedToUnsignedRanges w l0 = concatMap go l0
  where go :: (Integer,Integer) -> [(Integer,Integer)]
        go (l,h)
          | h < 0 = [(toUnsigned w l, toUnsigned w h)]
          | l < 0 = [(toUnsigned w l, maxUnsigned w), (0,h)]
          | otherwise = [(l,h)]


------------------------------------------------------------------------
-- Operations

-- | @range w l h@ returns domain containing values @l@ to @h@.
range :: (1 <= w) => NatRepr w -> Integer -> Integer -> BVDomain w
range w l h = assert (0 <= l && l <= h && h <= maxUnsigned w) $
  BVDomain { domainRanges = Map.singleton l h
           }

empty :: (1 <= w) => NatRepr w -> BVDomain w
empty _ = BVDomain { domainRanges = Map.empty
                   }

any :: (1 <= w) => NatRepr w -> BVDomain w
any w = range w 0 (maxUnsigned w)

-- | Create a bitvector domain representing the integer.
--
singleton :: (1 <= w) => NatRepr w -> Integer -> BVDomain w
singleton w v = range w v v

validRange :: NatRepr w -> Integer -> Integer -> Bool
validRange w l h = 0 <= l && l <= h && h <= maxUnsigned w

checkRanges :: NatRepr w -> [(Integer, Integer)] -> Bool
checkRanges w l = all (uncurry (validRange w)) l

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
fromList _ params w ranges =
    assert (checkRanges w ranges) (boundedBVDomain params res)
  where empty_maps = (Map.empty, Map.empty)
        res  = Fold.foldl' (\p (l,h) -> insertRange' l h p) empty_maps ranges

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
select :: (1 <= u) => Integer -> NatRepr u -> BVDomain w -> BVDomain u
select _i n _d = any n -- TODO

{-
splitRange :: Integer -> BVDomain w -> [Either (Integer,Integer) (Integer,Integer)]
splitRange v d = go (toList d)
  where go [] = []
        go r@((l,_):_) | l >= v = Right <$> r
        go ((l,h):r)   | h >= v = Left (l,v-1) : (Right <$> ((v,h):r))
        go (p:r) = Left p : go r
-}

negate :: (1 <= w) => BVDomainParams -> NatRepr w -> BVDomain w -> BVDomain w
negate params w d = fromList "negate" params w r
  where r = concatMap go (toList d)
        sz = rangeSize w
        neg v = sz - v
        go (0,0) = [(0,0)]
        go (0,h) = [(0,0), (neg h, sz-1)]
        go (l,h) = [(neg h, neg l)]

modRange :: NatRepr w -> Integer -> Integer -> [(Integer,Integer)]
modRange w l0 h0
    | ld == hd = assert (lm <= hm) $ [(lm,hm)]
    | otherwise = assert (ld < hd) $ [(lm, sz-1), (0, hm)]
  where sz = rangeSize w
        (ld,lm) = l0 `divMod` sz
        (hd,hm) = h0 `divMod` sz

add :: (1 <= w) => BVDomainParams -> NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
add params w x y =
  fromList "add" params w $ do
    (xl,xh) <- toList x
    (yl,yh) <- toList y
    modRange w (xl + yl) (xh + yh)

mul :: (1 <= w) => BVDomainParams -> NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
mul params w x y = fromList "mul" params w $ do
  (xl,xh) <- toList x
  (yl,yh) <- toList y
  modRange w (xl * yl) (xh * yh)

udiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
udiv w _x _y = any w -- TODO

urem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
urem w _x _y = any w -- TODO

sdiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
sdiv w _x _y = any w -- TODO

srem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
srem w _x _y = any w -- TODO

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

sext :: forall w u
     .  (1 <= w, w+1 <= u)
     => BVDomainParams
     -> NatRepr w
     -> BVDomain w
     -> NatRepr u
     -> BVDomain u
sext params uw x w = do
  let wProof :: LeqProof 1 w
      wProof = LeqProof
      uProof :: LeqProof (w+1) u
      uProof = LeqProof
      fProof :: LeqProof 1 u
      fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof
  case fProof of
    LeqProof -> fromList "sext" params w $ do
      signedToUnsignedRanges w (toSignedRanges uw x)

trunc :: (1 <= u, u+1 <= w) => BVDomainParams -> BVDomain w -> NatRepr u -> BVDomain u
trunc params x w =
  fromList "trunc" params w $ do
    fmap (over both (toUnsigned w)) (toList x)

-- | Complement bits in range.
not :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w
not w _x = any w -- TODO

and :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
and w _x _y = any w -- TODO

or :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
or w _x _y = any w -- TODO

xor :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
xor w _x _y = any w -- TODO
