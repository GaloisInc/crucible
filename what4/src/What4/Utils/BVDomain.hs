{-|
Module      : What4.Utils.BVDomain
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : huffman@galois.com

Provides an interval-based implementation of bitvector abstract
domains.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.BVDomain
  ( BVDomain
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
  , any
  , singleton
  , range
  , fromAscEltList
  , union
  , concat
  , select
  , zext
  , sext
    -- ** Shifts
  , shl
  , lshr
  , ashr
    -- ** Arithmetic
  , add
  , negate
  , scale
  , mul
  , udiv
  , urem
  , sdiv
  , srem
    -- ** Bitwise
  , What4.Utils.BVDomain.not
  , and
  , or
  , xor
  ) where

import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import           Data.Parameterized.NatRepr
import           Numeric.Natural
import           GHC.TypeNats
import           GHC.Stack

import           Prelude hiding (any, concat, negate, and, or)

--------------------------------------------------------------------------------
-- BVDomain definition

-- | A value of type @'BVDomain' w@ represents a set of bitvectors of
-- width @w@. Each 'BVDomain' can represent a single contiguous
-- interval of bitvectors that may wrap around from -1 to 0.
data BVDomain (w :: Nat)
  = BVDAny !Integer
  -- ^ The set of all bitvectors of width @w@. Argument caches @2^w-1@.
  | BVDInterval !Integer !Integer !Integer
  -- ^ Intervals are represented by a starting value and a size.
  -- @BVDInterval mask l d@ represents the set of values of the form
  -- @x mod 2^w@ for @x@ such that @l <= x <= l + d@. It should
  -- satisfy the invariants @0 <= l < 2^w@ and @0 <= d < 2^w@. The
  -- first argument caches the value @2^w-1@.
  deriving Show

bvdMask :: BVDomain w -> Integer
bvdMask x =
  case x of
    BVDAny mask -> mask
    BVDInterval mask _ _ -> mask

--------------------------------------------------------------------------------

-- | @halfRange n@ returns @2^(n-1)@.
halfRange :: (1 <= w) => NatRepr w -> Integer
halfRange w = bit (widthVal w - 1)

--------------------------------------------------------------------------------
-- Projection functions

-- | Convert domain to list of ranges.
ranges :: NatRepr w -> BVDomain w -> [(Integer, Integer)]
ranges _w x =
  case x of
    BVDAny mask -> [(0, mask)]
    BVDInterval mask xl xd
      | xh > mask -> [(0, xh .&. mask), (xl, mask)]
      | otherwise -> [(xl, xh)]
      where xh = xl + xd

-- | Return value if this is a singleton.
asSingleton :: BVDomain w -> Maybe Integer
asSingleton x =
  case x of
    BVDAny _ -> Nothing
    BVDInterval _ xl xd
      | xd == 0 -> Just xl
      | otherwise -> Nothing

isSingletonZero :: BVDomain w -> Bool
isSingletonZero x =
  case x of
    BVDInterval _ 0 0 -> True
    _ -> False

isBVDAny :: BVDomain w -> Bool
isBVDAny x =
  case x of
    BVDAny {} -> True
    BVDInterval {} -> False

-- | Return unsigned bounds for domain.
ubounds :: BVDomain w -> (Integer, Integer)
ubounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask al aw
      | ah > mask -> (0, mask)
      | otherwise -> (al, ah)
      where ah = al + aw

-- | Return signed bounds for domain.
sbounds :: (1 <= w) => NatRepr w -> BVDomain w -> (Integer, Integer)
sbounds w a = (lo - delta, hi - delta)
  where
    delta = halfRange w
    (lo, hi) = ubounds (add a (BVDInterval (bvdMask a) delta 0))

-- | Return true if domains contain a common element.
domainsOverlap :: BVDomain w -> BVDomain w -> Bool
domainsOverlap a b =
  case a of
    BVDAny _ -> True
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> True
        BVDInterval mask bl bw ->
          diff <= bw || diff + aw > mask
          where diff = (al - bl) .&. mask

eq :: BVDomain w -> BVDomain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b = Just (x == y)
  | domainsOverlap a b == False = Just False
  | otherwise = Nothing

-- | Check if all elements in one domain are less than all elements in other.
slt :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> Maybe Bool
slt w a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = sbounds w a
    (b_min, b_max) = sbounds w b

-- | Check if all elements in one domain are less than all elements in other.
ult :: (1 <= w) => BVDomain w -> BVDomain w -> Maybe Bool
ult a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = ubounds a
    (b_min, b_max) = ubounds b

-- | Return @Just@ if every bitvector in the domain has the same bit
-- at the given index.
testBit ::
  NatRepr w ->
  BVDomain w ->
  Natural {- ^ Index of bit (least-significant bit has index 0) -} ->
  Maybe Bool
testBit w a i =
  if i >= natValue w then Nothing else
  case a of
    BVDAny _ -> Nothing
    BVDInterval _ al aw
      | (al `shiftR` j) == (ah `shiftR` j) ->
        Just (al `Bits.testBit` j)
      | otherwise ->
        Nothing
      where
        j = fromIntegral i
        ah = al + aw

--------------------------------------------------------------------------------
-- Operations

-- | Represents all values
any :: (1 <= w) => NatRepr w -> BVDomain w
any w = BVDAny (maxUnsigned w)

-- | Create a bitvector domain representing the integer.
singleton :: (HasCallStack, 1 <= w) => NatRepr w -> Integer -> BVDomain w
singleton w x = BVDInterval mask (x .&. mask) 0
  where mask = maxUnsigned w

-- | @range w l u@ returns domain containing all bitvectors formed
-- from the @w@ low order bits of some @i@ in @[l,u]@.  Note that per
-- @testBit@, the least significant bit has index @0@.
range :: NatRepr w -> Integer -> Integer -> BVDomain w
range w al ah = interval mask al ((ah - al) .&. mask)
  where mask = maxUnsigned w

-- | Unsafe constructor for internal use only. Caller must ensure that
-- @mask = maxUnsigned w@, and that @aw@ is non-negative.
interval :: Integer -> Integer -> Integer -> BVDomain w
interval mask al aw =
  if aw >= mask then BVDAny mask else BVDInterval mask (al .&. mask) aw

-- | Create an abstract domain from an ascending list of elements.
-- The elements are assumed to be distinct.
fromAscEltList :: (1 <= w) => NatRepr w -> [Integer] -> BVDomain w
fromAscEltList w [] = singleton w 0
fromAscEltList w [x] = singleton w x
fromAscEltList w (x0 : x1 : xs) = go (x0, x0) (x1, x1) xs
  where
    -- Invariant: the gap between @b@ and @c@ is the biggest we've
    -- seen between adjacent values so far.
    go (a, b) (c, d) [] = union (range w a b) (range w c d)
    go (a, b) (c, d) (e : rest)
      | e - d > c - b = go (a, d) (e, e) rest
      | otherwise     = go (a, b) (c, e) rest

-- | Return union of two domains.
union :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
union a b =
  case a of
    BVDAny _ -> a
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> b
        BVDInterval mask bl bw ->
          interval mask cl (ch - cl)
          where
            size = mask + 1
            ac = 2 * al + aw -- twice the average value of a
            bc = 2 * bl + bw -- twice the average value of b
            -- If the averages are 2^(w-1) or more apart,
            -- then shift the lower interval up by 2^w.
            al' = if ac + mask < bc then al + size else al
            bl' = if bc + mask < ac then bl + size else bl
            ah' = al' + aw
            bh' = bl' + bw
            cl = min al' bl'
            ch = max ah' bh'

-- | @concat a y@ returns domain where each element in @a@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @a@, and the least significant bits are @y@.
concat :: NatRepr u -> BVDomain u -> NatRepr v -> BVDomain v -> BVDomain (u + v)
concat u a v b =
  case a of
    BVDAny _ -> BVDAny mask
    BVDInterval _ al aw -> interval mask (cat al bl) (cat aw bw)
  where
    cat i j = i `shiftL` widthVal v + j
    mask = maxUnsigned (addNat u v)
    (bl, bh) = ubounds b
    bw = bh - bl

-- | @shrink i a@ drops the @i@ least significant bits from @a@.
shrink ::
  NatRepr i ->
  BVDomain (i + n) -> BVDomain n
shrink i a =
  case a of
    BVDAny mask -> BVDAny (shr mask)
    BVDInterval mask al aw ->
      interval (shr mask) bl (bh - bl)
      where
        bl = shr al
        bh = shr (al + aw)
  where
    shr x = x `shiftR` widthVal i

-- | @trunc n d@ selects the @n@ least significant bits from @d@.
trunc ::
  (n <= w) =>
  NatRepr n ->
  BVDomain w -> BVDomain n
trunc n a =
  case a of
    BVDAny _ -> BVDAny mask
    BVDInterval _ al aw -> interval mask al aw
  where
    mask = maxUnsigned n

-- | @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  BVDomain w -> BVDomain n
select i n a = shrink i (trunc (addNat i n) a)

zext :: (1 <= w, w+1 <= u) => BVDomain w -> NatRepr u -> BVDomain u
zext a u = range u al ah
  where (al, ah) = ubounds a

sext ::
  forall w u. (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  BVDomain w ->
  NatRepr u ->
  BVDomain u
sext w a u =
  case fProof of
    LeqProof ->
      range u al ah
      where (al, ah) = sbounds w a
  where
    wProof :: LeqProof 1 w
    wProof = LeqProof
    uProof :: LeqProof (w+1) u
    uProof = LeqProof
    fProof :: LeqProof 1 u
    fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof

--------------------------------------------------------------------------------
-- Shifts

shl :: BVDomain w -> BVDomain w -> BVDomain w
shl a b
  | isBVDAny a = a
  | isSingletonZero a = a
  | isSingletonZero b = a
  | otherwise = interval mask lo (hi - lo)
    where
      mask = bvdMask a
      size = mask + 1
      (bl, bh) = ubounds b
      bl' = clamp bl
      bh' = clamp bh
      -- compute bounds for c = 2^b
      cl = if (mask `shiftR` bl' == 0) then size else bit bl'
      ch = if (mask `shiftR` bh' == 0) then size else bit bh'
      (lo, hi) = mulRange (zbounds a) (cl, ch)

lshr :: BVDomain w -> BVDomain w -> BVDomain w
lshr a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    cl = al `shiftR` clamp bh
    ch = ah `shiftR` clamp bl

ashr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
ashr w a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = sbounds w a
    (bl, bh) = ubounds b
    cl = al `shiftR` (if al < 0 then clamp bl else clamp bh)
    ch = ah `shiftR` (if ah < 0 then clamp bh else clamp bl)

-- | Return nearest representable Int, suitable for use as a shift amount.
clamp :: Integer -> Int
clamp x
  | x > toInteger (maxBound :: Int) = maxBound
  | x < toInteger (minBound :: Int) = minBound
  | otherwise = fromInteger x

--------------------------------------------------------------------------------
-- Arithmetic

add :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
add a b =
  case a of
    BVDAny _ -> a
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> b
        BVDInterval mask bl bw ->
          interval mask (al + bl) (aw + bw)

negate :: (1 <= w) => BVDomain w -> BVDomain w
negate a =
  case a of
    BVDAny _ -> a
    BVDInterval mask al aw -> BVDInterval mask ((-ah) .&. mask) aw
      where ah = al + aw

scale :: (1 <= w) => Integer -> BVDomain w -> BVDomain w
scale k a
  | k == 0 = BVDInterval (bvdMask a) 0 0
  | k == 1 = a
  | otherwise =
    case a of
      BVDAny _ -> a
      BVDInterval mask al aw
        | k >= 0 -> interval mask (k * al) (k * aw)
        | otherwise -> interval mask (k * ah) (k * aw)
        where ah = al + aw

mul :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
mul a b
  | isSingletonZero a = a
  | isSingletonZero b = b
  | isBVDAny a = a
  | isBVDAny b = b
  | otherwise = interval mask cl (ch - cl)
    where
      mask = bvdMask a
      (cl, ch) = mulRange (zbounds a) (zbounds b)

-- | Choose a representative integer range (positive or negative) for
-- the given bitvector domain such that the endpoints are as close to
-- zero as possible.
zbounds :: BVDomain w -> (Integer, Integer)
zbounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask lo sz -> (lo', lo' + sz)
      where lo' = if 2*lo + sz > mask then lo - (mask + 1) else lo

mulRange :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
mulRange (al, ah) (bl, bh) = (cl, ch)
  where
    (albl, albh) = scaleRange al (bl, bh)
    (ahbl, ahbh) = scaleRange ah (bl, bh)
    cl = min albl ahbl
    ch = max albh ahbh

scaleRange :: Integer -> (Integer, Integer) -> (Integer, Integer)
scaleRange k (lo, hi)
  | k < 0 = (k * hi, k * lo)
  | otherwise = (k * lo, k * hi)

udiv :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
udiv a b = interval mask ql (qh - ql)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    ql = al `div` max 1 bh -- assume that division by 0 does not happen
    qh = ah `div` max 1 bl -- assume that division by 0 does not happen

urem :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
urem a b
  | qh == ql = interval mask rl (rh - rl)
  | otherwise = interval mask 0 (bh - 1)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    (ql, rl) = al `divMod` max 1 bh -- assume that division by 0 does not happen
    (qh, rh) = ah `divMod` max 1 bl -- assume that division by 0 does not happen

-- | Interval arithmetic for integer division (rounding towards 0).
-- Given @a@ in @[al..ah]@ and @b@ in @[bl..bh]@, @sdivRange (al, ah)
-- (bl, bh)@ returns @(ql, qh)@ such that @a `quot` b@ is in
-- @[ql..qh]@.
sdivRange :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
sdivRange (al, ah) (bl, bh)
  | bl >= 0 =
    (al `quot` max 1 (if al < 0 then bl else bh),
     ah `quot` max 1 (if ah > 0 then bl else bh))
  | bh <= 0 =
    (ah `quot` min (-1) (if ah > 0 then bh else bl),
     al `quot` min (-1) (if al < 0 then bh else bl))
  | otherwise = -- interval [bl..bh] includes [-1..+1]
    (min al (-ah), max (-al) ah)

sdiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
sdiv w a b = interval mask ql (qh - ql)
  where
    mask = bvdMask a
    (ql, qh) = sdivRange (sbounds w a) (sbounds w b)

srem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
srem w a b =
  if ql == qh then
    (if ql < 0
     then interval mask (al - ql * bl) (aw - ql * bw)
     else interval mask (al - ql * bh) (aw + ql * bw))
  else interval mask rl (rh - rl)
  where
    mask = bvdMask a
    (al, ah) = sbounds w a
    (bl, bh) = sbounds w b
    (ql, qh) = sdivRange (al, ah) (bl, bh)
    rl = if al < 0 then min (bl+1) (-bh+1) else 0
    rh = if ah > 0 then max (-bl-1) (bh-1) else 0
    aw = ah - al
    bw = bh - bl

--------------------------------------------------------------------------------
-- Bitwise logical

-- | Complement bits in range.
not :: BVDomain w -> BVDomain w
not a =
  case a of
    BVDAny _ -> a
    BVDInterval mask al aw ->
      BVDInterval mask (Bits.complement ah .&. mask) aw
      where ah = al + aw

and :: BVDomain w -> BVDomain w -> BVDomain w
and a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = bitbounds a
    (bl, bh) = bitbounds b
    (cl, ch) = (al .&. bl, ah .&. bh)

or :: BVDomain w -> BVDomain w -> BVDomain w
or a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = bitbounds a
    (bl, bh) = bitbounds b
    (cl, ch) = (al .|. bl, ah .|. bh)

xor :: BVDomain w -> BVDomain w -> BVDomain w
xor a b =
  case a of
    BVDAny _ -> a
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> b
        BVDInterval mask bl bw ->
          interval mask cl cu
          where
            au = unknowns al (al + aw)
            bu = unknowns bl (bl + bw)
            cu = au .|. bu
            cl = (al `Bits.xor` cl) .&. complement cu

-- | Return bitwise bounds for domain (i.e. logical AND of all
-- possible values, paired with logical OR of all possible values).
bitbounds :: BVDomain w -> (Integer, Integer)
bitbounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask al aw
      | al + aw > mask -> (0, mask)
      | otherwise -> (al .&. complement au, al .|. au)
      where au = unknowns al (al + aw)

-- | @unknowns lo hi@ returns a bitmask representing the set of bit
-- positions whose values are not constant throughout the range
-- @lo..hi@.
unknowns :: Integer -> Integer -> Integer
unknowns lo hi = fillright 1 (lo `Bits.xor` hi)
  where
    -- @fillright 1 x@ rounds up @x@ to the nearest 2^n-1.
    fillright :: Int -> Integer -> Integer
    fillright i x
      | x' == x = x
      | otherwise = fillright (2 * i) x'
      where x' = x .|. (x `shiftR` i)
