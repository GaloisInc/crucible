{-|
Module      : What4.Utils.BVDomain.Empty
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

Defines an empty bitvector domain compatible with
'What4.Utils.BVDomain.Map' that can be used for
comparing the performance of different implementations.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeOperators #-}
#if MIN_VERSION_base(4,9,0)
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
module What4.Utils.BVDomain.Empty
  ( BVDomain
    -- * Projection function
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
  , trunc
  , not
  , and
  , or
  , xor
  ) where

import Control.Exception (assert)
import Data.Parameterized.NatRepr

import GHC.TypeLits

import Prelude hiding (any, concat, negate, not, and, or)

------------------------------------------------------------------------
-- BVDomain definition

newtype BVDomain (w :: Nat) = BVDomain ()

-- | Return value if this is a singleton.
asSingleton :: (1 <= w) => BVDomain w -> Maybe Integer
asSingleton _ = Nothing

-- | Return signed bounds for domain.  Returns Nothing if the domain is empty.
sbounds :: (1 <= w) => NatRepr w -> BVDomain w -> Maybe (Integer, Integer)
sbounds w _ = Just (minSigned w, maxSigned w)

-- | Return unsigned bounds for domain.  Returns Nothing if the domain is empty.
ubounds :: (1 <= w) => NatRepr w -> BVDomain w -> Maybe (Integer, Integer)
ubounds w _ = Just (0, maxUnsigned w)

domainsOverlap :: BVDomain w -> BVDomain w -> Bool
domainsOverlap _ _ = True

eq :: (1 <= w) => BVDomain w -> BVDomain w -> Maybe Bool
eq _ _ = Nothing


-- | Check if all elements in one domain are less than all elements in other.
slt :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> Maybe Bool
slt _ _ _ = Nothing

-- | Check if all elements in one domain are less than all elements in other.
ult :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> Maybe Bool
ult _ _ _ = Nothing

-- | Return true if bits in domain are set.
testBit :: (1 <= w)
        => NatRepr w
        -> BVDomain w
        -> Integer -- ^ Index of bit (least-significant bit has index 0)
        -> Maybe Bool
testBit _ _ _ = Nothing

ranges :: NatRepr w -> BVDomain w -> [(Integer, Integer)]
ranges w _ = [(0, maxUnsigned w)]

------------------------------------------------------------------------
-- Operations

-- | @range w l h@ returns domain containing values @l@ to @h@.
range :: (1 <= w) => NatRepr w -> Integer -> Integer -> BVDomain w
range w l h = assert (0 <= l && l <= h && h <= maxUnsigned w) $ BVDomain ()

empty :: (1 <= w) => NatRepr w -> BVDomain w
empty _ = BVDomain ()

any :: (1 <= w) => NatRepr w -> BVDomain w
any _ = BVDomain ()


-- | From an ascending list of elements.
fromAscEltList :: NatRepr w -> [Integer] -> BVDomain w
fromAscEltList _ _ = BVDomain ()

singleton :: (1 <= w) => NatRepr w -> Integer -> BVDomain w
singleton _ _ = BVDomain ()

-- | @concat x y@ returns domain where each element in @x@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @x@, and the least significant bits are @y@.
concat :: NatRepr u -> BVDomain u -> NatRepr v -> BVDomain v -> BVDomain (u+v)
concat _ _ _ _ = BVDomain ()

-- | @select i n d@ selects @n@ bits starting from index @i@ from @d@.
select :: (1 <= u) => Integer -> NatRepr u -> BVDomain w -> BVDomain u
select _i _ _d = BVDomain ()

negate :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w
negate w _ = any w

add :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
add w _ _ = any w

mul :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
mul w _ _ = any w

udiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
udiv w _x _y = any w -- TODO

urem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
urem w _x _y = any w -- TODO

sdiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
sdiv w _x _y = any w -- TODO

srem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
srem w _x _y = any w -- TODO

-- | Return union of two domains.
union :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
union _ _ _ = BVDomain ()

shl :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
shl w _x _y = any w -- TODO

lshr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
lshr w _x _y = any w -- TODO

ashr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
ashr w _x _y = any w -- TODO

zext :: (1 <= w, w+1 <= u) => BVDomain w -> NatRepr u -> BVDomain u
zext _x w =
  case isPosNat w of
    Just LeqProof -> any w -- TODO
    Nothing -> error $ "BVDomain.zext bad value"

sext :: (1 <= w, w+1 <= u) => BVDomain w -> NatRepr u -> BVDomain u
sext _x w =
  case isPosNat w of
    Just LeqProof -> any w -- TODO
    Nothing -> error $ "BVDomain.sext bad value"

trunc :: (1 <= u, u+1 <= w) => BVDomain w -> NatRepr u -> BVDomain u
trunc _x w = any w -- TODO

-- | Complement bits in range.
not :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w
not w _x = any w -- TODO

and :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
and w _x _y = any w -- TODO

or :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
or w _x _y = any w -- TODO

xor :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
xor w _x _y = any w -- TODO
