{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Utils
-- Description      : Miscellaneous utility functions.
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
module Lang.Crucible.LLVM.Utils
  ( applyUnless
  , sextendBVTo
  ) where

import What4.Interface

import Lang.Crucible.Backend
import Lang.Crucible.Panic (panic)

-- | If the first argument is 'False', apply the second argument to the third.
-- Otherwise, simply return the third argument.
applyUnless :: Applicative f => Bool -> (a -> f a) -> a -> f a
applyUnless b f x = if b then pure x else f x

-- | Convert a 'SymBV' value of width @w@ to width @w'@, performing sign
-- extension or truncation as needed.
sextendBVTo :: (1 <= w, 1 <= w', IsSymInterface sym)
            => sym
            -> NatRepr w
            -> NatRepr w'
            -> SymExpr sym (BaseBVType w)
            -> IO (SymExpr sym (BaseBVType w'))
sextendBVTo sym w w' x
  | Just Refl <- testEquality w w' = return x
  | Just LeqProof <- testLeq (incNat w) w' = bvSext sym w' x
  | Just LeqProof <- testLeq (incNat w') w = bvTrunc sym w' x
  | otherwise = panic "sextendBVTo"
                  [ "Impossible widths!"
                  , show w
                  , show w'
                  ]
