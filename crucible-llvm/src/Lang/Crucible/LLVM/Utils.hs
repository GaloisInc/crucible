------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Utils
-- Description      : Miscellaneous utility functions.
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
module Lang.Crucible.LLVM.Utils (applyUnless) where

-- | If the first argument is 'False', apply the second argument to the third.
-- Otherwise, simply return the third argument.
applyUnless :: Applicative f => Bool -> (a -> f a) -> a -> f a
applyUnless b f x = if b then pure x else f x
