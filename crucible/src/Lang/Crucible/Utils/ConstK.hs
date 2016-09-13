{-# LANGUAGE PolyKinds #-}
module Lang.Crucible.Utils.ConstK
  ( ConstK(..)
  ) where

-- | A type wrapper around the CFG postdom to allow us to use a parameterized context.
newtype ConstK (a :: *) (b :: k) = ConstK a
