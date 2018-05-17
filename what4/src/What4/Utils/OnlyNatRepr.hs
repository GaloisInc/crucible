{-|
Module           : What4.Utils.OnlyNatRepr
Copyright        : (c) Galois
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Defines a GADT for indicating a base type must be a natural number.  Used for
restricting index types in MATLAB arrays.
-}
{-# LANGUAGE GADTs #-}
module What4.Utils.OnlyNatRepr
  ( OnlyNatRepr(..)
  , toBaseTypeRepr
  ) where

import Data.Hashable (Hashable(..))
import Data.Parameterized.Classes (HashableF(..))
import What4.BaseTypes

-- | This provides a GADT instance used to indicate a 'BaseType' must have
-- value 'BaseNatType'.
data OnlyNatRepr tp
   = (tp ~ BaseNatType) => OnlyNatRepr

instance TestEquality OnlyNatRepr where
  testEquality OnlyNatRepr OnlyNatRepr = Just Refl

instance Hashable (OnlyNatRepr tp) where
  hashWithSalt s OnlyNatRepr = s

instance HashableF OnlyNatRepr where
  hashWithSaltF = hashWithSalt

toBaseTypeRepr :: OnlyNatRepr tp -> BaseTypeRepr tp
toBaseTypeRepr OnlyNatRepr = BaseNatRepr
