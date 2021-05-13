{- |
Module           : ClockVector
Description      : Implementation of Vector Clocks
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

Defines a vector clock ADT as described in "Dynamic Partial-Order Reduction for
Model Checking Software" (Flanagan and Godefroid, 2005), which differs somewhat
from as described by Lamport, though not fundamentally.

At a high level, a vector clock VC is a mapping from events to timestamps. In a
distributed system, each process p will have its own vector clock VC(p).
VC(p)(x) is then the timestamp of event "x" according to process p.

If a vector of clocks VCs : ProcessID -> ProcessID -> Nat, then the usecase is that VC(p)(q) is the
last event of q that happened before p.
-}
{-# LANGUAGE RankNTypes #-}
module Crucibles.ClockVector where

import           Control.Lens
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)

newtype ClockVector p v = CV { getCV :: Map p v }
  deriving (Show)

-- | Denotes properties required of values used for timestamp.
-- We need a least value in the ordering.
class ClockVectorValue v where
  least :: v

instance ClockVectorValue Int where
  least = 0

-- | The empty vector clock.
cvEmpty :: Ord p => ClockVector p v
cvEmpty = CV mempty

cvMap :: Lens' (ClockVector p v) (Map p v)
cvMap = lens getCV (\cv m -> cv { getCV = m })

-- | Look up a timestamp value
cvAt :: (ClockVectorValue v, Ord p) => p -> Lens' (ClockVector p v) v
cvAt i = lens getter setter
  where
    getter (CV cv)   = fromMaybe least (Map.lookup i cv)
    setter (CV cv) v = CV (Map.insert i v cv)

-- | The important operation is to be able to take the maximum of two vector clocks, which
-- is computed pointwise.
maxClockVector :: (Ord p, Ord v) => ClockVector p v -> ClockVector p v -> ClockVector p v
maxClockVector cv1 cv2 =
  CV $ Map.unionWith max (getCV cv1) (getCV cv2)

-- | Take the maximum of a list of clock vectors.
maxClockVectors :: (Ord p, Ord v) => [ClockVector p v] -> ClockVector p v
maxClockVectors = foldl' maxClockVector (CV mempty)

-- | "Pretty print" a clock vector
ppCV :: (Show a1, Show a2) => ClockVector a1 a2 -> String
ppCV (CV m) =
  unlines [ show p ++ ": " ++ show v | (p, v) <- Map.toList m ]

ppCVs :: (Show a, Show a1, Show a2) => Map a (ClockVector a1 a2) -> String
ppCVs cvs =
  unlines [ show p ++ "\n" ++ ppCV cv | (p, cv) <- Map.toList cvs ]
