{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module What4.IndexLit where

import Data.Parameterized.Classes
import Numeric.Natural

import What4.BaseTypes

------------------------------------------------------------------------
-- IndexLit

-- | This represents a concrete index value, and is used for creating
-- arrays.
data IndexLit idx where
  NatIndexLit :: !Natural -> IndexLit BaseNatType
  BVIndexLit :: (1 <= w) => !(NatRepr w) -> !Integer ->  IndexLit (BaseBVType w)

instance Eq (IndexLit tp) where
  x == y = isJust (testEquality x y)

instance TestEquality IndexLit where
  testEquality (NatIndexLit x) (NatIndexLit y) =
    if x == y then
     Just Refl
     else
     Nothing
  testEquality (BVIndexLit wx x) (BVIndexLit wy y) = do
    Refl <- testEquality wx wy
    if x == y then Just Refl else Nothing
  testEquality _ _ =
    Nothing

instance OrdF IndexLit where
  compareF (NatIndexLit x) (NatIndexLit y) = fromOrdering (compare x y)
  compareF NatIndexLit{} _ = LTF
  compareF _ NatIndexLit{} = GTF
  compareF (BVIndexLit wx x) (BVIndexLit wy y) =
    case compareF wx wy of
      LTF -> LTF
      GTF -> GTF
      EQF -> fromOrdering (compare x y)

instance Hashable (IndexLit tp) where
  hashWithSalt = hashIndexLit
  {-# INLINE hashWithSalt #-}


hashIndexLit :: Int -> IndexLit idx -> Int
s `hashIndexLit` (NatIndexLit i) =
    s `hashWithSalt` (0::Int)
      `hashWithSalt` i
s `hashIndexLit` (BVIndexLit w i) =
    s `hashWithSalt` (1::Int)
      `hashWithSalt` w
      `hashWithSalt` i

instance HashableF IndexLit where
  hashWithSaltF = hashIndexLit

instance Show (IndexLit tp) where
  showsPrec p (NatIndexLit i) s = showsPrec p i s
  showsPrec p (BVIndexLit w i) s = showsPrec p i ("::[" ++ shows w (']' : s))

instance ShowF IndexLit
