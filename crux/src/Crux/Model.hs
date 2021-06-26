-- | This file is almost exactly the same as crucible-c/src/Model.hs

{-# Language DataKinds #-}
{-# Language PolyKinds #-}
{-# Language Rank2Types #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Crux.Model where

import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Pair (Pair(..))
import qualified Numeric as N
import           LibBF (BigFloat)
import qualified LibBF as BF

import           Lang.Crucible.Types

import           Crux.UI.JS
import           Crux.Types


emptyModelView :: ModelView
emptyModelView = ModelView $ MapF.fromList
  [ noVals (BaseBVRepr (knownNat @8))
  , noVals (BaseBVRepr (knownNat @16))
  , noVals (BaseBVRepr (knownNat @32))
  , noVals (BaseBVRepr (knownNat @64))
  , noVals (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @8) (knownNat @24)))
  , noVals (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @11) (knownNat @53)))
  ]

noVals :: BaseTypeRepr ty -> Pair BaseTypeRepr Vals
noVals ty = Pair ty (Vals [])

--------------------------------------------------------------------------------

toDouble :: Rational -> Double
toDouble = fromRational


showBVLiteral :: (1 <= w) => NatRepr w -> BV w -> String
showBVLiteral w bv =
    (if x < 0 then "-0x" else "0x") ++ N.showHex i (if natValue w == 64 then "L" else "")
  where
  x = BV.asSigned w bv
  i = abs x

showFloatLiteral :: BigFloat -> String
showFloatLiteral x
   | BF.bfIsNaN x     = "NAN"
   | BF.bfIsInf x     = if BF.bfIsNeg x then "-INFINITY" else "INFINITY"
   | BF.bfIsZero x    = if BF.bfIsNeg x then "-0.0f" else "0.0f"
                                               -- NB, 24 bits of precision for float
   | otherwise        = BF.bfToString 16 (BF.showFree (Just 24) <> BF.addPrefix) x ++ "f"

showDoubleLiteral :: BigFloat -> String
showDoubleLiteral x
   | BF.bfIsNaN x     = "(double) NAN"
   | BF.bfIsInf x     = if BF.bfIsNeg x then "- ((double) INFINITY)" else "(double) INFINITY"
   | BF.bfIsZero x    = if BF.bfIsNeg x then "-0.0" else "0.0"
                                               -- NB, 53 bits of precision for double
   | otherwise        = BF.bfToString 16 (BF.showFree (Just 53) <> BF.addPrefix) x

valsJS :: BaseTypeRepr ty -> Vals ty -> IO [JS]
valsJS ty (Vals xs) =
  let showEnt = case ty of
        BaseBVRepr n -> showEnt' (showBVLiteral n) n
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | Just Refl <- testEquality eb (knownNat @8)
          , Just Refl <- testEquality sb (knownNat @24)
          -> showEnt' showFloatLiteral (32 :: Int)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | Just Refl <- testEquality eb (knownNat @11)
          , Just Refl <- testEquality sb (knownNat @53)
          -> showEnt' showDoubleLiteral (64 :: Int)
        BaseRealRepr -> showEnt' (show . toDouble) (knownNat @64)
        _ -> error ("Type not implemented: " ++ show ty)

  in mapM showEnt xs

  where
  showEnt' :: Show b => (a -> String) -> b -> Entry a -> IO JS
  showEnt' repr n e =
    do l <- jsLoc (entryLoc e)
       pure $ jsObj
         [ "name" ~> jsStr (entryName e)
         , "loc"  ~> l
         , "val"  ~> jsStr (repr (entryValue e))
         , "bits" ~> jsStr (show n)
         ]

modelJS :: ModelView -> IO JS
modelJS m =
  jsList . concat <$> sequence (MapF.foldrWithKey (\k v xs -> valsJS k v : xs) [] (modelVals m))
