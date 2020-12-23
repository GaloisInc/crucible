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

import           Data.Binary.IEEE754 as IEEE754
import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Pair (Pair(..))
import           Data.Parameterized.TraversableF (traverseF)
import qualified Numeric as N

import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegMap (RegValue)
import           What4.Expr (GroundEvalFn(..), ExprBuilder)
import           What4.ProgramLoc

import           Crux.UI.JS
import           Crux.Types


emptyModel :: Model sym
emptyModel = Model $ MapF.fromList
  [ noVars (BaseBVRepr (knownNat @8))
  , noVars (BaseBVRepr (knownNat @16))
  , noVars (BaseBVRepr (knownNat @32))
  , noVars (BaseBVRepr (knownNat @64))
  , noVars (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @8) (knownNat @24)))
  , noVars (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @11) (knownNat @53)))
  ]

noVars :: BaseTypeRepr ty -> Pair BaseTypeRepr (Vars sym)
noVars ty = Pair ty (Vars [])

addVar ::
  ProgramLoc ->
  String ->
  BaseTypeRepr ty ->
  RegValue sym (BaseToType ty) ->
  Model sym ->
  Model sym
addVar l nm k v (Model mp) = Model (MapF.insertWith jn k (Vars [ ent ]) mp)
  where jn (Vars new) (Vars old) = Vars (new ++ old)
        ent = Entry { entryName = nm, entryLoc = l, entryValue = v }

evalVars ::
  sym ~ ExprBuilder t st fs =>
  GroundEvalFn t ->
  Vars sym ty ->
  IO (Vals ty)
evalVars ev (Vars xs) = Vals . reverse <$> mapM evEntry xs
  where evEntry e = do v <- groundEval ev (entryValue e)
                       return e { entryValue = v }

evalModel ::
  sym ~ ExprBuilder t st fs =>
  GroundEvalFn t ->
  Model sym ->
  IO (MapF BaseTypeRepr Vals)
evalModel ev (Model mp) = traverseF (evalVars ev) mp


--------------------------------------------------------------------------------

toDouble :: Rational -> Double
toDouble = fromRational


showBVLiteral :: (1 <= w) => NatRepr w -> BV w -> String
showBVLiteral w bv =
    (if x < 0 then "-0x" else "0x") ++ N.showHex i (if natValue w == 64 then "L" else "")

  where
  x = BV.asSigned w bv
  i = abs x

showFloatLiteral :: BV 32 -> String
showFloatLiteral bv
   | isNaN x          = "NAN"
   | isInfinite x     = if signum x < 0 then "-INFINITY" else "INFINITY"
   | isNegativeZero x = "-0.0f"
   | otherwise        =
      (if mag < 0 then "-0x" else "0x") ++ N.showHex (abs mag) ("p" ++ show ex ++ "f")

 where
 x = IEEE754.wordToFloat (fromInteger (BV.asUnsigned bv))
 (mag,ex) = decodeFloat x


showDoubleLiteral :: BV 64 -> String
showDoubleLiteral bv
   | isNaN x          = "(double) NAN"
   | isInfinite x     = if signum x < 0 then "- ((double) INFINITY)" else "(double) INFINITY"
   | isNegativeZero x = "-0.0"
   | otherwise        =
      (if mag < 0 then "-0x" else "0x") ++ N.showHex (abs mag) ("p" ++ show ex)

 where
 x = IEEE754.wordToDouble (fromInteger (BV.asUnsigned bv))
 (mag,ex) = decodeFloat x


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

instance Semigroup (Model sym) where
  (Model m1) <> m2        = MapF.foldrWithKey f m2 m1 where
    f :: forall s. BaseTypeRepr s -> Vars sym s -> Model sym -> Model sym
    f k vs (Model m) = Model (MapF.insertWith jn k vs m)
    jn (Vars new) (Vars old) = Vars (new ++ old)

instance Monoid (Model sym) where
  mempty               = emptyModel
  mappend m1 m2        = m1 <> m2
