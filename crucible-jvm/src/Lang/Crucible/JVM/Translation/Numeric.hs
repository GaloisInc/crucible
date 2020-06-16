{- |
Module           : Lang.Crucible.JVM.Translation.Numeric
Description      : Primitive JVM operations on numeric types
Copyright        : (c) Galois, Inc 2018-2019
License          : BSD3
Maintainer       : huffman@galois.com, sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.JVM.Translation.Numeric where

import qualified Data.BitVector.Sized as BV

import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Reg (Expr(..))
import Lang.Crucible.Types

import Lang.Crucible.JVM.Types

----------------------------------------------------------------------
-- * Type conversions

floatFromDouble :: JVMDouble s -> JVMFloat s
floatFromDouble d = App (FloatCast SingleFloatRepr RNE d)

intFromDouble :: JVMDouble s -> JVMInt s
intFromDouble d = App (FloatToSBV w32 RTZ d)

longFromDouble :: JVMDouble s -> JVMLong s
longFromDouble d = App (FloatToSBV w64 RTZ d)

doubleFromFloat :: JVMFloat s -> JVMDouble s
doubleFromFloat f = App (FloatCast DoubleFloatRepr RNE f)

intFromFloat :: JVMFloat s -> JVMInt s
intFromFloat f = App (FloatToSBV w32 RTZ f)

longFromFloat :: JVMFloat s -> JVMLong s
longFromFloat f = App (FloatToSBV w64 RTZ f)

doubleFromInt :: JVMInt s -> JVMDouble s
doubleFromInt i = App (FloatFromSBV DoubleFloatRepr RNE i)

floatFromInt :: JVMInt s -> JVMFloat s
floatFromInt i = App (FloatFromSBV SingleFloatRepr RNE i)

longFromInt :: JVMInt s -> JVMLong s
longFromInt x = App (BVSext w64 w32 x)

doubleFromLong :: JVMLong s -> JVMDouble s
doubleFromLong l = App (FloatFromSBV DoubleFloatRepr RNE l)

floatFromLong :: JVMLong s -> JVMFloat s
floatFromLong l = App (FloatFromSBV SingleFloatRepr RNE l)

intFromLong :: JVMLong s -> JVMInt s
intFromLong l = App (BVTrunc w32 w64 l)

----------------------------------------------------------------------
-- * Int operations

iConst :: Integer -> JVMInt s
iConst i = App (BVLit w32 (BV.mkBV w32 i))

iZero :: JVMInt s
iZero = iConst 0

-- | Mask the low 5 bits of a shift amount for type int.
iShiftMask :: JVMInt s -> JVMInt s
iShiftMask i = App (BVAnd w32 i (iConst 31))

iShl, iShr, iUshr :: JVMInt s -> JVMInt s -> JVMInt s
iShl e1 e2 = App (BVShl w32 e1 (iShiftMask e2))
iShr e1 e2 = App (BVAshr w32 e1 (iShiftMask e2))
iUshr e1 e2 = App (BVLshr w32 e1 (iShiftMask e2))

iAdd, iSub, iMul :: JVMInt s -> JVMInt s -> JVMInt s
iAdd e1 e2 = App (BVAdd w32 e1 e2)
iSub e1 e2 = App (BVSub w32 e1 e2)
iMul e1 e2 = App (BVMul w32 e1 e2)

iDiv, iRem :: JVMInt s -> JVMInt s -> JVMInt s
iDiv e1 e2 = App (BVSdiv w32 e1 e2)
iRem e1 e2 = App (BVSrem w32 e1 e2)

iAnd, iOr, iXor :: JVMInt s -> JVMInt s -> JVMInt s
iAnd e1 e2 = App (BVAnd w32 e1 e2)
iOr  e1 e2 = App (BVOr  w32 e1 e2)
iXor e1 e2 = App (BVXor w32 e1 e2)

iNeg :: JVMInt s -> JVMInt s
iNeg e = App (BVSub w32 iZero e)

iIte :: JVMBool s -> JVMInt s -> JVMInt s -> JVMInt s
iIte cond e1 e2 = App (BVIte cond w32 e1 e2)

----------------------------------------------------------------------
-- * Long operations

lConst :: Integer -> JVMLong s
lConst i = App (BVLit w64 (BV.mkBV w64 i))

lZero :: JVMLong s
lZero = lConst 0

-- | Mask the low 6 bits of a shift amount for type long.
lShiftMask :: JVMInt s -> JVMLong s
lShiftMask i = longFromInt (App (BVAnd w32 i (iConst 63)))

lShl, lShr, lUshr :: JVMLong s -> JVMInt s -> JVMLong s
lShl e1 e2 = App (BVShl w64 e1 (lShiftMask e2))
lShr e1 e2 = App (BVAshr w64 e1 (lShiftMask e2))
lUshr e1 e2 = App (BVLshr w64 e1 (lShiftMask e2))

lAdd, lSub, lMul :: JVMLong s -> JVMLong s -> JVMLong s
lAdd e1 e2 = App (BVAdd w64 e1 e2)
lSub e1 e2 = App (BVSub w64 e1 e2)
lMul e1 e2 = App (BVMul w64 e1 e2)

lDiv, lRem :: JVMLong s -> JVMLong s -> JVMLong s
lDiv e1 e2 = App (BVSdiv w64 e1 e2)
lRem e1 e2 = App (BVSrem w64 e1 e2)

lAnd, lOr, lXor :: JVMLong s -> JVMLong s -> JVMLong s
lAnd e1 e2 = App (BVAnd w64 e1 e2)
lOr  e1 e2 = App (BVOr  w64 e1 e2)
lXor e1 e2 = App (BVXor w64 e1 e2)

lNeg :: JVMLong s -> JVMLong s
lNeg e = App (BVSub w64 lZero e)

-- | Both @value1@ and @value2@ must be of type long. They are both
-- popped from the operand stack, and a signed integer comparison is
-- performed. If @value1@ is greater than @value2@, the @int@ value 1
-- is pushed onto the operand stack. If @value1@ is equal to @value2@,
-- the @int@ value 0 is pushed onto the operand stack. If @value1@ is
-- less than @value2@, the @int@ value -1 is pushed onto the operand
-- stack.
lCmp :: JVMLong s -> JVMLong s -> JVMInt s
lCmp e1 e2 =
  iIte (App (BVEq w64 e1 e2)) (iConst 0) $
  iIte (App (BVSlt w64 e1 e2)) (iConst (-1)) (iConst 1)

----------------------------------------------------------------------
-- * Float operations

fConst :: Float -> JVMFloat s
fConst f = App (FloatLit f)

-- | Positive zero.
fPosZero :: JVMFloat s
fPosZero = fConst 0.0

-- | Negative zero.
fNegZero :: JVMFloat s
fNegZero = fConst (-0.0)

-- | For float values, negation is not the same as subtraction from
-- zero. If @x@ is @+0.0,@ then @0.0-x@ equals @+0.0@, but @-x@ equals
-- @-0.0@. Unary minus merely inverts the sign of a float. Special
-- cases of interest:
--
--    * If the operand is NaN, the result is NaN (recall that NaN has no sign).
--
--    * If the operand is an infinity, the result is the infinity of opposite sign.
--
--    * If the operand is a zero, the result is the zero of opposite sign.
fNeg :: JVMFloat s -> JVMFloat s
fNeg e = App (FloatNeg SingleFloatRepr e)

fAdd, fSub, fMul, fDiv, fRem :: JVMFloat s -> JVMFloat s -> JVMFloat s
fAdd e1 e2 = App (FloatAdd SingleFloatRepr RNE e1 e2)
fSub e1 e2 = App (FloatSub SingleFloatRepr RNE e1 e2)
fMul e1 e2 = App (FloatMul SingleFloatRepr RNE e1 e2)
fDiv e1 e2 = App (FloatDiv SingleFloatRepr RNE e1 e2)
fRem e1 e2 = App (FloatRem SingleFloatRepr e1 e2)

-- | A floating-point comparison is performed: If @value1@ is greater
-- than @value2@, the @int@ value 1 is pushed onto the operand stack.
-- Otherwise, if @value1@ is equal to @value2@, the @int@ value 0 is
-- pushed onto the operand stack. Otherwise, if @value1@ is less than
-- @value2@, the @int@ value -1 is pushed onto the operand stack.
-- Otherwise, at least one of @value1@ or @value2@ is NaN. The @fcmpg@
-- instruction pushes the @int@ value 1 onto the operand stack and the
-- @fcmpl@ instruction pushes the @int@ value -1 onto the operand stack.
fCmpg :: JVMFloat s -> JVMFloat s -> JVMInt s
fCmpg e1 e2 =
  iIte (App (FloatLt e1 e2)) (iConst (-1)) $
  iIte (App (FloatFpEq e1 e2)) (iConst 0) $
  iConst 1

fCmpl :: JVMFloat s -> JVMFloat s -> JVMInt s
fCmpl e1 e2 =
  iIte (App (FloatGt e1 e2)) (iConst 1) $
  iIte (App (FloatFpEq e1 e2)) (iConst 0) $
  iConst (-1)

----------------------------------------------------------------------
-- * Double operations

dConst :: Double -> JVMDouble s
dConst d = App (DoubleLit d)

-- | Positive zero.
dPosZero :: JVMDouble s
dPosZero = dConst 0.0

-- | Negative zero.
dNegZero :: JVMDouble s
dNegZero = dConst (-0.0)

dAdd, dSub, dMul, dDiv, dRem :: JVMDouble s -> JVMDouble s -> JVMDouble s
dAdd e1 e2 = App (FloatAdd DoubleFloatRepr RNE e1 e2)
dSub e1 e2 = App (FloatSub DoubleFloatRepr RNE e1 e2)
dMul e1 e2 = App (FloatMul DoubleFloatRepr RNE e1 e2)
dDiv e1 e2 = App (FloatDiv DoubleFloatRepr RNE e1 e2)
dRem e1 e2 = App (FloatRem DoubleFloatRepr e1 e2)

dNeg :: JVMDouble s -> JVMDouble s
dNeg e = App (FloatNeg DoubleFloatRepr e)

-- | A floating-point comparison is performed: If @value1@ is greater
-- than @value2@, the @int@ value 1 is pushed onto the operand stack.
-- Otherwise, if @value1@ is equal to @value2@, the @int@ value 0 is
-- pushed onto the operand stack. Otherwise, if @value1@ is less than
-- @value2@, the @int@ value -1 is pushed onto the operand stack.
-- Otherwise, at least one of @value1@ or @value2@ is NaN. The @dcmpg@
-- instruction pushes the @int@ value 1 onto the operand stack and the
-- @dcmpl@ instruction pushes the @int@ value -1 onto the operand stack.
dCmpg :: JVMDouble s -> JVMDouble s -> JVMInt s
dCmpg e1 e2 =
  iIte (App (FloatLt e1 e2)) (iConst (-1)) $
  iIte (App (FloatFpEq e1 e2)) (iConst 0) $
  iConst 1

dCmpl :: JVMDouble s -> JVMDouble s -> JVMInt s
dCmpl e1 e2 =
  iIte (App (FloatGt e1 e2)) (iConst 1) $
  iIte (App (FloatFpEq e1 e2)) (iConst 0) $
  iConst (-1)

