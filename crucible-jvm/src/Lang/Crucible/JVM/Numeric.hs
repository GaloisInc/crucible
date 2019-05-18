{- |
Module           : Lang.Crucible.JVM.Numeric
Description      : Primitive JVM operations on numeric types
Copyright        : (c) Galois, Inc 2018-2019
License          : BSD3
Maintainer       : huffman@galois.com, sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.JVM.Numeric where

import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Generator
import Lang.Crucible.Types

import Lang.Crucible.JVM.Types
import Lang.Crucible.JVM.Generator

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
-- * Basic Value Operations

iConst :: Integer -> JVMInt s
iConst i = App (BVLit w32 i)

lConst :: Integer -> JVMLong s
lConst i = App (BVLit w64 i)

dConst :: Double -> JVMDouble s
dConst d = App (DoubleLit d)

fConst :: Float -> JVMFloat s
fConst f = App (FloatLit f)

iZero :: JVMInt s
iZero = iConst 0

lZero :: JVMLong s
lZero = lConst 0

-- | Mask the low 5 bits of a shift amount of type int.
iShiftMask :: JVMInt s -> JVMInt s
iShiftMask i = App (BVAnd w32 i (iConst 31))

-- | Mask the low 6 bits of a shift amount of type long.
lShiftMask :: JVMLong s -> JVMLong s
lShiftMask i = App (BVAnd w64 i (lConst 63))

-- Both positive and negative zeros
posZerof :: JVMFloat s
posZerof = App $ FloatLit 0.0

negZerof :: JVMFloat s
negZerof = App $ FloatLit (-0.0)

posZerod :: JVMDouble s
posZerod = App $ DoubleLit 0.0

negZerod :: JVMDouble s
negZerod = App $ DoubleLit (-0.0)

iNeg :: JVMInt s -> JVMInt s
iNeg e = App (BVSub w32 iZero e)

lNeg :: JVMLong s -> JVMLong s
lNeg e = App (BVSub w64 lZero e)

-- TODO: doublecheck
-- For float values, negation is not the same as subtraction from zero. If x is +0.0,
-- then 0.0-x equals +0.0, but -x equals -0.0. Unary minus merely inverts the sign of a float.
-- Special cases of interest:
--    If the operand is NaN, the result is NaN (recall that NaN has no sign).
--    If the operand is an infinity, the result is the infinity of opposite sign.
--    If the operand is a zero, the result is the zero of opposite sign.
fNeg :: JVMFloat s -> JVMGenerator h s ret (JVMFloat s)
fNeg e = ifte (App $ FloatEq e posZerof)
              (return negZerof)
              (return $ App (FloatSub SingleFloatRepr RNE posZerof e))


dAdd, dSub, dMul, dDiv, dRem :: JVMDouble s -> JVMDouble s -> JVMDouble s
dAdd e1 e2 = App (FloatAdd DoubleFloatRepr RNE e1 e2)
dSub e1 e2 = App (FloatSub DoubleFloatRepr RNE e1 e2)
dMul e1 e2 = App (FloatMul DoubleFloatRepr RNE e1 e2)
dDiv e1 e2 = App (FloatDiv DoubleFloatRepr RNE e1 e2)
dRem e1 e2 = App (FloatRem DoubleFloatRepr e1 e2)


--TODO: treatment of NaN
--TODO: difference between dCmpg/dCmpl
-- | If the two numbers are the same, the int 0 is pushed onto the
-- stack. If value2 is greater than value1, the int 1 is pushed onto the
-- stack. If value1 is greater than value2, -1 is pushed onto the
-- stack. If either numbers is NaN, the int 1 is pushed onto the
-- stack. +0.0 and -0.0 are treated as equal.
dCmpg, dCmpl :: forall fi s h ret.
                Expr JVM s (FloatType fi) -> Expr JVM s (FloatType fi) -> JVMGenerator h s ret (JVMInt s)
dCmpg e1 e2 = ifte (App (FloatEq e1 e2)) (return $ App $ BVLit w32 0)
                   (ifte (App (FloatGe e2 e1)) (return $ App $ BVLit w32 (-1))
                         (return $ App $ BVLit w32 1))
dCmpl = dCmpg

dNeg :: JVMDouble s ->  JVMGenerator h s ret (JVMDouble s)
dNeg e = ifte (App $ FloatEq e posZerod)
              (return negZerod)
              (return $ App (FloatSub DoubleFloatRepr RNE posZerod e))


fAdd, fSub, fMul, fDiv, fRem :: JVMFloat s -> JVMFloat s -> JVMFloat s
fAdd e1 e2 = App (FloatAdd SingleFloatRepr RNE e1 e2)
fSub e1 e2 = App (FloatSub SingleFloatRepr RNE e1 e2)
fMul e1 e2 = App (FloatMul SingleFloatRepr RNE e1 e2)
fDiv e1 e2 = App (FloatDiv SingleFloatRepr RNE e1 e2)
fRem e1 e2 = App (FloatRem SingleFloatRepr e1 e2)


-- TODO: are these signed or unsigned integers?
-- | Takes two two-word long integers off the stack and compares them. If
-- the two integers are the same, the int 0 is pushed onto the stack. If
-- value2 is greater than value1, the int 1 is pushed onto the stack. If
-- value1 is greater than value2, the int -1 is pushed onto the stack.
lCmp :: JVMLong s -> JVMLong s -> JVMGenerator h s ret (JVMInt s)
lCmp e1 e2 = ifte (App (BVEq knownRepr e1 e2)) (return $ App $ BVLit w32 0)
                  (ifte (App (BVSlt knownRepr e1 e2)) (return $ App $ BVLit w32 (-1))
                        (return $ App $ BVLit w32 (1)))

