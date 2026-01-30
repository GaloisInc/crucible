-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libc.Math
-- Description      : Override definitions for C @math.h@ functions
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Galois, Inc. <crux@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.Libc.Math
  ( -- * math.h overrides
    mathOverrides
    -- * Override declarations
  , llvmCeilOverride
  , llvmCeilfOverride
  , llvmFloorOverride
  , llvmFloorfOverride
  , llvmFmaOverride
  , llvmFmafOverride
  , llvmIsinfOverride
  , llvm__isinfOverride
  , llvm__isinffOverride
  , llvmIsnanOverride
  , llvm__isnanOverride
  , llvm__isnanfOverride
  , llvm__isnandOverride
  , llvmSqrtOverride
  , llvmSqrtfOverride
  , llvmSinOverride
  , llvmSinfOverride
  , llvmCosOverride
  , llvmCosfOverride
  , llvmTanOverride
  , llvmTanfOverride
  , llvmAsinOverride
  , llvmAsinfOverride
  , llvmAcosOverride
  , llvmAcosfOverride
  , llvmAtanOverride
  , llvmAtanfOverride
  , llvmSinhOverride
  , llvmSinhfOverride
  , llvmCoshOverride
  , llvmCoshfOverride
  , llvmTanhOverride
  , llvmTanhfOverride
  , llvmAsinhOverride
  , llvmAsinhfOverride
  , llvmAcoshOverride
  , llvmAcoshfOverride
  , llvmAtanhOverride
  , llvmAtanhfOverride
  , llvmHypotOverride
  , llvmHypotfOverride
  , llvmAtan2Override
  , llvmAtan2fOverride
  , llvmPowfOverride
  , llvmPowOverride
  , llvmExpOverride
  , llvmExpfOverride
  , llvmLogOverride
  , llvmLogfOverride
  , llvmExpm1Override
  , llvmExpm1fOverride
  , llvmLog1pOverride
  , llvmLog1pfOverride
  , llvmExp2Override
  , llvmExp2fOverride
  , llvmLog2Override
  , llvmLog2fOverride
  , llvmExp10Override
  , llvmExp10fOverride
  , llvm__exp10Override
  , llvm__exp10fOverride
  , llvmLog10Override
  , llvmLog10fOverride
    -- * Implementation functions
  , callCeil
  , callFloor
  , callFMA
  , callIsinf
  , callIsnan
  , callSqrt
  , callSpecialFunction1
  , callSpecialFunction2
  , defaultRM
  ) where

import           Control.Monad.IO.Class (liftIO)

import qualified Data.Parameterized.Context as Ctx

import           What4.Interface
import qualified What4.SpecialFunctions as W4

import           Lang.Crucible.Backend
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap

import           Lang.Crucible.LLVM.QQ( llvmOvr )

import           Lang.Crucible.LLVM.Intrinsics.Common

-- | All math.h overrides
mathOverrides ::
  IsSymInterface sym =>
  [SomeLLVMOverride p sym ext]
mathOverrides =
  [ SomeLLVMOverride llvmCeilOverride
  , SomeLLVMOverride llvmCeilfOverride
  , SomeLLVMOverride llvmFloorOverride
  , SomeLLVMOverride llvmFloorfOverride
  , SomeLLVMOverride llvmFmaOverride
  , SomeLLVMOverride llvmFmafOverride
  , SomeLLVMOverride llvmIsinfOverride
  , SomeLLVMOverride llvm__isinfOverride
  , SomeLLVMOverride llvm__isinffOverride
  , SomeLLVMOverride llvmIsnanOverride
  , SomeLLVMOverride llvm__isnanOverride
  , SomeLLVMOverride llvm__isnanfOverride
  , SomeLLVMOverride llvm__isnandOverride
  , SomeLLVMOverride llvmSqrtOverride
  , SomeLLVMOverride llvmSqrtfOverride
  , SomeLLVMOverride llvmSinOverride
  , SomeLLVMOverride llvmSinfOverride
  , SomeLLVMOverride llvmCosOverride
  , SomeLLVMOverride llvmCosfOverride
  , SomeLLVMOverride llvmTanOverride
  , SomeLLVMOverride llvmTanfOverride
  , SomeLLVMOverride llvmAsinOverride
  , SomeLLVMOverride llvmAsinfOverride
  , SomeLLVMOverride llvmAcosOverride
  , SomeLLVMOverride llvmAcosfOverride
  , SomeLLVMOverride llvmAtanOverride
  , SomeLLVMOverride llvmAtanfOverride
  , SomeLLVMOverride llvmSinhOverride
  , SomeLLVMOverride llvmSinhfOverride
  , SomeLLVMOverride llvmCoshOverride
  , SomeLLVMOverride llvmCoshfOverride
  , SomeLLVMOverride llvmTanhOverride
  , SomeLLVMOverride llvmTanhfOverride
  , SomeLLVMOverride llvmAsinhOverride
  , SomeLLVMOverride llvmAsinhfOverride
  , SomeLLVMOverride llvmAcoshOverride
  , SomeLLVMOverride llvmAcoshfOverride
  , SomeLLVMOverride llvmAtanhOverride
  , SomeLLVMOverride llvmAtanhfOverride
  , SomeLLVMOverride llvmHypotOverride
  , SomeLLVMOverride llvmHypotfOverride
  , SomeLLVMOverride llvmAtan2Override
  , SomeLLVMOverride llvmAtan2fOverride
  , SomeLLVMOverride llvmPowfOverride
  , SomeLLVMOverride llvmPowOverride
  , SomeLLVMOverride llvmExpOverride
  , SomeLLVMOverride llvmExpfOverride
  , SomeLLVMOverride llvmLogOverride
  , SomeLLVMOverride llvmLogfOverride
  , SomeLLVMOverride llvmExpm1Override
  , SomeLLVMOverride llvmExpm1fOverride
  , SomeLLVMOverride llvmLog1pOverride
  , SomeLLVMOverride llvmLog1pfOverride
  , SomeLLVMOverride llvmExp2Override
  , SomeLLVMOverride llvmExp2fOverride
  , SomeLLVMOverride llvmLog2Override
  , SomeLLVMOverride llvmLog2fOverride
  , SomeLLVMOverride llvmExp10Override
  , SomeLLVMOverride llvmExp10fOverride
  , SomeLLVMOverride llvm__exp10Override
  , SomeLLVMOverride llvm__exp10fOverride
  , SomeLLVMOverride llvmLog10Override
  , SomeLLVMOverride llvmLog10fOverride
  ]

------------------------------------------------------------------------
-- ** Declarations

llvmCeilOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCeilOverride =
  [llvmOvr| double @ceil( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment callCeil args)

llvmCeilfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCeilfOverride =
  [llvmOvr| float @ceilf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment callCeil args)


llvmFloorOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmFloorOverride =
  [llvmOvr| double @floor( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment callFloor args)

llvmFloorfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmFloorfOverride =
  [llvmOvr| float @floorf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment callFloor args)

llvmFmafOverride ::
     forall sym p ext
   . IsSymInterface sym
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType SingleFloat
                  ::> FloatType SingleFloat
                  ::> FloatType SingleFloat)
        (FloatType SingleFloat)
llvmFmafOverride =
  [llvmOvr| float @fmaf( float, float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment callFMA args)

llvmFmaOverride ::
     forall sym p ext
   . IsSymInterface sym
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType DoubleFloat
                  ::> FloatType DoubleFloat
                  ::> FloatType DoubleFloat)
        (FloatType DoubleFloat)
llvmFmaOverride =
  [llvmOvr| double @fma( double, double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment callFMA args)


-- math.h defines isinf() and isnan() as macros, so you might think it unusual
-- to provide function overrides for them. However, if you write, say,
-- (isnan)(x) instead of isnan(x), Clang will compile the former as a direct
-- function call rather than as a macro application. Some experimentation
-- reveals that the isnan function's argument is always a double, so we give its
-- argument the type double here to match this unstated convention. We follow
-- suit similarly with isinf.
--
-- Clang does not yet provide direct function call versions of isfinite() or
-- isnormal(), so we do not provide overrides for them.

llvmIsinfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvmIsinfOverride =
  [llvmOvr| i32 @isinf( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsinf (knownNat @32)) args)

-- __isinf and __isinff are like the isinf macro, except their arguments are
-- known to be double or float, respectively. They are not mentioned in the
-- POSIX source standard, only the binary standard. See
-- http://refspecs.linux-foundation.org/LSB_4.0.0/LSB-Core-generic/LSB-Core-generic/baselib---isinf.html and
-- http://refspecs.linux-foundation.org/LSB_4.0.0/LSB-Core-generic/LSB-Core-generic/baselib---isinff.html.
llvm__isinfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvm__isinfOverride =
  [llvmOvr| i32 @__isinf( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsinf (knownNat @32)) args)

llvm__isinffOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (BVType 32)
llvm__isinffOverride =
  [llvmOvr| i32 @__isinff( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsinf (knownNat @32)) args)

llvmIsnanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvmIsnanOverride =
  [llvmOvr| i32 @isnan( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsnan (knownNat @32)) args)

-- __isnan and __isnanf are like the isnan macro, except their arguments are
-- known to be double or float, respectively. They are not mentioned in the
-- POSIX source standard, only the binary standard. See
-- http://refspecs.linux-foundation.org/LSB_4.0.0/LSB-Core-generic/LSB-Core-generic/baselib---isnan.html and
-- http://refspecs.linux-foundation.org/LSB_4.0.0/LSB-Core-generic/LSB-Core-generic/baselib---isnanf.html.
llvm__isnanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvm__isnanOverride =
  [llvmOvr| i32 @__isnan( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsnan (knownNat @32)) args)

llvm__isnanfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (BVType 32)
llvm__isnanfOverride =
  [llvmOvr| i32 @__isnanf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsnan (knownNat @32)) args)

-- macOS compiles isnan() to __isnand() when the argument is a double.
llvm__isnandOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvm__isnandOverride =
  [llvmOvr| i32 @__isnand( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callIsnan (knownNat @32)) args)

llvmSqrtOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSqrtOverride =
  [llvmOvr| double @sqrt( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment callSqrt args)

llvmSqrtfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSqrtfOverride =
  [llvmOvr| float @sqrtf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment callSqrt args)

------------------------------------------------------------------------
-- **** Circular trigonometry functions

-- sin(f)

llvmSinOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSinOverride =
  [llvmOvr| double @sin( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Sin) args)

llvmSinfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSinfOverride =
  [llvmOvr| float @sinf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Sin) args)

-- cos(f)

llvmCosOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCosOverride =
  [llvmOvr| double @cos( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Cos) args)

llvmCosfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCosfOverride =
  [llvmOvr| float @cosf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Cos) args)

-- tan(f)

llvmTanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmTanOverride =
  [llvmOvr| double @tan( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Tan) args)

llvmTanfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmTanfOverride =
  [llvmOvr| float @tanf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Tan) args)

-- asin(f)

llvmAsinOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAsinOverride =
  [llvmOvr| double @asin( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arcsin) args)

llvmAsinfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAsinfOverride =
  [llvmOvr| float @asinf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arcsin) args)

-- acos(f)

llvmAcosOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAcosOverride =
  [llvmOvr| double @acos( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arccos) args)

llvmAcosfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAcosfOverride =
  [llvmOvr| float @acosf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arccos) args)

-- atan(f)

llvmAtanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAtanOverride =
  [llvmOvr| double @atan( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arctan) args)

llvmAtanfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAtanfOverride =
  [llvmOvr| float @atanf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arctan) args)

------------------------------------------------------------------------
-- **** Hyperbolic trigonometry functions

-- sinh(f)

llvmSinhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSinhOverride =
  [llvmOvr| double @sinh( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Sinh) args)

llvmSinhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSinhfOverride =
  [llvmOvr| float @sinhf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Sinh) args)

-- cosh(f)

llvmCoshOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCoshOverride =
  [llvmOvr| double @cosh( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Cosh) args)

llvmCoshfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCoshfOverride =
  [llvmOvr| float @coshf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Cosh) args)

-- tanh(f)

llvmTanhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmTanhOverride =
  [llvmOvr| double @tanh( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Tanh) args)

llvmTanhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmTanhfOverride =
  [llvmOvr| float @tanhf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Tanh) args)

-- asinh(f)

llvmAsinhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAsinhOverride =
  [llvmOvr| double @asinh( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arcsinh) args)

llvmAsinhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAsinhfOverride =
  [llvmOvr| float @asinhf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arcsinh) args)

-- acosh(f)

llvmAcoshOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAcoshOverride =
  [llvmOvr| double @acosh( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arccosh) args)

llvmAcoshfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAcoshfOverride =
  [llvmOvr| float @acoshf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arccosh) args)

-- atanh(f)

llvmAtanhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAtanhOverride =
  [llvmOvr| double @atanh( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arctanh) args)

llvmAtanhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAtanhfOverride =
  [llvmOvr| float @atanhf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Arctanh) args)

------------------------------------------------------------------------
-- **** Rectangular to polar coordinate conversion

-- hypot(f)

llvmHypotOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmHypotOverride =
  [llvmOvr| double @hypot( double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction2 W4.Hypot) args)

llvmHypotfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmHypotfOverride =
  [llvmOvr| float @hypotf( float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction2 W4.Hypot) args)

-- atan2(f)

llvmAtan2Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAtan2Override =
  [llvmOvr| double @atan2( double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction2 W4.Arctan2) args)

llvmAtan2fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAtan2fOverride =
  [llvmOvr| float @atan2f( float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction2 W4.Arctan2) args)

------------------------------------------------------------------------
-- **** Exponential and logarithm functions

-- pow(f)

llvmPowfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmPowfOverride =
  [llvmOvr| float @powf( float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction2 W4.Pow) args)

llvmPowOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmPowOverride =
  [llvmOvr| double @pow( double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction2 W4.Pow) args)

-- exp(f)

llvmExpOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExpOverride =
  [llvmOvr| double @exp( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp) args)

llvmExpfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExpfOverride =
  [llvmOvr| float @expf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp) args)

-- log(f)

llvmLogOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLogOverride =
  [llvmOvr| double @log( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log) args)

llvmLogfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLogfOverride =
  [llvmOvr| float @logf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log) args)

-- expm1(f)

llvmExpm1Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExpm1Override =
  [llvmOvr| double @expm1( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Expm1) args)

llvmExpm1fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExpm1fOverride =
  [llvmOvr| float @expm1f( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Expm1) args)

-- log1p(f)

llvmLog1pOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog1pOverride =
  [llvmOvr| double @log1p( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log1p) args)

llvmLog1pfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog1pfOverride =
  [llvmOvr| float @log1pf( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log1p) args)

------------------------------------------------------------------------
-- **** Base 2 exponential and logarithm

-- exp2(f)

llvmExp2Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExp2Override =
  [llvmOvr| double @exp2( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp2) args)

llvmExp2fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExp2fOverride =
  [llvmOvr| float @exp2f( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp2) args)

-- log2(f)

llvmLog2Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog2Override =
  [llvmOvr| double @log2( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log2) args)

llvmLog2fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog2fOverride =
  [llvmOvr| float @log2f( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log2) args)

------------------------------------------------------------------------
-- **** Base 10 exponential and logarithm

-- exp10(f)

llvmExp10Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExp10Override =
  [llvmOvr| double @exp10( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp10) args)

llvmExp10fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExp10fOverride =
  [llvmOvr| float @exp10f( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp10) args)

-- macOS uses __exp10(f) instead of exp10(f).

llvm__exp10Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvm__exp10Override =
  [llvmOvr| double @__exp10( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp10) args)

llvm__exp10fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvm__exp10fOverride =
  [llvmOvr| float @__exp10f( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Exp10) args)

-- log10(f)

llvmLog10Override ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog10Override =
  [llvmOvr| double @log10( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log10) args)

llvmLog10fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog10fOverride =
  [llvmOvr| float @log10f( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callSpecialFunction1 W4.Log10) args)

------------------------------------------------------------------------
-- ** Implementations

callSpecialFunction1 ::
  forall fi p sym ext r args ret.
  (IsSymInterface sym, KnownRepr FloatInfoRepr fi) =>
  W4.SpecialFunction (EmptyCtx ::> W4.R) ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callSpecialFunction1 fn (regValue -> x) = do
  sym <- getSymInterface
  liftIO $ iFloatSpecialFunction1 sym (knownRepr :: FloatInfoRepr fi) fn x

callSpecialFunction2 ::
  forall fi p sym ext r args ret.
  (IsSymInterface sym, KnownRepr FloatInfoRepr fi) =>
  W4.SpecialFunction (EmptyCtx ::> W4.R ::> W4.R) ->
  RegEntry sym (FloatType fi) ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callSpecialFunction2 fn (regValue -> x) (regValue -> y) = do
  sym <- getSymInterface
  liftIO $ iFloatSpecialFunction2 sym (knownRepr :: FloatInfoRepr fi) fn x y

callCeil ::
  forall fi p sym ext r args ret.
  IsSymInterface sym =>
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callCeil (regValue -> x) = do
  sym <- getSymInterface
  liftIO $ iFloatRound @_ @fi sym RTP x

callFloor ::
  forall fi p sym ext r args ret.
  IsSymInterface sym =>
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callFloor (regValue -> x) = do
  sym <- getSymInterface
  liftIO $ iFloatRound @_ @fi sym RTN x

-- | An implementation of @libc@'s @fma@ function.
callFMA ::
     forall fi p sym ext r args ret
   . IsSymInterface sym
  => RegEntry sym (FloatType fi)
  -> RegEntry sym (FloatType fi)
  -> RegEntry sym (FloatType fi)
  -> OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callFMA (regValue -> x) (regValue -> y) (regValue -> z) = do
  sym <- getSymInterface
  liftIO $ iFloatFMA @_ @fi sym defaultRM x y z

-- | An implementation of @libc@'s @isinf@ macro. This returns @1@ when the
-- argument is positive infinity, @-1@ when the argument is negative infinity,
-- and zero otherwise.
callIsinf ::
  forall fi w p sym ext r args ret.
  (IsSymInterface sym, 1 <= w) =>
  NatRepr w ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callIsinf w (regValue -> x) = do
  sym <- getSymInterface
  liftIO $ do
    isInf <- iFloatIsInf @_ @fi sym x
    isNeg <- iFloatIsNeg @_ @fi sym x
    isPos <- iFloatIsPos @_ @fi sym x
    isInfN <- andPred sym isInf isNeg
    isInfP <- andPred sym isInf isPos
    bv1 <- bvOne sym w
    bvNeg1 <- bvNeg sym bv1
    bv0 <- bvZero sym w
    res0 <- bvIte sym isInfP bv1 bv0
    bvIte sym isInfN bvNeg1 res0

callIsnan ::
  forall fi w p sym ext r args ret.
  (IsSymInterface sym, 1 <= w) =>
  NatRepr w ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callIsnan w (regValue -> x) = do
  sym <- getSymInterface
  liftIO $ do
    isnan  <- iFloatIsNaN @_ @fi sym x
    bv1 <- bvOne sym w
    bv0 <- bvZero sym w
    -- isnan() is allowed to return any nonzero value if the argument is NaN, and
    -- out of all the possible nonzero values, `1` is certainly one of them.
    bvIte sym isnan bv1 bv0

callSqrt ::
  forall fi p sym ext r args ret.
  IsSymInterface sym =>
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callSqrt (regValue -> x) = do
  sym <- getSymInterface
  liftIO $ iFloatSqrt @_ @fi sym defaultRM x

-- | IEEE 754 declares 'RNE' to be the default rounding mode, and most @libc@
-- implementations agree with this in practice. The only places where we do not
-- use this as the default are operations that specifically require the behavior
-- of a particular rounding mode, such as @ceil@ or @floor@.
defaultRM :: RoundingMode
defaultRM = RNE
