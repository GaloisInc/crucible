{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Mir.Intrinsics.Size where

import GHC.TypeLits (type (<=))

import Control.Monad.IO.Class (MonadIO, liftIO)

import Data.BitVector.Sized qualified as BV
import Data.Parameterized (knownRepr)
import Data.Parameterized.NatRepr (NatComparison (..), NatRepr, compareNat)
import Data.Parameterized.NatRepr qualified as N
import Data.Type.Equality (testEquality, pattern Refl)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.CFG.Expr (App (..), pattern BVEq, pattern BVIte)
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Types
  ( BVType,
    BaseBVType,
    BaseTypeRepr,
    BoolType,
    IntegerType,
    NatType,
    TypeRepr (..),
    pattern BaseBVRepr,
  )

import What4.Interface (bvLit)


-- Rust usize/isize representation

type SizeBits = 64

type UsizeType = BVType SizeBits
type IsizeType = BVType SizeBits
type BaseUsizeType = BaseBVType SizeBits
type BaseIsizeType = BaseBVType SizeBits

pattern UsizeRepr :: () => tp ~ UsizeType => TypeRepr tp
pattern UsizeRepr <- BVRepr (testEquality (knownRepr :: N.NatRepr SizeBits) -> Just Refl)
  where UsizeRepr = BVRepr (knownRepr :: N.NatRepr SizeBits)

pattern IsizeRepr :: () => tp ~ IsizeType => TypeRepr tp
pattern IsizeRepr <- BVRepr (testEquality (knownRepr :: N.NatRepr SizeBits) -> Just Refl)
  where IsizeRepr = BVRepr (knownRepr :: N.NatRepr SizeBits)

pattern BaseUsizeRepr :: () => tp ~ BaseUsizeType => BaseTypeRepr tp
pattern BaseUsizeRepr <- BaseBVRepr (testEquality (knownRepr :: N.NatRepr SizeBits) -> Just Refl)
  where BaseUsizeRepr = BaseBVRepr (knownRepr :: N.NatRepr SizeBits)

pattern BaseIsizeRepr :: () => tp ~ BaseIsizeType => BaseTypeRepr tp
pattern BaseIsizeRepr <- BaseBVRepr (testEquality (knownRepr :: N.NatRepr SizeBits) -> Just Refl)
  where BaseIsizeRepr = BaseBVRepr (knownRepr :: N.NatRepr SizeBits)


usizeLit :: Integer -> App ext f UsizeType
usizeLit = BVLit knownRepr . BV.mkBV knownRepr

usizeAdd :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeAdd = BVAdd knownRepr

usizeSub :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeSub = BVSub knownRepr

usizeMul :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeMul = BVMul knownRepr

usizeDiv :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeDiv = BVUdiv knownRepr

usizeRem :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeRem = BVUrem knownRepr

usizeAnd :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeAnd = BVAnd knownRepr

usizeOr :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeOr = BVOr knownRepr

usizeXor :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeXor = BVXor knownRepr

usizeShl :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeShl = BVShl knownRepr

usizeShr :: f UsizeType -> f UsizeType -> App ext f UsizeType
usizeShr = BVLshr knownRepr

usizeEq :: f UsizeType -> f UsizeType -> App ext f BoolType
usizeEq = BVEq knownRepr

usizeLe :: f UsizeType -> f UsizeType -> App ext f BoolType
usizeLe = BVUle knownRepr

usizeLt :: f UsizeType -> f UsizeType -> App ext f BoolType
usizeLt = BVUlt knownRepr

natToUsize :: (App ext f IntegerType -> f IntegerType) -> f NatType -> App ext f UsizeType
natToUsize wrap = IntegerToBV knownRepr . wrap . NatToInteger

usizeToNat :: f UsizeType -> App ext f NatType
usizeToNat = BvToNat knownRepr

usizeToBv :: (1 <= r) => NatRepr r ->
    (App ext f (BVType r) -> f (BVType r)) ->
    f UsizeType -> f (BVType r)
usizeToBv r wrap = case compareNat r (knownRepr :: N.NatRepr SizeBits) of
    NatLT _ -> wrap . BVTrunc r knownRepr
    NatEQ -> id
    NatGT _ -> wrap . BVZext r knownRepr

bvToUsize :: (1 <= w) => NatRepr w ->
    (App ext f UsizeType -> f UsizeType) ->
    f (BVType w) -> f UsizeType
bvToUsize w wrap = case compareNat w (knownRepr :: N.NatRepr SizeBits) of
    NatLT _ -> wrap . BVZext knownRepr w
    NatEQ -> id
    NatGT _ -> wrap . BVTrunc knownRepr w

sbvToUsize :: (1 <= w) => NatRepr w ->
    (App ext f UsizeType -> f UsizeType) ->
    f (BVType w) -> f UsizeType
sbvToUsize w wrap = case compareNat w (knownRepr :: N.NatRepr SizeBits) of
    NatLT _ -> wrap . BVSext knownRepr w
    NatEQ -> id
    NatGT _ -> wrap . BVTrunc knownRepr w

usizeIte :: f BoolType -> f UsizeType -> f UsizeType -> App ext f UsizeType
usizeIte c t e = BVIte c knownRepr t e


isizeLit :: Integer -> App ext f IsizeType
isizeLit = BVLit knownRepr . BV.mkBV knownRepr

isizeAdd :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeAdd = BVAdd knownRepr

isizeSub :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeSub = BVSub knownRepr

isizeMul :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeMul = BVMul knownRepr

isizeDiv :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeDiv = BVSdiv knownRepr

isizeRem :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeRem = BVSrem knownRepr

isizeNeg :: f IsizeType -> App ext f IsizeType
isizeNeg = BVNeg knownRepr

isizeAnd :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeAnd = BVAnd knownRepr

isizeOr :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeOr = BVOr knownRepr

isizeXor :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeXor = BVXor knownRepr

isizeShl :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeShl = BVShl knownRepr

isizeShr :: f IsizeType -> f IsizeType -> App ext f IsizeType
isizeShr = BVAshr knownRepr

isizeEq :: f IsizeType -> f IsizeType -> App ext f BoolType
isizeEq = BVEq knownRepr

isizeLe :: f IsizeType -> f IsizeType -> App ext f BoolType
isizeLe = BVSle knownRepr

isizeLt :: f IsizeType -> f IsizeType -> App ext f BoolType
isizeLt = BVSlt knownRepr

integerToIsize ::
    (App ext f IsizeType -> f IsizeType) ->
    f IntegerType -> f IsizeType
integerToIsize wrap = wrap . IntegerToBV knownRepr

isizeToBv :: (1 <= r) => NatRepr r ->
    (App ext f (BVType r) -> f (BVType r)) ->
    f IsizeType -> f (BVType r)
isizeToBv r wrap = case compareNat r (knownRepr :: N.NatRepr SizeBits) of
    NatLT _ -> wrap . BVTrunc r knownRepr
    NatEQ -> id
    NatGT _ -> wrap . BVSext r knownRepr

bvToIsize :: (1 <= w) => NatRepr w ->
    (App ext f IsizeType -> f IsizeType) ->
    f (BVType w) -> f IsizeType
bvToIsize w wrap = case compareNat w (knownRepr :: N.NatRepr SizeBits) of
    NatLT _ -> wrap . BVZext knownRepr w
    NatEQ -> id
    NatGT _ -> wrap . BVTrunc knownRepr w

sbvToIsize :: (1 <= w) => NatRepr w ->
    (App ext f IsizeType -> f IsizeType) ->
    f (BVType w) -> f IsizeType
sbvToIsize w wrap = case compareNat w (knownRepr :: N.NatRepr SizeBits) of
    NatLT _ -> wrap . BVSext knownRepr w
    NatEQ -> id
    NatGT _ -> wrap . BVTrunc knownRepr w

isizeIte :: f BoolType -> f IsizeType -> f IsizeType -> App ext f IsizeType
isizeIte c t e = BVIte c knownRepr t e


usizeToIsize :: (App ext f IsizeType -> f IsizeType) -> f UsizeType -> f IsizeType
usizeToIsize _wrap = id

isizeToUsize :: (App ext f UsizeType -> f UsizeType) -> f IsizeType -> f UsizeType
isizeToUsize _wrap = id


wordLit :: (IsSymInterface sym, MonadIO m) => sym -> Word -> m (RegValue sym UsizeType)
wordLit sym o = liftIO $ bvLit sym N.knownNat (BV.mkBV N.knownNat (fromIntegral o))
