{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Mir.Intrinsics
  {-
( -- * Internal implementation types
  MirReferenceSymbol
, MirReferenceType
, pattern MirReferenceRepr
, MirReference(..)
, MirReferencePath(..)
, muxRefPath
, muxRef
, MirSlice
, pattern MirSliceRepr

  -- * MIR Syntax extension
, MIR
, MirStmt(..)
, mirExtImpl
) -} where

import           GHC.Natural
import           GHC.TypeLits
import           Control.Lens hiding (Empty, (:>), Index, view)
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Data.Kind(Type)
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import           Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.String
import qualified Data.Vector as V

import qualified Text.Regex as Regex
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.TH.GADT as U
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as N

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Extension.Safety(AssertionClassifier,NoAssertionClassifier,HasStructuredAssertions(..))
import           Lang.Crucible.CFG.Generator hiding (dropRef)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree hiding (FnState)
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           What4.Concrete (ConcreteVal(..), concreteType)
import           What4.Interface
import           What4.Partial (maybePartExpr)
import           What4.Utils.MonadST

import           Mir.DefId
import           Mir.Mir
import           Mir.PP

import           Debug.Trace

import           Unsafe.Coerce


mirIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
mirIntrinsicTypes =
   MapF.insert (knownSymbol @MirReferenceSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MirVectorSymbol) IntrinsicMuxFn $
   MapF.empty



-- Rust enum representation

-- A Rust enum, whose variants have the types listed in `ctx`.
type RustEnumType ctx = StructType (RustEnumFields ctx)
type RustEnumFields ctx = EmptyCtx ::> IsizeType ::> VariantType ctx

pattern RustEnumFieldsRepr :: () => ctx' ~ RustEnumFields ctx => CtxRepr ctx -> CtxRepr ctx'
pattern RustEnumFieldsRepr ctx = Empty :> IsizeRepr :> VariantRepr ctx
pattern RustEnumRepr :: () => tp ~ RustEnumType ctx => CtxRepr ctx -> TypeRepr tp
pattern RustEnumRepr ctx = StructRepr (RustEnumFieldsRepr ctx)

mkRustEnum :: CtxRepr ctx -> f IsizeType -> f (VariantType ctx) -> App ext f (RustEnumType ctx)
mkRustEnum ctx discr variant = MkStruct (RustEnumFieldsRepr ctx) (Empty :> discr :> variant)

rustEnumDiscriminant :: f (RustEnumType ctx) -> App ext f IsizeType
rustEnumDiscriminant e = GetStruct e i1of2 IsizeRepr

rustEnumVariant :: CtxRepr ctx -> f (RustEnumType ctx) -> App ext f (VariantType ctx)
rustEnumVariant ctx e = GetStruct e i2of2 (VariantRepr ctx)


-- Rust usize/isize representation

type SizeBits = 32

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
usizeLit = BVLit knownRepr

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

vectorGetUsize :: (TypeRepr tp) ->
    (App ext f NatType -> f NatType) ->
    f (VectorType tp) -> f UsizeType -> App ext f tp
vectorGetUsize tpr wrap vec idx = VectorGetEntry tpr vec (wrap $ usizeToNat idx)

vectorSetUsize :: (TypeRepr tp) ->
    (App ext f NatType -> f NatType) ->
    f (VectorType tp) -> f UsizeType -> f tp -> App ext f (VectorType tp)
vectorSetUsize tpr wrap vec idx val = VectorSetEntry tpr vec (wrap $ usizeToNat idx) val

vectorSizeUsize ::
    (forall tp'. App ext f tp' -> f tp') ->
    f (VectorType tp) -> App ext f UsizeType
vectorSizeUsize wrap vec = natToUsize wrap $ wrap $ VectorSize vec


isizeLit :: Integer -> App ext f IsizeType
isizeLit = BVLit knownRepr

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


--------------------------------------------------------------
-- * A MirReference is a Crucible RefCell paired with a path to a sub-component
--
-- We use this to represent mutable data

type MirReferenceSymbol = "MirReference"
type MirReferenceType tp = IntrinsicType MirReferenceSymbol (EmptyCtx ::> tp)

pattern MirReferenceRepr :: () => tp' ~ MirReferenceType tp => TypeRepr tp -> TypeRepr tp'
pattern MirReferenceRepr tp <-
     IntrinsicRepr (testEquality (knownSymbol @MirReferenceSymbol) -> Just Refl) (Empty :> tp)
 where MirReferenceRepr tp = IntrinsicRepr (knownSymbol @MirReferenceSymbol) (Empty :> tp)

type family MirReferenceFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MirReferenceFam sym (EmptyCtx ::> tp) = MirReference sym tp
  MirReferenceFam sym ctx = TypeError ('Text "MirRefeence expects a single argument, but was given" ':<>:
                                       'ShowType ctx)
instance IsExprBuilder sym => IntrinsicClass sym MirReferenceSymbol where
  type Intrinsic sym MirReferenceSymbol ctx = MirReferenceFam sym ctx

  muxIntrinsic sym _tys _nm (Empty :> _tp) = muxRef sym
  muxIntrinsic _sym _tys nm ctx = typeError nm ctx

data MirReferenceRoot sym :: CrucibleType -> Type where
  RefCell_RefRoot :: !(RefCell tp) -> MirReferenceRoot sym tp
  GlobalVar_RefRoot :: !(GlobalVar tp) -> MirReferenceRoot sym tp

data MirReferencePath sym :: CrucibleType -> CrucibleType -> Type where
  Empty_RefPath :: MirReferencePath sym tp tp
  Any_RefPath ::
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base AnyType) ->
    MirReferencePath sym  tp_base tp
  Field_RefPath ::
    !(CtxRepr ctx) ->
    !(MirReferencePath sym tp_base (StructType ctx)) ->
    !(Index ctx tp) ->
    MirReferencePath sym tp_base tp
  Variant_RefPath ::
    !(CtxRepr ctx) ->
    !(MirReferencePath sym tp_base (RustEnumType ctx)) ->
    !(Index ctx tp) ->
    MirReferencePath sym tp_base tp
  Index_RefPath ::
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base (VectorType tp)) ->
    !(RegValue sym UsizeType) ->
    MirReferencePath sym tp_base tp
  Just_RefPath ::
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base (MaybeType tp)) ->
    MirReferencePath sym tp_base tp

data MirReference sym (tp :: CrucibleType) where
  MirReference ::
    !(MirReferenceRoot sym tpr) ->
    !(MirReferencePath sym tpr tp) ->
    MirReference sym tp

refRootType :: MirReferenceRoot sym tp -> TypeRepr tp
refRootType (RefCell_RefRoot r) = refType r
refRootType (GlobalVar_RefRoot r) = globalType r

instance TestEquality (MirReferenceRoot sym) where
    RefCell_RefRoot x `testEquality` RefCell_RefRoot y = x `testEquality` y
    GlobalVar_RefRoot x `testEquality` GlobalVar_RefRoot y = x `testEquality` y
    _ `testEquality` _ = Nothing

muxRefPath ::
  IsExprBuilder sym =>
  sym ->
  Pred sym ->
  MirReferencePath sym tp_base tp ->
  MirReferencePath sym tp_base tp ->
  MaybeT IO (MirReferencePath sym tp_base tp)
muxRefPath sym c path1 path2 = case (path1,path2) of
  (Empty_RefPath, Empty_RefPath) -> return Empty_RefPath
  (Any_RefPath ctx1 p1, Any_RefPath ctx2 p2)
    | Just Refl <- testEquality ctx1 ctx2 ->
         do p' <- muxRefPath sym c p1 p2
            return (Any_RefPath ctx1 p')
  (Field_RefPath ctx1 p1 f1, Field_RefPath ctx2 p2 f2)
    | Just Refl <- testEquality ctx1 ctx2
    , Just Refl <- testEquality f1 f2 ->
         do p' <- muxRefPath sym c p1 p2
            return (Field_RefPath ctx1 p' f1)
  (Variant_RefPath ctx1 p1 f1, Variant_RefPath ctx2 p2 f2)
    | Just Refl <- testEquality ctx1 ctx2
    , Just Refl <- testEquality f1 f2 ->
         do p' <- muxRefPath sym c p1 p2
            return (Variant_RefPath ctx1 p' f1)
  (Index_RefPath tp p1 i1, Index_RefPath _ p2 i2) ->
         do p' <- muxRefPath sym c p1 p2
            i' <- lift $ bvIte sym c i1 i2
            return (Index_RefPath tp p' i')
  (Just_RefPath tp p1, Just_RefPath _ p2) ->
         do p' <- muxRefPath sym c p1 p2
            return (Just_RefPath tp p')
  _ -> mzero

muxRef :: forall sym tp.
  IsExprBuilder sym =>
  sym ->
  Pred sym ->
  MirReference sym tp ->
  MirReference sym tp ->
  IO (MirReference sym tp)
muxRef sym c (MirReference r1 p1) (MirReference r2 p2) =
   runMaybeT action >>= \case
     Nothing -> fail "Incompatible MIR reference merge"
     Just x  -> return x

  where
  action :: MaybeT IO (MirReference sym tp)
  action =
    do Refl <- MaybeT (return $ testEquality (refRootType r1) (refRootType r2))
       Refl <- MaybeT (return $ testEquality r1 r2)
       p' <- muxRefPath sym c p1 p2
       return (MirReference r1 p')


--------------------------------------------------------------
-- A MirVectorType is dynamically either a VectorType or a SymbolicArrayType.
-- We use this in `MirSlice` to allow taking slices of either
-- `crucible::vector::Vector` or `crucible::array::Array`.

-- Aliases for working with MIR arrays, which have a single usize index.
type UsizeArrayType btp = SymbolicArrayType (EmptyCtx ::> BaseUsizeType) btp
pattern UsizeArrayRepr :: () => tp' ~ UsizeArrayType btp => BaseTypeRepr btp -> TypeRepr tp'
pattern UsizeArrayRepr btp <-
    SymbolicArrayRepr (testEquality (Empty :> BaseUsizeRepr) -> Just Refl) btp
  where UsizeArrayRepr btp = SymbolicArrayRepr (Empty :> BaseUsizeRepr) btp


type MirVectorSymbol = "MirVector"
type MirVectorType tp = IntrinsicType MirVectorSymbol (EmptyCtx ::> tp)

pattern MirVectorRepr :: () => tp' ~ MirVectorType tp => TypeRepr tp -> TypeRepr tp'
pattern MirVectorRepr tp <-
     IntrinsicRepr (testEquality (knownSymbol @MirVectorSymbol) -> Just Refl) (Empty :> tp)
 where MirVectorRepr tp = IntrinsicRepr (knownSymbol @MirVectorSymbol) (Empty :> tp)

type family MirVectorFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MirVectorFam sym (EmptyCtx ::> tp) = MirVector sym tp
  MirVectorFam sym ctx = TypeError ('Text "MirVector expects a single argument, but was given" ':<>:
                                       'ShowType ctx)
instance IsSymInterface sym => IntrinsicClass sym MirVectorSymbol where
  type Intrinsic sym MirVectorSymbol ctx = MirVectorFam sym ctx

  muxIntrinsic sym tys _nm (Empty :> tpr) = muxMirVector sym tys tpr
  muxIntrinsic _sym _tys nm ctx = typeError nm ctx

data MirVector sym (tp :: CrucibleType) where
  MirVector_Vector ::
    !(RegValue sym (VectorType tp)) ->
    MirVector sym tp
  MirVector_Array ::
    !(RegValue sym (UsizeArrayType btp)) ->
    MirVector sym (BaseToType btp)

muxMirVector :: forall sym tp.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  TypeRepr tp ->
  Pred sym ->
  MirVector sym tp ->
  MirVector sym tp ->
  IO (MirVector sym tp)
muxMirVector sym itefns tpr c (MirVector_Vector v1) (MirVector_Vector v2) =
    MirVector_Vector <$> muxRegForType sym itefns (VectorRepr tpr) c v1 v2
muxMirVector sym itefns (asBaseType -> AsBaseType btpr) c
        (MirVector_Array a1) (MirVector_Array a2) =
    MirVector_Array <$> muxRegForType sym itefns (UsizeArrayRepr btpr) c a1 a2
muxMirVector sym _ _ _ _ _ =
    addFailedAssertion sym $ Unsupported $ "Cannot merge dissimilar MirVectors."



-- | Sigil type indicating the MIR syntax extension
data MIR
type instance ExprExtension MIR = EmptyExprExtension
type instance StmtExtension MIR = MirStmt
type instance AssertionClassifier MIR = NoAssertionClassifier

-- First `Any` is the data pointer - either an immutable or mutable reference.
-- Second `Any` is the vtable.
type DynRefType = StructType (EmptyCtx ::> AnyType ::> AnyType)

dynRefDataIndex :: Index (EmptyCtx ::> AnyType ::> AnyType) AnyType
dynRefDataIndex = skipIndex baseIndex

dynRefVtableIndex :: Index (EmptyCtx ::> AnyType ::> AnyType) AnyType
dynRefVtableIndex = lastIndex (incSize $ incSize zeroSize)


data MirStmt :: (CrucibleType -> Type) -> CrucibleType -> Type where
  MirNewRef ::
     !(TypeRepr tp) ->
     MirStmt f (MirReferenceType tp)
  MirGlobalRef ::
     GlobalVar tp ->
     MirStmt f (MirReferenceType tp)
  MirReadRef ::
     !(TypeRepr tp) ->
     !(f (MirReferenceType tp)) ->
     MirStmt f tp
  MirWriteRef ::
     !(f (MirReferenceType tp)) ->
     !(f tp) ->
     MirStmt f UnitType
  MirDropRef ::
     !(f (MirReferenceType tp)) ->
     MirStmt f UnitType
  MirSubanyRef ::
     !(TypeRepr tp) ->
     !(f (MirReferenceType AnyType)) ->
     MirStmt f (MirReferenceType tp)
  MirSubfieldRef ::
     !(CtxRepr ctx) ->
     !(f (MirReferenceType (StructType ctx))) ->
     !(Index ctx tp) ->
     MirStmt f (MirReferenceType tp)
  MirSubvariantRef ::
     !(CtxRepr ctx) ->
     !(f (MirReferenceType (RustEnumType ctx))) ->
     !(Index ctx tp) ->
     MirStmt f (MirReferenceType tp)
  MirSubindexRef ::
     !(TypeRepr tp) ->
     !(f (MirReferenceType (VectorType tp))) ->
     !(f UsizeType) ->
     MirStmt f (MirReferenceType tp)
  MirSubjustRef ::
     !(TypeRepr tp) ->
     !(f (MirReferenceType (MaybeType tp))) ->
     MirStmt f (MirReferenceType tp)
  VectorSnoc ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     !(f tp) ->
     MirStmt f (VectorType tp)
  VectorHead ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     MirStmt f (MaybeType tp)
  VectorTail ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     MirStmt f (VectorType tp)
  VectorInit ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     MirStmt f (VectorType tp)
  VectorLast ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     MirStmt f (MaybeType tp)
  VectorConcat ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     !(f (VectorType tp)) ->
     MirStmt f (VectorType tp)
  VectorTake ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     !(f NatType) ->
     MirStmt f (VectorType tp)
  VectorDrop ::
     !(TypeRepr tp) ->
     !(f (VectorType tp)) ->
     !(f NatType) ->
     MirStmt f (VectorType tp)
  ArrayZeroed ::
     (1 <= w) =>
     !(Assignment BaseTypeRepr (idxs ::> idx)) ->
     !(NatRepr w) ->
     MirStmt f (SymbolicArrayType (idxs ::> idx) (BaseBVType w))
  MirVector_FromVector ::
    !(TypeRepr tp) ->
    !(f (VectorType tp)) ->
    MirStmt f (MirVectorType tp)
  MirVector_FromArray ::
    !(BaseTypeRepr btp) ->
    !(f (UsizeArrayType btp)) ->
    MirStmt f (MirVectorType (BaseToType btp))
  MirVector_Lookup ::
    !(TypeRepr tp) ->
    !(f (MirVectorType tp)) ->
    !(f UsizeType) ->
    MirStmt f tp
  MirVector_Update ::
    !(TypeRepr tp) ->
    !(f (MirVectorType tp)) ->
    !(f UsizeType) ->
    !(f tp) ->
    MirStmt f (MirVectorType tp)

$(return [])


traverseMirStmt ::
  Applicative m =>
  (forall t. e t -> m (f t)) ->
  (forall t. MirStmt e t -> m (MirStmt f t))
traverseMirStmt = $(U.structuralTraversal [t|MirStmt|] [])

instance TestEqualityFC MirStmt where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|MirStmt|]
       [ (U.DataArg 0 `U.TypeApp` U.AnyType, [|testSubterm|])
       , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|BaseTypeRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|Assignment|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testEquality|])
       ])
instance TestEquality f => TestEquality (MirStmt f) where
  testEquality = testEqualityFC testEquality

instance OrdFC MirStmt where
  compareFC compareSubterm =
    $(U.structuralTypeOrd [t|MirStmt|]
       [ (U.DataArg 0 `U.TypeApp` U.AnyType, [|compareSubterm|])
       , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|BaseTypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|Assignment|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareF|])
       ])

instance TypeApp MirStmt where
  appType = \case
    MirNewRef tp    -> MirReferenceRepr tp
    MirGlobalRef gv -> MirReferenceRepr (globalType gv)
    MirReadRef tp _ -> tp
    MirWriteRef _ _ -> UnitRepr
    MirDropRef _    -> UnitRepr
    MirSubanyRef tp _ -> MirReferenceRepr tp
    MirSubfieldRef ctx _ idx -> MirReferenceRepr (ctx ! idx)
    MirSubvariantRef ctx _ idx -> MirReferenceRepr (ctx ! idx)
    MirSubindexRef tp _ _ -> MirReferenceRepr tp
    MirSubjustRef tp _ -> MirReferenceRepr tp
    VectorSnoc tp _ _ -> VectorRepr tp
    VectorHead tp _ -> MaybeRepr tp
    VectorTail tp _ -> VectorRepr tp
    VectorInit tp _ -> VectorRepr tp
    VectorLast tp _ -> MaybeRepr tp
    VectorConcat tp _ _ -> VectorRepr tp
    VectorTake tp _ _ -> VectorRepr tp
    VectorDrop tp _ _ -> VectorRepr tp
    ArrayZeroed idxs w -> SymbolicArrayRepr idxs (BaseBVRepr w)
    MirVector_FromVector tp _ -> MirVectorRepr tp
    MirVector_FromArray btp _ -> MirVectorRepr (baseToType btp)
    MirVector_Lookup tp _ _ -> tp
    MirVector_Update tp _ _ _ -> MirVectorRepr tp

instance PrettyApp MirStmt where
  ppApp pp = \case 
    MirNewRef tp -> "newMirRef" <+> pretty tp
    MirGlobalRef gv -> "globalMirRef" <+> pretty gv
    MirReadRef _ x  -> "readMirRef" <+> pp x
    MirWriteRef x y -> "writeMirRef" <+> pp x <+> "<-" <+> pp y
    MirDropRef x    -> "dropMirRef" <+> pp x
    MirSubanyRef tpr x -> "subanyRef" <+> pretty tpr <+> pp x
    MirSubfieldRef _ x idx -> "subfieldRef" <+> pp x <+> text (show idx)
    MirSubvariantRef _ x idx -> "subvariantRef" <+> pp x <+> text (show idx)
    MirSubindexRef _ x idx -> "subindexRef" <+> pp x <+> pp idx
    MirSubjustRef _ x -> "subjustRef" <+> pp x
    VectorSnoc _ v e -> "vectorSnoc" <+> pp v <+> pp e
    VectorHead _ v -> "vectorHead" <+> pp v
    VectorTail _ v -> "vectorTail" <+> pp v
    VectorInit _ v -> "vectorInit" <+> pp v
    VectorLast _ v -> "vectorLast" <+> pp v
    VectorConcat _ v1 v2 -> "vectorConcat" <+> pp v1 <+> pp v2
    VectorTake _ v i -> "vectorTake" <+> pp v <+> pp i
    VectorDrop _ v i -> "vectorDrop" <+> pp v <+> pp i
    ArrayZeroed idxs w -> "arrayZeroed" <+> text (show idxs) <+> text (show w)
    MirVector_FromVector tp v -> "mirVector_fromVector" <+> pretty tp <+> pp v
    MirVector_FromArray btp a -> "mirVector_fromArray" <+> pretty btp <+> pp a
    MirVector_Lookup _ v i -> "mirVector_lookup" <+> pp v <+> pp i
    MirVector_Update _ v i x -> "mirVector_update" <+> pp v <+> pp i <+> pp x


instance FunctorFC MirStmt where
  fmapFC = fmapFCDefault
instance FoldableFC MirStmt where
  foldMapFC = foldMapFCDefault
instance TraversableFC MirStmt where
  traverseFC = traverseMirStmt


instance HasStructuredAssertions MIR where
  explain _       = \case
  toPredicate _ _ = \case
      

instance IsSyntaxExtension MIR

readBeforeWriteMsg :: SimErrorReason
readBeforeWriteMsg = ReadBeforeWriteSimError
    "Attempted to read uninitialized reference cell"

readRefRoot :: IsSymInterface sym =>
    SimState p sym ext rtp f a ->
    sym ->
    MirReferenceRoot sym tp ->
    IO (RegValue sym tp)
readRefRoot s sym (RefCell_RefRoot rc) =
    readPartExpr sym (lookupRef rc (s ^. stateTree . actFrame . gpGlobals)) readBeforeWriteMsg
readRefRoot s sym (GlobalVar_RefRoot gv) =
    case lookupGlobal gv (s ^. stateTree . actFrame . gpGlobals) of
        Just x -> return x
        Nothing -> addFailedAssertion sym readBeforeWriteMsg
    
writeRefRoot :: IsSymInterface sym =>
    SimState p sym ext rtp f a ->
    sym ->
    MirReferenceRoot sym tp ->
    RegValue sym tp ->
    SimState p sym ext rtp f a
writeRefRoot s sym (RefCell_RefRoot rc) v =
    s & stateTree . actFrame . gpGlobals %~ insertRef sym rc v
writeRefRoot s _sym (GlobalVar_RefRoot gv) v =
    s & stateTree . actFrame . gpGlobals %~ insertGlobal gv v

execMirStmt :: IsSymInterface sym => EvalStmtFunc p sym MIR
execMirStmt stmt s =
  let ctx = s^.stateContext
      sym = ctx^.ctxSymInterface
      halloc = simHandleAllocator ctx
      iTypes = ctxIntrinsicTypes ctx
  in case stmt of
       MirNewRef tp ->
         do r <- freshRefCell halloc tp
            let r' = MirReference (RefCell_RefRoot r) Empty_RefPath
            return (r', s)

       MirGlobalRef gv ->
         do let r = MirReference (GlobalVar_RefRoot gv) Empty_RefPath
            return (r, s)

       MirDropRef (regValue -> MirReference r path) ->
         case path of
           Empty_RefPath ->
             case r of
               RefCell_RefRoot rc ->
                 do let s' = s & stateTree . actFrame . gpGlobals %~ dropRef rc
                    return ((), s')
               GlobalVar_RefRoot _gv ->
                 addFailedAssertion sym (GenericSimError "Cannot drop a global variable")
           _ -> addFailedAssertion sym (GenericSimError "Cannot drop an interior reference")

       MirReadRef _tp (regValue -> MirReference r path) ->
         do v <- readRefRoot s sym r
            v' <- readRefPath sym iTypes v path
            return (v', s)

       MirWriteRef (regValue -> MirReference r Empty_RefPath) (regValue -> x) ->
         do let s' = writeRefRoot s sym r x
            return ((), s')
       MirWriteRef (regValue -> MirReference r path) (regValue -> x) ->
         do v <- readRefRoot s sym r
            v' <- writeRefPath sym iTypes v path x
            let s' = writeRefRoot s sym r v'
            return ((), s')
       MirSubanyRef tp (regValue -> MirReference r path) ->
         do let r' = MirReference r (Any_RefPath tp path)
            return (r', s)
       MirSubfieldRef ctx0 (regValue -> MirReference r path) idx ->
         do let r' = MirReference r (Field_RefPath ctx0 path idx)
            return (r', s)
       MirSubvariantRef ctx0 (regValue -> MirReference r path) idx ->
         do let r' = MirReference r (Variant_RefPath ctx0 path idx)
            return (r', s)
       MirSubindexRef tp (regValue -> MirReference r path) (regValue -> idx) ->
         do let r' = MirReference r (Index_RefPath tp path idx)
            return (r', s)
       MirSubjustRef tp (regValue -> MirReference r path) ->
         do let r' = MirReference r (Just_RefPath tp path)
            return (r', s)
       VectorSnoc _tp (regValue -> vecValue) (regValue -> elemValue) ->
            return (V.snoc vecValue elemValue, s)
       VectorHead _tp (regValue -> vecValue) -> do
            let val = maybePartExpr sym $
                    if V.null vecValue then Nothing else Just $ V.head vecValue
            return (val, s)
       VectorTail _tp (regValue -> vecValue) ->
            return (if V.null vecValue then V.empty else V.tail vecValue, s)
       VectorInit _tp (regValue -> vecValue) ->
            return (if V.null vecValue then V.empty else V.init vecValue, s)
       VectorLast _tp (regValue -> vecValue) -> do
            let val = maybePartExpr sym $
                    if V.null vecValue then Nothing else Just $ V.last vecValue
            return (val, s)
       VectorConcat _tp (regValue -> v1) (regValue -> v2) ->
            return (v1 <> v2, s)
       VectorTake _tp (regValue -> v) (regValue -> idx) -> case asConcrete idx of
            Just (ConcreteNat idx') -> return (V.take (fromIntegral idx') v, s)
            Nothing -> addFailedAssertion sym $
                GenericSimError "VectorTake index must be concrete"
       VectorDrop _tp (regValue -> v) (regValue -> idx) -> case asConcrete idx of
            Just (ConcreteNat idx') -> return (V.drop (fromIntegral idx') v, s)
            Nothing -> addFailedAssertion sym $
                GenericSimError "VectorDrop index must be concrete"
       ArrayZeroed idxs w -> do
            zero <- bvLit sym w 0
            val <- constantArray sym idxs zero
            return (val, s)

       MirVector_FromVector _tp (regValue -> v) ->
            return (MirVector_Vector v, s)
       MirVector_FromArray _tp (regValue -> a) ->
            return (MirVector_Array a, s)
       MirVector_Lookup tpr (regValue -> MirVector_Vector v) (regValue -> i) -> do
            i' <- bvToNat sym i
            x <- indexVectorWithSymNat sym (muxRegForType sym iTypes tpr) v i'
            return (x, s)
       MirVector_Lookup _tp (regValue -> MirVector_Array a) (regValue -> i) -> do
            x <- arrayLookup sym a (Empty :> i)
            return (x, s)
       MirVector_Update tpr (regValue -> MirVector_Vector v) (regValue -> i) (regValue -> x) -> do
            i' <- bvToNat sym i
            v' <- updateVectorWithSymNat sym (muxRegForType sym iTypes tpr) v i' x
            return (MirVector_Vector v', s)
       MirVector_Update _tp (regValue -> MirVector_Array a) (regValue -> i) (regValue -> x) -> do
            a' <- arrayUpdate sym a (Empty :> i) x
            return (MirVector_Array a', s)

writeRefPath :: IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  RegValue sym tp' ->
  IO (RegValue sym tp)
writeRefPath sym iTypes v path x =
  adjustRefPath sym iTypes v path (\_ -> return x)


adjustRefPath :: IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  (RegValue sym tp' -> IO (RegValue sym tp')) ->
  IO (RegValue sym tp)
adjustRefPath sym iTypes v path0 adj = case path0 of
  Empty_RefPath -> adj v
  Any_RefPath tpr path ->
      adjustRefPath sym iTypes v path (\(AnyValue vtp x) ->
         case testEquality vtp tpr of
           Nothing -> fail ("Any type mismatch! Expected: " ++ show tpr ++
                            "\nbut got: " ++ show vtp)
           Just Refl -> AnyValue vtp <$> adj x
         )
  Field_RefPath _ctx path fld ->
      adjustRefPath sym iTypes v path
        (\x -> adjustM (\x' -> RV <$> adj (unRV x')) fld x)
  Variant_RefPath _ctx path fld ->
      -- TODO: report an error if variant `fld` is not selected
      adjustRefPath sym iTypes v path (field @1 (\(RV x) ->
        RV <$> adjustM (\x' -> VB <$> mapM adj (unVB x')) fld x))
  Index_RefPath tp path idx ->
      adjustRefPath sym iTypes v path (\v' -> do
        idx' <- bvToNat sym idx
        adjustVectorWithSymNat sym (muxRegForType sym iTypes tp) v' idx' adj)
  Just_RefPath _tp path ->
      adjustRefPath sym iTypes v path (\v' -> mapM adj v')


readRefPath :: IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  IO (RegValue sym tp')
readRefPath sym iTypes v = \case
  Empty_RefPath -> return v
  Any_RefPath tpr path ->
    do AnyValue vtp x <- readRefPath sym iTypes v path
       case testEquality vtp tpr of
         Nothing -> fail ("Any type mismatch! Expected: " ++ show tpr ++ 
                           "\nbut got: " ++ show vtp)
         Just Refl -> return x
  Field_RefPath _ctx path fld ->
    do flds <- readRefPath sym iTypes v path
       return $ unRV $ flds ! fld
  Variant_RefPath ctx path fld ->
    do (Empty :> _discr :> RV variant) <- readRefPath sym iTypes v path
       let msg = GenericSimError $
               "attempted to read from wrong variant (" ++ show fld ++ " of " ++ show ctx ++ ")"
       readPartExpr sym (unVB $ variant ! fld) msg
  Index_RefPath tp path idx ->
    do v' <- readRefPath sym iTypes v path
       idx' <- bvToNat sym idx
       indexVectorWithSymNat sym (muxRegForType sym iTypes tp) v' idx'
  Just_RefPath tp path ->
    do v' <- readRefPath sym iTypes v path
       let msg = ReadBeforeWriteSimError $
               "attempted to read from uninitialized Maybe of type " ++ show tp
       readPartExpr sym v' msg


mirExtImpl :: forall sym p. IsSymInterface sym => ExtensionImpl p sym MIR
mirExtImpl = ExtensionImpl
             { extensionEval = \_sym -> \case
             , extensionExec = execMirStmt
             }

--------------------------------------------------------------------------------
-- ** Slices

-- A Slice is a sequence of values plus an index to the first element
-- and a length.

type MirSlice tp     = StructType (EmptyCtx ::>
                           MirReferenceType (VectorType tp) ::> -- values
                           UsizeType ::>    --- first element
                           UsizeType)       --- length

pattern MirSliceRepr :: () => tp' ~ MirSlice tp => TypeRepr tp -> TypeRepr tp'
pattern MirSliceRepr tp <- StructRepr
     (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignEmpty)
         (MirReferenceRepr (VectorRepr tp)))
         UsizeRepr)
         UsizeRepr)
 where MirSliceRepr tp = StructRepr (Empty :> MirReferenceRepr (VectorRepr tp) :> UsizeRepr :> UsizeRepr)

mirSliceCtxRepr :: TypeRepr tp -> CtxRepr (EmptyCtx ::>
                           MirReferenceType (VectorType tp) ::>
                           UsizeType ::>
                           UsizeType)
mirSliceCtxRepr tp = (Empty :> MirReferenceRepr (VectorRepr tp) :> UsizeRepr :> UsizeRepr)

getSliceVector :: Expr MIR s (MirSlice tp) -> Expr MIR s (MirReferenceType (VectorType tp))
getSliceVector e = getStruct i1of3 e

getSliceLB :: Expr MIR s (MirSlice tp) -> Expr MIR s UsizeType
getSliceLB e = getStruct i2of3 e 

getSliceLen :: Expr MIR s (MirSlice tp) -> Expr MIR s UsizeType
getSliceLen e = getStruct i3of3 e

updateSliceLB :: TypeRepr tp -> Expr MIR s (MirSlice tp) -> Expr MIR s UsizeType ->  Expr MIR s (MirSlice tp)
updateSliceLB tp e start = setStruct (mirSliceCtxRepr tp) e i2of3 ns where
   os = getStruct i2of3 e
   ns = App $ usizeAdd os start

updateSliceLen :: TypeRepr tp -> Expr MIR s (MirSlice tp) -> Expr MIR s UsizeType -> Expr MIR s (MirSlice tp)
updateSliceLen tp e end = setStruct (mirSliceCtxRepr tp) e i3of3 end where

--------------------------------------------------------------------------------
-- ** Immutable slices

-- A Slice is a sequence of values plus an index to the first element
-- and a length.

type MirImmSlice tp     = StructType (EmptyCtx ::>
                           VectorType tp ::> -- values
                           UsizeType ::>    --- first element
                           UsizeType)       --- length

pattern MirImmSliceRepr :: () => tp' ~ MirImmSlice tp => TypeRepr tp -> TypeRepr tp'
pattern MirImmSliceRepr tp <- StructRepr
     (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignEmpty)
         (VectorRepr tp))
         UsizeRepr)
         UsizeRepr)
 where MirImmSliceRepr tp = StructRepr (Empty :> VectorRepr tp :> UsizeRepr :> UsizeRepr)

mirImmSliceCtxRepr :: TypeRepr tp -> CtxRepr (EmptyCtx ::>
                           VectorType tp ::>
                           UsizeType ::>
                           UsizeType)
mirImmSliceCtxRepr tp = (Empty :> VectorRepr tp :> UsizeRepr :> UsizeRepr)

getImmSliceVector :: Expr MIR s (MirImmSlice tp) -> Expr MIR s (VectorType tp)
getImmSliceVector e = getStruct i1of3 e

getImmSliceLB :: Expr MIR s (MirImmSlice tp) -> Expr MIR s UsizeType
getImmSliceLB e = getStruct i2of3 e

getImmSliceLen :: Expr MIR s (MirImmSlice tp) -> Expr MIR s UsizeType
getImmSliceLen e = getStruct i3of3 e

updateImmSliceLB :: TypeRepr tp -> Expr MIR s (MirImmSlice tp) -> Expr MIR s UsizeType ->  Expr MIR s (MirImmSlice tp)
updateImmSliceLB tp e start = setStruct (mirImmSliceCtxRepr tp) e i2of3 ns where
   os = getStruct i2of3 e
   ns = App $ usizeAdd os start

updateImmSliceLen :: TypeRepr tp -> Expr MIR s (MirImmSlice tp) -> Expr MIR s UsizeType -> Expr MIR s (MirImmSlice tp)
updateImmSliceLen tp e end = setStruct (mirImmSliceCtxRepr tp) e i3of3 end where
