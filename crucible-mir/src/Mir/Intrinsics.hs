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
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

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

import           GHC.Stack
import           GHC.TypeLits
import           Control.Lens hiding (Empty, (:>), Index, view)
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Maybe
import qualified Data.BitVector.Sized as BV
import           Data.Kind(Type)
import           Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Maybe as Maybe
import qualified Data.Vector as V
import           Data.Word

import           Prettyprinter

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context hiding (init)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.TH.GADT as U
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as N

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator hiding (dropRef)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Panic
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree hiding (FnState)
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           What4.Interface
import           What4.Partial
    (PartExpr, pattern Unassigned, maybePartExpr, justPartExpr, mergePartial, mkPE)

import           Mir.FancyMuxTree



-- Rust enum representation

-- A Rust enum, whose variants have the types listed in `ctx`.
type RustEnumType discrTp variantsCtx = StructType (RustEnumFields discrTp variantsCtx)
type RustEnumFields discrTp variantsCtx = EmptyCtx ::> discrTp ::> VariantType variantsCtx

data SomeRustEnumRepr where
  SomeRustEnumRepr ::
    !(TypeRepr discrTp) ->
    !(CtxRepr variantsCtx) ->
    SomeRustEnumRepr

pattern RustEnumFieldsRepr :: () => ctx ~ RustEnumFields discrTp variantsCtx => TypeRepr discrTp -> CtxRepr variantsCtx -> CtxRepr ctx
pattern RustEnumFieldsRepr discrTp variantsCtx = Empty :> discrTp :> VariantRepr variantsCtx
pattern RustEnumRepr :: () => tp ~ RustEnumType discrTp variantsCtx => TypeRepr discrTp -> CtxRepr variantsCtx -> TypeRepr tp
pattern RustEnumRepr discrTp variantsCtx = StructRepr (RustEnumFieldsRepr discrTp variantsCtx)

mkRustEnum :: TypeRepr discrTp -> CtxRepr variantsCtx -> f discrTp -> f (VariantType variantsCtx) -> App ext f (RustEnumType discrTp variantsCtx)
mkRustEnum discrTp variantsCtx discr variant = MkStruct (RustEnumFieldsRepr discrTp variantsCtx) (Empty :> discr :> variant)

rustEnumDiscriminant :: TypeRepr discrTp -> f (RustEnumType discrTp variantsCtx) -> App ext f discrTp
rustEnumDiscriminant discrTp e = GetStruct e i1of2 discrTp

rustEnumVariant :: CtxRepr variantsCtx -> f (RustEnumType discrTp variantsCtx) -> App ext f (VariantType variantsCtx)
rustEnumVariant variantsCtx e = GetStruct e i2of2 (VariantRepr variantsCtx)


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


--------------------------------------------------------------
-- * A MirReference is a Crucible RefCell (or other root) paired with a path to a sub-component
--
-- We use this to represent pointers and references.

type MirReferenceSymbol = "MirReference"
type MirReferenceType = IntrinsicType MirReferenceSymbol EmptyCtx

pattern MirReferenceRepr :: () => tp ~ MirReferenceType => TypeRepr tp
pattern MirReferenceRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MirReferenceSymbol) -> Just Refl) Empty
 where MirReferenceRepr = IntrinsicRepr (knownSymbol @MirReferenceSymbol) Empty

type family MirReferenceFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MirReferenceFam sym EmptyCtx = MirReferenceMux sym
  MirReferenceFam sym ctx = TypeError ('Text "MirRefeence expects a single argument, but was given" :<>:
                                       'ShowType ctx)
instance IsSymInterface sym => IntrinsicClass sym MirReferenceSymbol where
  type Intrinsic sym MirReferenceSymbol ctx = MirReferenceFam sym ctx

  muxIntrinsic sym iTypes _nm Empty = muxRef sym iTypes
  muxIntrinsic _sym _tys nm ctx = typeError nm ctx

data MirReferenceRoot sym :: CrucibleType -> Type where
  RefCell_RefRoot :: !(RefCell tp) -> MirReferenceRoot sym tp
  GlobalVar_RefRoot :: !(GlobalVar tp) -> MirReferenceRoot sym tp
  Const_RefRoot :: !(TypeRepr tp) -> !(RegValue sym tp) -> MirReferenceRoot sym tp

data MirReferencePath sym :: CrucibleType -> CrucibleType -> Type where
  Empty_RefPath :: MirReferencePath sym tp tp
  Field_RefPath ::
    !(CtxRepr ctx) ->
    !(MirReferencePath sym tp_base (StructType ctx)) ->
    !(Index ctx tp) ->
    MirReferencePath sym tp_base tp
  Variant_RefPath ::
    !(TypeRepr discrTp) ->
    !(CtxRepr variantsCtx) ->
    !(MirReferencePath sym tp_base (RustEnumType discrTp variantsCtx)) ->
    !(Index variantsCtx tp) ->
    MirReferencePath sym tp_base tp
  Just_RefPath ::
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base (MaybeType tp)) ->
    MirReferencePath sym tp_base tp
  -- | Access an entry in a @Vector@ (backed by a Crucible 'V.Vector').
  VectorIndex_RefPath ::
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base (VectorType tp)) ->
    !(RegValue sym UsizeType) ->
    MirReferencePath sym tp_base tp
  -- | Access an entry in an @Array@ (backed by an SMT array).
  ArrayIndex_RefPath ::
    !(BaseTypeRepr btp) ->
    !(MirReferencePath sym tp_base (UsizeArrayType btp)) ->
    !(RegValue sym UsizeType) ->
    MirReferencePath sym tp_base (BaseToType btp)
  -- | Access an entry in a `MirAggregate`.
  AgElem_RefPath ::
    !(RegValue sym UsizeType) ->
    -- | Size in bytes of the entry to access
    !Word ->
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base MirAggregateType) ->
    MirReferencePath sym tp_base tp

data MirReference sym where
  MirReference ::
    !(TypeRepr tp) ->
    !(MirReferenceRoot sym tpr) ->
    !(MirReferencePath sym tpr tp) ->
    MirReference sym
  -- The result of an integer-to-pointer cast.  Guaranteed not to be
  -- dereferenceable.
  MirReference_Integer ::
    !(RegValue sym UsizeType) ->
    MirReference sym

data MirReferenceMux sym where
  MirReferenceMux :: !(FancyMuxTree sym (MirReference sym)) -> MirReferenceMux sym

instance IsSymInterface sym => Show (MirReferenceRoot sym tp) where
    show (RefCell_RefRoot rc) = "(RefCell_RefRoot " ++ show rc ++ ")"
    show (GlobalVar_RefRoot gv) = "(GlobalVar_RefRoot " ++ show gv ++ ")"
    show (Const_RefRoot tpr _) = "(Const_RefRoot " ++ show tpr ++ " _)"

instance IsSymInterface sym => Show (MirReferencePath sym tp tp') where
    show Empty_RefPath = "Empty_RefPath"
    show (Field_RefPath ctx p idx) = "(Field_RefPath " ++ show ctx ++ " " ++ show p ++ " " ++ show idx ++ ")"
    show (Variant_RefPath tp ctx p idx) = "(Variant_RefPath " ++ show tp ++ " " ++ show ctx ++ " " ++ show p ++ " " ++ show idx ++ ")"
    show (Just_RefPath tpr p) = "(Just_RefPath " ++ show tpr ++ " " ++ show p ++ ")"
    show (VectorIndex_RefPath tpr p idx) = "(VectorIndex_RefPath " ++ show tpr ++ " " ++ show p ++ " " ++ show (printSymExpr idx) ++ ")"
    show (ArrayIndex_RefPath btpr p idx) = "(ArrayIndex_RefPath " ++ show btpr ++ " " ++ show p ++ " " ++ show (printSymExpr idx) ++ ")"
    show (AgElem_RefPath off sz tpr p) = "(AgElem_RefPath " ++ show (printSymExpr off) ++ " " ++ show sz ++ " " ++ show tpr ++ " " ++ show p ++ ")"

instance IsSymInterface sym => Show (MirReference sym) where
    show (MirReference tpr root path) = "(MirReference " ++ show tpr ++ " " ++ show (refRootType root) ++ " " ++ show root ++ " " ++ show path ++ ")"
    show (MirReference_Integer _) = "(MirReference_Integer _)"

instance IsSymInterface sym => Show (MirReferenceMux sym) where
  show (MirReferenceMux tree) = show tree

instance OrdSkel (MirReference sym) where
    compareSkel = cmpRef
      where
        cmpRef :: MirReference sym -> MirReference sym -> Ordering
        cmpRef (MirReference tpr1 r1 p1) (MirReference tpr2 r2 p2) =
            compareSkelF tpr1 tpr2 <> cmpRoot r1 r2 <> cmpPath p1 p2
        cmpRef (MirReference _ _ _) _ = LT
        cmpRef _ (MirReference _ _ _) = GT
        cmpRef (MirReference_Integer _) (MirReference_Integer _) = EQ

        cmpRoot :: MirReferenceRoot sym tp1 -> MirReferenceRoot sym tp2 -> Ordering
        cmpRoot (RefCell_RefRoot rc1) (RefCell_RefRoot rc2) = compareSkelF rc1 rc2
        cmpRoot (RefCell_RefRoot _) _ = LT
        cmpRoot _ (RefCell_RefRoot _) = GT
        cmpRoot (GlobalVar_RefRoot gv1) (GlobalVar_RefRoot gv2) = compareSkelF gv1 gv2
        cmpRoot (GlobalVar_RefRoot _) _ = LT
        cmpRoot _ (GlobalVar_RefRoot _) = GT
        cmpRoot (Const_RefRoot tpr1 _) (Const_RefRoot tpr2 _) = compareSkelF tpr1 tpr2

        cmpPath :: MirReferencePath sym tp1 tp1' -> MirReferencePath sym tp2 tp2' -> Ordering
        cmpPath Empty_RefPath Empty_RefPath = EQ
        cmpPath Empty_RefPath _ = LT
        cmpPath _ Empty_RefPath = GT
        cmpPath (Field_RefPath ctx1 p1 idx1) (Field_RefPath ctx2 p2 idx2) =
            compareSkelF2 ctx1 idx1 ctx2 idx2 <> cmpPath p1 p2
        cmpPath (Field_RefPath _ _ _) _ = LT
        cmpPath _ (Field_RefPath _ _ _) = GT
        cmpPath (Variant_RefPath _ ctx1 p1 idx1) (Variant_RefPath _ ctx2 p2 idx2) =
            compareSkelF2 ctx1 idx1 ctx2 idx2 <> cmpPath p1 p2
        cmpPath (Variant_RefPath _ _ _ _) _ = LT
        cmpPath _ (Variant_RefPath _ _ _ _) = GT
        cmpPath (Just_RefPath tpr1 p1) (Just_RefPath tpr2 p2) =
            compareSkelF tpr1 tpr2 <> cmpPath p1 p2
        cmpPath (Just_RefPath _ _) _ = LT
        cmpPath _ (Just_RefPath _ _) = GT
        cmpPath (VectorIndex_RefPath tpr1 p1 _) (VectorIndex_RefPath tpr2 p2 _) =
            compareSkelF tpr1 tpr2 <> cmpPath p1 p2
        cmpPath (VectorIndex_RefPath _ _ _) _ = LT
        cmpPath _ (VectorIndex_RefPath _ _ _) = GT
        cmpPath (ArrayIndex_RefPath btpr1 p1 _) (ArrayIndex_RefPath btpr2 p2 _) =
            compareSkelF btpr1 btpr2 <> cmpPath p1 p2
        cmpPath (ArrayIndex_RefPath _ _ _) _ = LT
        cmpPath _ (ArrayIndex_RefPath _ _ _) = GT
        cmpPath (AgElem_RefPath _off1 sz1 tpr1 p1) (AgElem_RefPath _off2 sz2 tpr2 p2) =
            compare sz1 sz2 <> compareSkelF tpr1 tpr2 <> cmpPath p1 p2

refRootType :: MirReferenceRoot sym tp -> TypeRepr tp
refRootType (RefCell_RefRoot r) = refType r
refRootType (GlobalVar_RefRoot r) = globalType r
refRootType (Const_RefRoot tpr _) = tpr

muxRefRoot ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Pred sym ->
  MirReferenceRoot sym tp ->
  MirReferenceRoot sym tp ->
  MaybeT IO (MirReferenceRoot sym tp)
muxRefRoot sym iTypes c root1 root2 = case (root1, root2) of
  (RefCell_RefRoot rc1, RefCell_RefRoot rc2)
    | Just Refl <- testEquality rc1 rc2 -> return root1
  (GlobalVar_RefRoot gv1, GlobalVar_RefRoot gv2)
    | Just Refl <- testEquality gv1 gv2 -> return root1
  (Const_RefRoot tpr v1, Const_RefRoot _tpr v2) -> do
    v' <- lift $ muxRegForType sym iTypes tpr c v1 v2
    return $ Const_RefRoot tpr v'

  (RefCell_RefRoot {}, _) -> mzero
  (GlobalVar_RefRoot {}, _) -> mzero
  (Const_RefRoot {}, _) -> mzero

muxRefPath ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  MirReferencePath sym tp_base tp ->
  MirReferencePath sym tp_base tp ->
  MaybeT IO (MirReferencePath sym tp_base tp)
muxRefPath sym c path1 path2 = case (path1,path2) of
  (Empty_RefPath, Empty_RefPath) -> return Empty_RefPath
  (Field_RefPath ctx1 p1 f1, Field_RefPath ctx2 p2 f2)
    | Just Refl <- testEquality ctx1 ctx2
    , Just Refl <- testEquality f1 f2 ->
         do p' <- muxRefPath sym c p1 p2
            return (Field_RefPath ctx1 p' f1)
  (Variant_RefPath tp1 ctx1 p1 f1, Variant_RefPath tp2 ctx2 p2 f2)
    | Just Refl <- testEquality tp1 tp2
    , Just Refl <- testEquality ctx1 ctx2
    , Just Refl <- testEquality f1 f2 ->
         do p' <- muxRefPath sym c p1 p2
            return (Variant_RefPath tp1 ctx1 p' f1)
  (Just_RefPath tp p1, Just_RefPath _ p2) ->
         do p' <- muxRefPath sym c p1 p2
            return (Just_RefPath tp p')
  (VectorIndex_RefPath tp p1 i1, VectorIndex_RefPath _ p2 i2) ->
         do p' <- muxRefPath sym c p1 p2
            i' <- lift $ bvIte sym c i1 i2
            return (VectorIndex_RefPath tp p' i')
  (ArrayIndex_RefPath btp p1 i1, ArrayIndex_RefPath _ p2 i2) ->
         do p' <- muxRefPath sym c p1 p2
            i' <- lift $ bvIte sym c i1 i2
            return (ArrayIndex_RefPath btp p' i')
  (AgElem_RefPath off1 sz tpr p1, AgElem_RefPath off2 _ _ p2) ->
         do off' <- lift $ bvIte sym c off1 off2
            p' <- muxRefPath sym c p1 p2
            return (AgElem_RefPath off' sz tpr p')

  (Empty_RefPath {}, _) -> mzero
  (Field_RefPath {}, _) -> mzero
  (Variant_RefPath {}, _) -> mzero
  (Just_RefPath {}, _) -> mzero
  (VectorIndex_RefPath {}, _) -> mzero
  (ArrayIndex_RefPath {}, _) -> mzero
  (AgElem_RefPath {}, _) -> mzero

muxRef' :: forall sym.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Pred sym ->
  MirReference sym ->
  MirReference sym ->
  IO (MirReference sym)
muxRef' sym iTypes c (MirReference tpr1 r1 p1) (MirReference tpr2 r2 p2) =
   runMaybeT action >>= \case
     -- Currently, this error occurs when the root types or the leaf/target
     -- types of the two references are unequal.
     Nothing -> fail "Incompatible MIR reference merge"
     Just x  -> return x
  where
  action :: MaybeT IO (MirReference sym)
  action =
    do Refl <- MaybeT (return $ testEquality (refRootType r1) (refRootType r2))
       Refl <- MaybeT (return $ testEquality tpr1 tpr2)
       r' <- muxRefRoot sym iTypes c r1 r2
       p' <- muxRefPath sym c p1 p2
       return (MirReference tpr1 r' p')
muxRef' sym _iTypes c (MirReference_Integer i1) (MirReference_Integer i2) = do
    i' <- bvIte sym c i1 i2
    return $ MirReference_Integer i'
muxRef' _ _ _ _ _ = do
    fail "incompatible MIR reference merge"

muxRef :: forall sym.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Pred sym ->
  MirReferenceMux sym ->
  MirReferenceMux sym ->
  IO (MirReferenceMux sym)
muxRef sym iTypes c (MirReferenceMux mt1) (MirReferenceMux mt2) =
    MirReferenceMux <$> mergeFancyMuxTree sym mux c mt1 mt2
  where mux p a b = liftIO $ muxRef' sym iTypes p a b


--------------------------------------------------------------
-- A MirAggregateType is a collection of elements of any type, with each entry
-- covering a specific range of logical bytes.

-- | A block of memory representing an aggregate value, such as a struct,
-- tuple, or array.  A `MirAggregate` value has a size in bytes and a set of
-- entries.  Each entry covers some range of bytes within the aggregate and
-- associates a `RegValue` with that range.  Entries are nonoverlapping, they
-- never extend past the size of the overall aggregate, and their byte ranges
-- and types are concrete (but their values may be symbolic).
--
-- The set of entries in a `MirAggregate` is not determined by its type (note
-- that `MirAggregate` doesn't take a `CtxRepr` or similar type index).
-- Instead, each `MirAggregate` begins empty, and entries are added to it
-- dynamically.  To keep the implementation simple, new entries are not allowed
-- to partially overlap old ones - they must either be disjoint from all
-- existing entries, or fully overwrite an existing entry.  Read operations
-- must also touch exactly one entry.
data MirAggregate sym where
  MirAggregate ::
    -- | Total size in bytes.  No entry can extend beyond this limit.
    !Word ->
    -- | Maps byte offset to an entry starting at that offset.
    !(IntMap (MirAggregateEntry sym)) ->
    MirAggregate sym

-- | A single entry in a `MirAggregate`.  The start of the covered byte range
-- is not stored here; instead, it's used as the key in the `MirAggregate`'s
-- `IntMap`.  This stores the size of the entry in bytes (which determines the
-- end of the range), the type of value, and a symbolic value of that type.
-- The value is wrapped in `MaybeRepr` / `PartExpr` so that the output of a mux
-- operation on `MirAggregate`s can have entries that are only conditionally
-- initialized.
data MirAggregateEntry sym where
  MirAggregateEntry :: forall sym tp.
    -- | Size in bytes
    !Word ->
    !(TypeRepr tp) ->
    !(RegValue sym (MaybeType tp)) ->
    MirAggregateEntry sym

instance IsSymInterface sym => Show (MirAggregateEntry sym) where
  show (MirAggregateEntry sz tpr _rv) =
    "(MirAggregateEntry " ++ show sz ++ " " ++ show tpr ++ " <regvalue>)"

type MirAggregateSymbol = "MirAggregate"
type MirAggregateType = IntrinsicType MirAggregateSymbol EmptyCtx

pattern MirAggregateRepr :: () => tp' ~ MirAggregateType => TypeRepr tp'
pattern MirAggregateRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MirAggregateSymbol) -> Just Refl) Empty
 where MirAggregateRepr = IntrinsicRepr (knownSymbol @MirAggregateSymbol) Empty

type family MirAggregateFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MirAggregateFam sym EmptyCtx = MirAggregate sym
  MirAggregateFam sym ctx = TypeError
    ('Text "MirAggregateType expects no arguments, but was given" :<>: 'ShowType ctx)

instance IsSymInterface sym => IntrinsicClass sym MirAggregateSymbol where
  type Intrinsic sym MirAggregateSymbol ctx = MirAggregateFam sym ctx

  muxIntrinsic sym tys _nm Empty = muxMirAggregate sym tys
  muxIntrinsic _sym _tys nm ctx = typeError nm ctx

muxMirAggregateEntry :: forall sym.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Word ->
  Pred sym ->
  Maybe (MirAggregateEntry sym) ->
  Maybe (MirAggregateEntry sym) ->
  IO (MirAggregateEntry sym)
muxMirAggregateEntry sym itefns offset c mEntry1 mEntry2 =
  case (mEntry1, mEntry2) of
    (Nothing, Nothing) -> panic "muxMirAggregateEntry" ["requires at least one entry"]
    (Just entry1, Nothing) -> goOneSided c entry1
    (Nothing, Just entry2) -> do
      c' <- notPred sym c
      goOneSided c' entry2
    (Just entry1, Just entry2) -> goTwoSided entry1 entry2
  where
    goOneSided :: Pred sym -> MirAggregateEntry sym -> IO (MirAggregateEntry sym)
    goOneSided activeCond (MirAggregateEntry sz tpr rv) = do
      rv' <- muxRegForType sym itefns (MaybeRepr tpr) activeCond rv Unassigned
      return $ MirAggregateEntry sz tpr rv'

    goTwoSided :: MirAggregateEntry sym -> MirAggregateEntry sym -> IO (MirAggregateEntry sym)
    goTwoSided (MirAggregateEntry sz tpr rv1) (MirAggregateEntry sz' tpr' rv2) = do
      when (sz' /= sz) $
        die $ "entry size " ++ show sz ++ " != " ++ show sz'
      Refl <- case testEquality tpr tpr' of
        Just x -> return x
        Nothing -> die $ "type mismatch: " ++ show tpr ++ " != " ++ show tpr'
      rv' <- muxRegForType sym itefns (MaybeRepr tpr) c rv1 rv2
      return $ MirAggregateEntry sz tpr rv'

    die :: String -> IO a
    die msg = fail $ "bad MirAggregate merge: offset " ++ show offset ++ ": " ++ msg

muxMirAggregate :: forall sym.
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  Pred sym ->
  MirAggregate sym ->
  MirAggregate sym ->
  IO (MirAggregate sym)
muxMirAggregate sym itefns c (MirAggregate sz1 m1) (MirAggregate sz2 m2) = do
  when (sz1 /= sz2) $ do
    fail $ "bad MirAggregate merge: size " ++ show sz1 ++ " != " ++ show sz2
  m' <- sequence $ IntMap.mergeWithKey
    (\offset entry1 entry2 -> Just $ muxEntries offset (Just entry1) (Just entry2))
    (IntMap.mapWithKey $ \offset entry1 -> muxEntries offset (Just entry1) Nothing)
    (IntMap.mapWithKey $ \offset entry2 -> muxEntries offset Nothing (Just entry2))
    m1 m2
  return $ MirAggregate sz1 m'
  where
    muxEntries off e1 e2 = muxMirAggregateEntry sym itefns off' c e1 e2
      where off' = fromIntegral off

-- | Return the @(offset, byteWidth, regValue)@ tuple for each entry whose type
-- is @tpr@. When performing a typed access, these are all the entries that the
-- access could apply to.
--
-- Results are returned in ascending order by offset.
mirAgTypedCandidates ::
  forall sym tp.
  TypeRepr tp ->
  MirAggregate sym ->
  [(Word, Word, RegValue sym (MaybeType tp))]
mirAgTypedCandidates tpr (MirAggregate _ m) =
  Maybe.mapMaybe
    (\(o, MirAggregateEntry byteWidth tpr' rv) ->
      case testEquality tpr tpr' of
        Just Refl -> Just (fromIntegral o, byteWidth, rv)
        Nothing -> Nothing)
    (IntMap.toAscList m)

wordLit :: IsSymInterface sym => sym -> Word -> IO (RegValue sym UsizeType)
wordLit sym o = bvLit sym knownNat (BV.mkBV knownNat (fromIntegral o))

-- | Lift @iteFn@ from type @tp@ to type @MaybeType tp@.
liftIteFnMaybe ::
  forall sym tp.
  IsSymInterface sym =>
  sym ->
  TypeRepr tp ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  Pred sym ->
  RegValue sym (MaybeType tp) ->
  RegValue sym (MaybeType tp) ->
  IO (RegValue sym (MaybeType tp))
liftIteFnMaybe sym _tpr iteFn c x y =
  mergePartial sym (\c' x' y' -> lift $ iteFn c' x' y') c x y

agNoValueAtOffsetSimError :: (Integral a, Show a) => a -> Word -> SimErrorReason
agNoValueAtOffsetSimError off sz =
  ReadBeforeWriteSimError $
    "no value at offset " ++ show off ++ ", in aggregate of size " ++ show sz

agNoValueAtSymbolicOffsetSimError :: Word -> SimErrorReason
agNoValueAtSymbolicOffsetSimError sz =
  ReadBeforeWriteSimError $
    "no value at offset <symbolic>, in aggregate of size " ++ show sz

readMirAggregateWithSymOffset ::
  forall sym bak tp.
  IsSymBackend sym bak =>
  bak ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  RegValue sym UsizeType ->
  TypeRepr tp ->
  MirAggregate sym ->
  MuxLeafT sym IO (RegValue sym tp)
readMirAggregateWithSymOffset bak iteFn off tpr ag@(MirAggregate totalSize m)
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
      case IntMap.lookup off' m of
        Nothing -> leafAbort $ agNoValueAtOffsetSimError off' totalSize
        Just (MirAggregateEntry _ tpr' rv)
          | Just Refl <- testEquality tpr tpr' ->
              leafReadPartExpr bak rv $ agNoValueAtOffsetSimError off' totalSize
          | otherwise -> leafAbort $ GenericSimError $
              "wrong type at offset " ++ show off' ++ ": got " ++ show tpr'
                ++ ", but the requested type is " ++ show tpr

  | otherwise =
      case candidates of
        -- Normally the final "else" branch returns the last candidate.  But if
        -- there are no candidates, we have no element to return, so we have to
        -- special-case it.
        [] -> leafAbort $ GenericSimError $
          -- This error is a bit vague, but since `candidates` only contains
          -- entries that match `tpr`, we don't have a more precise answer.
          "no value or wrong type: the requested type is " ++ show tpr
        (_o0, _w0, rv0) : candidates' -> do
          -- The candidates come from `mirAgTypedCandidates`, which promises to
          -- return elements in ascending order by offset, which satisfies
          -- `offsetInSpan`'s precondition.
          offsetValid <- offsetInSpans sym off (map (\(o, w, _) -> (o, o + w)) candidates)
          leafAssert bak offsetValid $ GenericSimError $
            "no value or wrong type: the requested type is " ++ show tpr
          rv <- liftIO $ foldM
            (\acc (o, _w, rv) -> do
              -- If `off == o`, return `rv`, else `acc`
              offsetEq <- bvEq sym off =<< offsetLit o
              iteFn' offsetEq rv acc)
            rv0 candidates'
          leafReadPartExpr bak rv $ agNoValueAtSymbolicOffsetSimError totalSize

  where
    sym = backendGetSym bak
    candidates = mirAgTypedCandidates tpr ag
    offsetLit = wordLit sym
    iteFn' = liftIteFnMaybe sym tpr iteFn

adjustMirAggregateWithSymOffset ::
  forall sym bak tp.
  (IsSymBackend sym bak) =>
  bak ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  RegValue sym UsizeType ->
  TypeRepr tp ->
  (RegValue sym tp -> MuxLeafT sym IO (RegValue sym tp)) ->
  MirAggregate sym ->
  MuxLeafT sym IO (MirAggregate sym)
adjustMirAggregateWithSymOffset bak iteFn off tpr f ag@(MirAggregate totalSize m)
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
      MirAggregateEntry sz tpr' rvPart <- case IntMap.lookup off' m of
        Just x -> return x
        Nothing -> leafAbort $ agNoValueAtOffsetSimError off' totalSize
      Refl <- case testEquality tpr tpr' of
        Just x -> return x
        Nothing -> leafAbort $ GenericSimError $
          "type mismatch at offset " ++ show off' ++ ": got " ++ show tpr'
            ++ ", but the requested type is " ++ show tpr
      rv <- leafReadPartExpr bak rvPart $ agNoValueAtOffsetSimError off' totalSize
      rv' <- f rv
      let rvPart' = justPartExpr sym rv'
      let entry' = MirAggregateEntry sz tpr rvPart'
      let m' = IntMap.insert off' entry' m
      return $ MirAggregate totalSize m'

  | otherwise = do
      let f' rvPart = do
            rv <- leafReadPartExpr bak rvPart $ agNoValueAtSymbolicOffsetSimError totalSize
            rv' <- f rv
            return $ justPartExpr sym rv'

      xs <- forM candidates $ \(o, _w, rvPart) -> do
        hit <- liftIO $ bvEq sym off =<< offsetLit o
        mRvPart' <- subMuxLeafIO bak (f' rvPart) hit
        rvPart'' <- case mRvPart' of
          Just rvPart' -> liftIO $ iteFn' hit rvPart' rvPart
          Nothing -> return rvPart
        return ((o, rvPart''), hit)

      -- `off` must refer to some existing offset with type `tpr`.  Using
      -- `adjust` to create new entries is not allowed.
      hitAny <- offsetInSpans sym off (map (\(o, w, _) -> (o, o + w)) candidates)
      leafAssert bak hitAny $ GenericSimError $
        "no value or wrong type: the requested type is " ++ show tpr

      let newEntryRvs = IntMap.fromAscList $ map (\((o, rv), _) -> (fromIntegral o, rv)) xs
      let newEntries = IntMap.intersectionWith
            (\(MirAggregateEntry sz tpr' _) rv ->
              case testEquality tpr' tpr of
                Just Refl -> MirAggregateEntry sz tpr rv
                Nothing ->
                  panic "adjustMirAggregateWithSymOffset"
                    ["`candidates`/`xs` should only contain entries of type `tpr`"])
            m newEntryRvs
      let m' = IntMap.union newEntries m
      return $ MirAggregate totalSize m'

  where
    sym = backendGetSym bak
    candidates = mirAgTypedCandidates tpr ag
    offsetLit = wordLit sym
    iteFn' = liftIteFnMaybe sym tpr iteFn


-- | Given a list of valid entry spans @(fromOffset, toOffset)@ in this
-- aggregate, create a predicate that the provided offset appears among their
-- @fromOffset@ values.
--
-- Precondition: the candidate spans are sorted in ascending order by
-- starting offset.
offsetInSpans ::
  forall sym.
  IsSymInterface sym =>
  sym ->
  RegValue sym UsizeType ->
  [(Word, Word)] ->
  MuxLeafT sym IO (SymExpr sym BaseBoolType)
offsetInSpans sym off spans = liftIO $ do
  -- Consider this struct:
  -- ```rs
  -- #[repr(C)]
  -- struct Foo {
  --   a: u16,
  --   b: [u8; 2],
  --   c: u16,
  --   d: [u8; 2],
  --   e: [u16; 3],
  -- }
  -- ```
  --
  -- We have a symbolic offset (`off`) and a concrete type (`tpr`), and need
  -- to determine whether an element of type `tpr` exists at `off` in the
  -- aggregate.
  --
  -- Suppose `tpr` is `u16`, and that the aggregate representing the struct
  -- has been flattened. The type-correct offsets of `u16`s are those of `a`
  -- (0), `c` (4), and each element of `e` (8, 10, and 12).
  --
  -- We start by partitioning these offsets into contiguous `runs` (of which
  -- there is one, from 8 to 14, exclusive of 14) and discrete `offsets` (of
  -- which there are two, 0 and 4).
  let (offsets, runs) = foldRuns spans

  -- For `offsets`, we construct a simplistic predicate: for each offset, is
  -- `off` equal to it? For our example, this will yield the predicate
  -- (`off` == 0 || `off` == 4).
  offsetsPred <- orPredBy (\o -> bvEq sym off =<< wordLit sym o) offsets

  -- For `runs`, we construct a more efficient predicate: for each run, is
  -- `off` within the bounds of the run, and does the stride (i.e. the width
  -- of a single `u16`) evenly divide it? For our example, this will yield
  -- the predicate (`off` >= 8 && `off` < 14 && `off` % 2 == 0). See
  -- `runPred`, below.
  runsPred <- orPredBy runPred runs

  -- If either predicate holds, the offset is a valid index into this
  -- aggregate.
  orPred sym runsPred offsetsPred
  where
    orPredBy :: (a -> IO (Pred sym)) -> [a] -> IO (Pred sym)
    orPredBy f xs = do
      xsPreds <- mapM f xs
      foldM (orPred sym) (falsePred sym) xsPreds

    -- Whether `off` appears in the given `Run` of aggregate elements.
    runPred :: Run -> IO (Pred sym)
    runPred run = do
      -- Note that we're able to use the unique stride as a proxy for element
      -- type width, since the widths of `Run` elements are exactly those of the
      -- original aggregate entry widths.
      let tyWidth = rStride run

      -- off >= rFrom
      afterBeginning <- bvUge sym off =<< wordLit sym (rFrom run)

      -- off < rTo (not `<=` because `rTo` is exclusive)
      beforeEnd <- bvUlt sym off =<< wordLit sym (rTo run)

      inBounds <- andPred sym afterBeginning beforeEnd

      -- (off - rFrom) `mod` tyWidth == 0
      relativeOff <- bvSub sym off =<< wordLit sym (rFrom run)
      offModWidth <- bvUrem sym relativeOff =<< wordLit sym tyWidth
      atTyBoundary <- bvEq sym offModWidth =<< wordLit sym 0

      andPred sym inBounds atTyBoundary

-- | Given a sorted list of element "spans", represented as @(fromOffset,
-- toOffset)@ pairs (where an element's bytes occupy all offsets in the
-- half-open range @[fromOffset, toOffset)@), find and return all contiguous
-- sequences of two or more elements of the same width and the @fromOffset@s all
-- other elements.
--
-- For example, @foldRuns [(0, 2), (4, 8), (8, 10), (10, 12), (12, 14)]@
-- should yield @([0, 4], [Run {rFrom = 8, rTo = 14, rStride = 2}])@. The
-- last three spans are adjacent to one another and are the same width, so
-- they are folded into a `Run` (to 14, exclusive of 14). The first two
-- spans are not contiguous, so they are returned as discrete offsets.
foldRuns :: [(Word, Word)] -> ([Word], [Run])
foldRuns spans =
  let (offsets, runs) = foldRuns' [] [] spans
    in (reverse offsets, reverse runs)
  where
    foldRuns' :: [Word] -> [Run] -> [(Word, Word)] -> ([Word], [Run])
    foldRuns' offsets runs spans_ =
      case (runs, spans_) of
        -- Done
        (_, []) ->
          (offsets, runs)
        -- Add to an existing run
        (r : rs, s : ss)
          | Just r' <- addToRun r s ->
              foldRuns' offsets (r' : rs) ss
        -- Add a new run
        (_, s1 : s2 : ss)
          | Just r <- mkRun s1 s2 ->
              foldRuns' offsets (r : runs) ss
        -- Add a new offset
        (_, (sFrom, _) : ss) ->
          foldRuns' (sFrom : offsets) runs ss

-- | Attempt to add the given span to the end of the given run.
addToRun :: Run -> (Word, Word) -> Maybe Run
addToRun run (sFrom, sTo)
  | rTo run == sFrom,
    rStride run == sTo - sFrom =
      Just (Run (rFrom run) sTo (rStride run))
  | otherwise =
      Nothing

-- | Attempt to make a new run from two spans, yielding a run if they are the
-- same width and are adjacent.
mkRun :: (Word, Word) -> (Word, Word) -> Maybe Run
mkRun (s1From, s1To) s2 =
  addToRun (Run s1From s1To (s1To - s1From)) s2

-- | Represents a contiguous "run" of aggregate elements of the same width.
data Run = Run
  { -- | Starting at (and inclusive of) this position
    rFrom :: !Word,
    -- | Ending at (and exclusive of) this position
    rTo :: !Word,
    -- | The spacing between the elements in this run
    rStride :: !Word
  }
  deriving (Show)


mirAggregate_entries :: sym -> MirAggregate sym -> [(Word, MirAggregateEntry sym)]
mirAggregate_entries _sym (MirAggregate _totalSize m) =
  [(fromIntegral off, entry) | (off, entry) <- IntMap.toList m]

mirAggregate_insert ::
  Word ->
  MirAggregateEntry sym ->
  MirAggregate sym ->
  Either String (MirAggregate sym)
mirAggregate_insert off entry@(MirAggregateEntry sz tpr _) (MirAggregate totalSize m) = do
  -- For now, we require that either there are no entries overlapping the byte
  -- range `off .. off + sz`, or there is an entry covering exactly that range
  -- whose type matches `tpr`.  In the future we could relax this by deleting
  -- existing entries that are fully covered by the new one (though this could
  -- cause trouble when the old and new `MirAggregate` get muxed together).
  case IntMap.lookupLT (fromIntegral $ off + sz) m of
    Nothing -> return ()
    Just (fromIntegral -> off', MirAggregateEntry sz' tpr' _)
      | off' == off -> do
          case testEquality tpr tpr' of
            Nothing -> die $ "type mismatch at offset " ++ show off ++ ": "
              ++ show tpr ++ " != " ++ show tpr'
            Just _ -> return ()
          when (sz /= sz') $
            die $ "size mismatch at offset " ++ show off ++ ": "
              ++ show sz ++ " != " ++ show sz'
      -- Existing entry's range comes entirely before the new one, so there is
      -- no overlap.
      | off' + sz' <= off -> return ()
      | otherwise -> die $ "partial overlap: " ++ show off ++ ".." ++ show (off + sz)
          ++ " vs " ++ show off' ++ ".." ++ show (off' + sz')
  -- New entry must not extend past `0 .. totalSize`.
  when (off + sz > totalSize) $
    die $ "entry out of range: covers " ++ show off ++ ".." ++ show (off + sz)
      ++ ", but total size is " ++ show totalSize
  -- All checks passed - insert the new entry
  return $ MirAggregate totalSize $ IntMap.insert (fromIntegral off) entry m
  where
    die msg = Left $ "bad MirAggregate insert: " ++ msg

writeMirAggregateWithSymOffset ::
  forall sym bak tp.
  (IsSymBackend sym bak) =>
  bak ->
  (Pred sym -> RegValue sym tp -> RegValue sym tp -> IO (RegValue sym tp)) ->
  RegValue sym UsizeType ->
  Word ->
  TypeRepr tp ->
  RegValue sym tp ->
  MirAggregate sym ->
  MuxLeafT sym IO (MirAggregate sym)
writeMirAggregateWithSymOffset bak iteFn off sz tpr val ag
  -- Concrete case: insert a new entry or overwrite an existing one with
  -- `mirAggregate_insert`.
  | Just (fromIntegral . BV.asUnsigned -> off') <- asBV off = do
      let entry = MirAggregateEntry sz tpr $ justPartExpr sym val
      case mirAggregate_insert off' entry ag of
        Left err -> leafAbort $ GenericSimError err
        Right ag' -> return ag'

  -- Symbolic case: overwrite an existing entry with `adjustMirAggregateWithSymOffset`.
  -- Creating a new entry at a symbolic offset is not allowed.
  | otherwise = do
      adjustMirAggregateWithSymOffset bak iteFn off tpr (\_oldVal -> return val) ag

  where
    sym = backendGetSym bak

-- | Look up a value in a `MirAggregate`.  This returns @Right maybeVal@ if it
-- finds a value at the requested offset, @Right Unassigned@ if the offset is
-- valid but there's no entry there, and @Left errorMessage@ if offset is
-- invalid (in the middle of some entry) or the type @tpr@ is incorrect.
mirAggregate_lookup ::
  Word ->
  TypeRepr tp ->
  MirAggregate sym ->
  Either String (RegValue sym (MaybeType tp))
mirAggregate_lookup off tpr (MirAggregate totalSize m) = do
  case IntMap.lookupLE (fromIntegral off) m of
    _ | off >= totalSize ->
      die $ "offset " ++ show off ++ " is out of range "
        ++ "for aggregate total size " ++ show totalSize
    Nothing -> Right Unassigned
    Just (fromIntegral -> off', MirAggregateEntry sz' tpr' rv)
      | off' == off -> do
          case testEquality tpr tpr' of
            Nothing -> die $ "type mismatch at offset " ++ show off ++ ": "
              ++ show tpr ++ " != " ++ show tpr'
            Just Refl -> Right rv
      -- Existing entry's range comes entirely before the new one, so there is
      -- no overlap (and no value at `off`).
      | off' + sz' <= off -> Right Unassigned
      | otherwise -> die $ "partial overlap: " ++ show off
          ++ " vs " ++ show off' ++ ".." ++ show (off' + sz')
  where
    die msg = Left $ "bad MirAggregate lookup: " ++ msg

-- | Resize a `MirAggregate`.  If the new size is larger, the extra space will
-- be left uninitialized.  If the new size is smaller, any entries that extend
-- past the new end point will be discarded.
resizeMirAggregate ::
  MirAggregate sym ->
  Word ->
  MirAggregate sym
resizeMirAggregate (MirAggregate totalSize m) newSize
  | newSize >= totalSize = MirAggregate newSize m
  | otherwise = MirAggregate newSize m'
  where
    m' = IntMap.filterWithKey
      (\off (MirAggregateEntry sz _ _) -> fromIntegral off + sz <= newSize)
      m


--------------------------------------------------------------

-- Aliases for working with the custom Array type, which is backed by an SMT
-- array at the Crucible level.
type UsizeArrayType btp = SymbolicArrayType (EmptyCtx ::> BaseUsizeType) btp
pattern UsizeArrayRepr :: () => tp' ~ UsizeArrayType btp => BaseTypeRepr btp -> TypeRepr tp'
pattern UsizeArrayRepr btp <-
    SymbolicArrayRepr (testEquality (Empty :> BaseUsizeRepr) -> Just Refl) btp
  where UsizeArrayRepr btp = SymbolicArrayRepr (Empty :> BaseUsizeRepr) btp


leafIndexVectorWithSymIndex ::
    (IsSymBackend sym bak) =>
    bak ->
    (Pred sym -> a -> a -> IO a) ->
    V.Vector a ->
    RegValue sym UsizeType ->
    MuxLeafT sym IO a
leafIndexVectorWithSymIndex bak iteFn v i
  | Just i' <- asBV i = case v V.!? fromIntegral (BV.asUnsigned i') of
        Just x -> return x
        Nothing -> leafAbort $ GenericSimError $
            "vector index out of range: the length is " ++ show (V.length v) ++
                " but the index is " ++ show i'
  -- Normally the final "else" branch returns the last element.  But the empty
  -- vector has no last element to return, so we have to special-case it.
  | V.null v = leafAbort $ GenericSimError $
        "vector index out of range: the length is " ++ show (V.length v)
  | otherwise = do
        let sym = backendGetSym bak
        inRange <- liftIO $ bvUlt sym i =<< bvLit sym knownNat (BV.mkBV knownNat (fromIntegral $ V.length v))
        leafAssert bak inRange $ GenericSimError $
            "vector index out of range: the length is " ++ show (V.length v)
        liftIO $ muxRange
            (\j -> bvEq sym i =<< bvLit sym knownNat (BV.mkBV knownNat (fromIntegral j)))
            iteFn
            (\j -> return $ v V.! fromIntegral j)
            0 (fromIntegral $ V.length v - 1)

leafAdjustVectorWithSymIndex ::
    forall sym bak a. (IsSymBackend sym bak) =>
    bak ->
    (Pred sym -> a -> a -> IO a) ->
    V.Vector a ->
    RegValue sym UsizeType ->
    (a -> MuxLeafT sym IO a) ->
    MuxLeafT sym IO (V.Vector a)
leafAdjustVectorWithSymIndex bak iteFn v i adj
  | Just (fromIntegral . BV.asUnsigned -> i') <- asBV i =
    if i' < V.length v then do
        x' <- adj $ v V.! i'
        return $ v V.// [(i', x')]
    else
        leafAbort $ GenericSimError $
            "vector index out of range: the length is " ++ show (V.length v) ++
                " but the index is " ++ show i'
  | otherwise = do
        inRange <- liftIO $ bvUlt sym i =<< bvLit sym knownNat (BV.mkBV knownNat (fromIntegral $ V.length v))
        leafAssert bak inRange $ GenericSimError $
            "vector index out of range: the length is " ++ show (V.length v)
        V.generateM (V.length v) go
  where
    sym = backendGetSym bak

    go :: Int -> MuxLeafT sym IO a
    go j = do
        hit <- liftIO $ bvEq sym i =<< bvLit sym knownNat (BV.mkBV knownNat (fromIntegral j))
        let x = v V.! j
        -- NB: With this design, any assert generated by `adj` will be
        -- replicated `N` times, in the form `assert (i == j -> p)`.  Currently
        -- this seems okay because the number of asserts will be linear, except
        -- in the case of nested arrays, which are uncommon.
        mx' <- subMuxLeafIO bak (adj x) hit
        case mx' of
            Just x' -> liftIO $ iteFn hit x' x
            Nothing -> return x



-- | Sigil type indicating the MIR syntax extension
data MIR
type instance ExprExtension MIR = EmptyExprExtension
type instance StmtExtension MIR = MirStmt

-- | The 'MirReferenceType' is the data pointer - either an immutable or mutable
-- reference. The 'AnyType' is the vtable.
type DynRefType = StructType (EmptyCtx ::> MirReferenceType ::> AnyType)

dynRefDataIndex :: Index (EmptyCtx ::> MirReferenceType ::> AnyType) MirReferenceType
dynRefDataIndex = skipIndex baseIndex

dynRefVtableIndex :: Index (EmptyCtx ::> MirReferenceType ::> AnyType) AnyType
dynRefVtableIndex = lastIndex (incSize $ incSize zeroSize)


data MirStmt :: (CrucibleType -> Type) -> CrucibleType -> Type where
  MirNewRef ::
     !(TypeRepr tp) ->
     MirStmt f MirReferenceType
  MirIntegerToRef ::
     !(f UsizeType) ->
     MirStmt f MirReferenceType
  MirGlobalRef ::
     !(GlobalVar tp) ->
     MirStmt f MirReferenceType
  MirConstRef ::
     !(TypeRepr tp) ->
     !(f tp) ->
     MirStmt f MirReferenceType
  MirReadRef ::
     !(TypeRepr tp) ->
     !(f MirReferenceType) ->
     MirStmt f tp
  MirWriteRef ::
     !(TypeRepr tp) ->
     !(f MirReferenceType) ->
     !(f tp) ->
     MirStmt f UnitType
  MirDropRef ::
     !(f MirReferenceType) ->
     MirStmt f UnitType
  MirSubfieldRef ::
     !(CtxRepr ctx) ->
     !(f MirReferenceType) ->
     !(Index ctx tp) ->
     MirStmt f MirReferenceType
  -- | Like `MirSubfieldRef`, but for fields with statically-unknown types, such
  -- as trait objects. The `Int` is the index of the field, and the `TypeRepr`
  -- is an optional type hint, if the expected type happens to be known and
  -- representable. If provided, it will be dynamically checked at simulation
  -- time.
  MirSubfieldRef_Untyped ::
     !(f MirReferenceType) ->
     !Int ->
     !(Maybe (Some TypeRepr)) ->
     MirStmt f MirReferenceType
  MirSubvariantRef ::
     !(TypeRepr discrTp) ->
     !(CtxRepr variantsCtx) ->
     !(f MirReferenceType) ->
     !(Index variantsCtx tp) ->
     MirStmt f MirReferenceType
  MirSubindexRef ::
     !(TypeRepr tp) ->
     !(f MirReferenceType) ->
     !(f UsizeType) ->
     -- | Size of the element, in bytes
     !Word ->
     MirStmt f MirReferenceType
  MirSubjustRef ::
     !(TypeRepr tp) ->
     !(f MirReferenceType) ->
     MirStmt f MirReferenceType
  MirRef_AgElem ::
     !(f UsizeType) ->
     !Word ->
     !(TypeRepr tp) ->
     !(f MirReferenceType) ->
     MirStmt f MirReferenceType
  MirRef_Eq ::
     !(f MirReferenceType) ->
     !(f MirReferenceType) ->
     MirStmt f BoolType
  -- Rust `ptr::offset`.  Steps by `count` units of `size_of::<T>`.  Arithmetic
  -- must not overflow and the resulting pointer must be in bounds.
  MirRef_Offset ::
     !(f MirReferenceType) ->
     !(f IsizeType) ->
     MirStmt f MirReferenceType
  -- Rust `ptr::wrapping_offset`.  Steps by `count` units of `size_of::<T>`,
  -- with no additional restrictions.
  MirRef_OffsetWrap ::
     !(f MirReferenceType) ->
     !(f IsizeType) ->
     MirStmt f MirReferenceType
  -- | Try to subtract two references, as in `pointer::offset_from`.  If both
  -- point into the same array, return their difference; otherwise, return
  -- Nothing.  The `Nothing` result is useful for overlap checks: slices from
  -- different arrays cannot overlap.
  MirRef_TryOffsetFrom ::
     !(f MirReferenceType) ->
     !(f MirReferenceType) ->
     MirStmt f (MaybeType IsizeType)
  -- | Peel off an outermost `Index_RefPath`.  Given a pointer to an element of
  -- a vector, this produces a pointer to the parent vector and the index of
  -- the element.  If the outermost path segment isn't `Index_RefPath`, this
  -- operation raises an error.
  MirRef_PeelIndex ::
     !(f MirReferenceType) ->
     MirStmt f (StructType (EmptyCtx ::> MirReferenceType ::> UsizeType))
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
  -- | Create an empty `MirAggregate`, where the size is given as an expression
  -- of `UsizeType`.  The size must still be a concrete expression at symbolic
  -- execution time.
  MirAggregate_Uninit ::
    !(f UsizeType) ->
    MirStmt f MirAggregateType
  -- | Create a `MirAggregate` by replicating a value @len@ times.  The total
  -- size in bytes is @elemSz * len@.  The array stride is set equal to the
  -- element size.
  MirAggregate_Replicate ::
    !Word ->
    !(TypeRepr tp) ->
    !(f tp) ->
    !(f UsizeType) ->
    MirStmt f MirAggregateType
  -- | Resize a `MirAggregate`.  As with `MirAggregate_Uninit`, the `UsizeType`
  -- expression must be concrete.
  MirAggregate_Resize ::
    !(f MirAggregateType) ->
    !(f UsizeType) ->
    MirStmt f MirAggregateType
  MirAggregate_Get ::
    -- | Offset
    !Word ->
    -- | Size
    !Word ->
    !(TypeRepr tp) ->
    !(f MirAggregateType) ->
    MirStmt f tp
  MirAggregate_Set ::
    -- | Offset
    !Word ->
    -- | Size
    !Word ->
    !(TypeRepr tp) ->
    !(f tp) ->
    !(f MirAggregateType) ->
    MirStmt f MirAggregateType

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
    MirNewRef _    -> MirReferenceRepr
    MirIntegerToRef _ -> MirReferenceRepr
    MirGlobalRef _ -> MirReferenceRepr
    MirConstRef _ _ -> MirReferenceRepr
    MirReadRef tp _ -> tp
    MirWriteRef _ _ _ -> UnitRepr
    MirDropRef _    -> UnitRepr
    MirSubfieldRef _ _ _ -> MirReferenceRepr
    MirSubfieldRef_Untyped _ _ _ -> MirReferenceRepr
    MirSubvariantRef _ _ _ _ -> MirReferenceRepr
    MirSubindexRef _ _ _ _ -> MirReferenceRepr
    MirSubjustRef _ _ -> MirReferenceRepr
    MirRef_AgElem _ _ _ _ -> MirReferenceRepr
    MirRef_Eq _ _ -> BoolRepr
    MirRef_Offset _ _ -> MirReferenceRepr
    MirRef_OffsetWrap _ _ -> MirReferenceRepr
    MirRef_TryOffsetFrom _ _ -> MaybeRepr IsizeRepr
    MirRef_PeelIndex _ -> StructRepr (Empty :> MirReferenceRepr :> UsizeRepr)
    VectorSnoc tp _ _ -> VectorRepr tp
    VectorHead tp _ -> MaybeRepr tp
    VectorTail tp _ -> VectorRepr tp
    VectorInit tp _ -> VectorRepr tp
    VectorLast tp _ -> MaybeRepr tp
    VectorConcat tp _ _ -> VectorRepr tp
    VectorTake tp _ _ -> VectorRepr tp
    VectorDrop tp _ _ -> VectorRepr tp
    ArrayZeroed idxs w -> SymbolicArrayRepr idxs (BaseBVRepr w)
    MirAggregate_Uninit _ -> MirAggregateRepr
    MirAggregate_Replicate _ _ _ _ -> MirAggregateRepr
    MirAggregate_Resize _ _ -> MirAggregateRepr
    MirAggregate_Get _ _ tp _ -> tp
    MirAggregate_Set _ _ _ _ _ -> MirAggregateRepr

instance PrettyApp MirStmt where
  ppApp pp = \case
    MirNewRef tp -> "newMirRef" <+> pretty tp
    MirIntegerToRef i -> "integerToMirRef" <+> pp i
    MirGlobalRef gv -> "globalMirRef" <+> pretty gv
    MirConstRef _ v -> "constMirRef" <+> pp v
    MirReadRef _ x  -> "readMirRef" <+> pp x
    MirWriteRef _ x y -> "writeMirRef" <+> pp x <+> "<-" <+> pp y
    MirDropRef x    -> "dropMirRef" <+> pp x
    MirSubfieldRef _ x idx -> "subfieldRef" <+> pp x <+> viaShow idx
    MirSubfieldRef_Untyped x fieldNum expectedTy -> "subfieldRef_Untyped" <+> pp x <+> viaShow fieldNum <+> viaShow expectedTy
    MirSubvariantRef _ _ x idx -> "subvariantRef" <+> pp x <+> viaShow idx
    MirSubindexRef _ x idx sz -> "subindexRef" <+> pp x <+> pp idx <+> viaShow sz
    MirSubjustRef _ x -> "subjustRef" <+> pp x
    MirRef_AgElem off _ _ ref -> "mirRef_agElem" <+> pp off <+> pp ref
    MirRef_Eq x y -> "mirRef_eq" <+> pp x <+> pp y
    MirRef_Offset p o -> "mirRef_offset" <+> pp p <+> pp o
    MirRef_OffsetWrap p o -> "mirRef_offsetWrap" <+> pp p <+> pp o
    MirRef_TryOffsetFrom p o -> "mirRef_tryOffsetFrom" <+> pp p <+> pp o
    MirRef_PeelIndex p -> "mirRef_peelIndex" <+> pp p
    VectorSnoc _ v e -> "vectorSnoc" <+> pp v <+> pp e
    VectorHead _ v -> "vectorHead" <+> pp v
    VectorTail _ v -> "vectorTail" <+> pp v
    VectorInit _ v -> "vectorInit" <+> pp v
    VectorLast _ v -> "vectorLast" <+> pp v
    VectorConcat _ v1 v2 -> "vectorConcat" <+> pp v1 <+> pp v2
    VectorTake _ v i -> "vectorTake" <+> pp v <+> pp i
    VectorDrop _ v i -> "vectorDrop" <+> pp v <+> pp i
    ArrayZeroed idxs w -> "arrayZeroed" <+> viaShow idxs <+> viaShow w
    MirAggregate_Uninit sz -> "mirAggregate_uninit" <+> pp sz
    MirAggregate_Replicate elemSz _ elemVal lenSym -> "mirAggregate_replicate" <+> viaShow elemSz <+> pp elemVal <+> pp lenSym
    MirAggregate_Resize ag szSym -> "mirAggregate_resize" <+> pp ag <+> pp szSym
    MirAggregate_Get off sz _ ag -> "mirAggregate_get" <+> viaShow off <+> viaShow sz <+> pp ag
    MirAggregate_Set off sz _ rv ag -> "mirAggregate_set" <+> viaShow off <+> viaShow sz <+> pp rv <+> pp ag


instance FunctorFC MirStmt where
  fmapFC = fmapFCDefault
instance FoldableFC MirStmt where
  foldMapFC = foldMapFCDefault
instance TraversableFC MirStmt where
  traverseFC = traverseMirStmt


instance IsSyntaxExtension MIR

readBeforeWriteMsg :: SimErrorReason
readBeforeWriteMsg = ReadBeforeWriteSimError
    "Attempted to read uninitialized reference cell"

newConstMirRef :: IsSymInterface sym =>
    sym ->
    TypeRepr tp ->
    RegValue sym tp ->
    MirReferenceMux sym
newConstMirRef sym tpr v = MirReferenceMux $ toFancyMuxTree sym $
    MirReference tpr (Const_RefRoot tpr v) Empty_RefPath

readRefRoot :: (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    MirReferenceRoot sym tp ->
    MuxLeafT sym IO (RegValue sym tp)
readRefRoot bak gs (RefCell_RefRoot rc) =
    leafReadPartExpr bak (lookupRef rc gs) readBeforeWriteMsg
readRefRoot _bak gs (GlobalVar_RefRoot gv) =
    case lookupGlobal gv gs of
        Just x -> return x
        Nothing -> leafAbort readBeforeWriteMsg
readRefRoot _ _ (Const_RefRoot _ v) = return v

writeRefRoot :: forall sym bak tp.
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    MirReferenceRoot sym tp ->
    RegValue sym tp ->
    MuxLeafT sym IO (SymGlobalState sym)
writeRefRoot bak gs iTypes (RefCell_RefRoot rc) v = do
    let sym = backendGetSym bak
    let tpr = refType rc
    let f p a b = liftIO $ muxRegForType sym iTypes tpr p a b
    let oldv = lookupRef rc gs
    newv <- leafUpdatePartExpr bak f v oldv
    return $ updateRef rc newv gs
writeRefRoot bak gs iTypes (GlobalVar_RefRoot gv) v = do
    let sym = backendGetSym bak
    let tpr = globalType gv
    p <- leafPredicate
    newv <- case lookupGlobal gv gs of
        _ | Just True <- asConstantPred p -> return v
        Just oldv -> liftIO $ muxRegForType sym iTypes tpr p v oldv
        -- GlobalVars can't be conditionally initialized.
        Nothing -> leafAbort $ ReadBeforeWriteSimError $
            "attempted conditional write to uninitialized global " ++
                show gv ++ " of type " ++ show tpr
    return $ insertGlobal gv newv gs
writeRefRoot _bak _gs _iTypes (Const_RefRoot tpr _) _ =
    leafAbort $ GenericSimError $
        "Cannot write to Const_RefRoot (of type " ++ show tpr ++ ")"

dropRefRoot ::
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    MirReferenceRoot sym tp ->
    MuxLeafT sym IO (SymGlobalState sym)
dropRefRoot bak gs (RefCell_RefRoot rc) = do
    let oldv = lookupRef rc gs
    newv <- leafClearPartExpr bak oldv
    return $ updateRef rc newv gs
dropRefRoot _bak _gs (GlobalVar_RefRoot gv) =
    leafAbort $ GenericSimError $
        "Cannot drop global variable " ++ show gv
dropRefRoot _bak _gs (Const_RefRoot tpr _) =
    leafAbort $ GenericSimError $
        "Cannot drop Const_RefRoot (of type " ++ show tpr ++ ")"

-- | Helper for defining a `MuxLeafT` operation that works only for
-- `MirReference`s with a specific pointee type `tp`.  If the `MirReference`
-- argument is a valid reference (not `MirReference_Integer`) with pointee type
-- `tp`, this calls `k` on the reference's parts; otherwise, this fails.
-- `desc` is a human-readable description of the operation, which is used in
-- the `leafAbort` error message.
typedLeafOp ::
    Monad m =>
    String ->
    TypeRepr tp ->
    MirReference sym ->
    (forall tp0. MirReferenceRoot sym tp0 -> MirReferencePath sym tp0 tp -> MuxLeafT sym m a) ->
    MuxLeafT sym m a
typedLeafOp desc expectTpr (MirReference tpr root path) k
  | Just Refl <- testEquality tpr expectTpr = k root path
  | otherwise = leafAbort $ GenericSimError $
      desc ++ " requires a reference to " ++ show expectTpr
        ++ ", but got a reference to " ++ show tpr
typedLeafOp desc _ (MirReference_Integer _) _ =
    leafAbort $ GenericSimError $
        "attempted " ++ desc ++ " on the result of an integer-to-pointer cast"

readMirRefLeaf ::
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym tp)
readMirRefLeaf bak gs iTypes tpr ref =
  typedLeafOp "read" tpr ref $ \root path -> do
    v <- readRefRoot bak gs root
    v' <- readRefPath bak iTypes v path
    return v'

writeMirRefLeaf ::
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReference sym ->
    RegValue sym tp ->
    MuxLeafT sym IO (SymGlobalState sym)
writeMirRefLeaf bak gs iTypes tpr ref val =
  typedLeafOp "write" tpr ref $ \root path ->
    case path of
      Empty_RefPath -> writeRefRoot bak gs iTypes root val
      _ -> do
        x <- readRefRoot bak gs root
        x' <- writeRefPath bak iTypes x path val
        writeRefRoot bak gs iTypes root x'

dropMirRefLeaf ::
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    MirReference sym ->
    MuxLeafT sym IO (SymGlobalState sym)
dropMirRefLeaf bak gs (MirReference _ root Empty_RefPath) = dropRefRoot bak gs root
dropMirRefLeaf _bak _gs (MirReference _ _ _) =
    leafAbort $ GenericSimError $
      "attempted to drop an interior reference (non-empty ref path)"
dropMirRefLeaf _bak _gs (MirReference_Integer _) =
    leafAbort $ GenericSimError $
      "attempted to drop the result of an integer-to-pointer cast"

dropMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    SymGlobalState sym ->
    MirReferenceMux sym ->
    IO (SymGlobalState sym)
dropMirRefIO bak gs (MirReferenceMux ref) =
    foldFancyMuxTree bak (dropMirRefLeaf bak) gs ref

subfieldMirRefLeaf ::
    CtxRepr ctx ->
    MirReference sym ->
    Index ctx tp ->
    MuxLeafT sym IO (MirReference sym)
subfieldMirRefLeaf ctx ref idx =
  typedLeafOp "subfield" (StructRepr ctx) ref $ \root path -> do
    let tpr = ctx ! idx
    return $ MirReference tpr root (Field_RefPath ctx path idx)

-- | Mimic `subfieldMirRefLeaf`, but infer the appropriate `CtxRepr` and `Index`
-- at simulation time. If @expectedTy@ is provided, this will assert that it
-- matches the actual type of the field during simulation.
subfieldMirRef_UntypedLeaf ::
    MirReference sym ->
    Int ->
    Maybe (Some TypeRepr) ->
    MuxLeafT sym IO (MirReference sym)
subfieldMirRef_UntypedLeaf ref fieldNum expectedTy =
  case ref of
    MirReference_Integer _ ->
      bail $ "attempted untyped subfield on the result of an integer-to-pointer cast"
    MirReference structReprHopefully refRoot refPath ->
      case structReprHopefully of
        StructRepr structCtx ->
          do
            Some fieldIdx <-
              case Ctx.intIndex fieldNum (Ctx.size structCtx) of
                Just someIdx -> pure someIdx
                Nothing ->
                  bail $ unwords $
                    [ "out-of-bounds field access:"
                    , "field", show fieldNum, "of struct", show structCtx ]
            let fieldRepr = structCtx ! fieldIdx
            () <- case expectedTy of
              Nothing -> pure ()
              Just (Some expected) ->
                case testEquality expected fieldRepr of
                  Just Refl -> pure ()
                  Nothing ->
                    bail $ unwords $
                      [ "expected field type", show expected
                      , "did not match actual field type", show fieldRepr ]
            let fieldPath = Field_RefPath structCtx refPath fieldIdx
            pure $ MirReference fieldRepr refRoot fieldPath
        notAStruct ->
          bail $ unwords $
            [ "untyped subfield requires a reference to a struct, but got a reference to"
            , show notAStruct ]
  where
    bail msg = leafAbort $ GenericSimError $ msg

subfieldMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    CtxRepr ctx ->
    MirReferenceMux sym ->
    Index ctx tp ->
    IO (MirReferenceMux sym)
subfieldMirRefIO bak iTypes ctx ref idx =
    modifyRefMuxIO bak iTypes (\ref' -> subfieldMirRefLeaf ctx ref' idx) ref

subfieldMirRef_UntypedIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    Int ->
    Maybe (Some TypeRepr) ->
    IO (MirReferenceMux sym)
subfieldMirRef_UntypedIO bak iTypes ref fieldNum expectedTy =
    modifyRefMuxIO bak iTypes (\ref' -> subfieldMirRef_UntypedLeaf ref' fieldNum expectedTy) ref

subvariantMirRefLeaf ::
    TypeRepr discrTp ->
    CtxRepr variantsCtx ->
    MirReference sym ->
    Index variantsCtx tp ->
    MuxLeafT sym IO (MirReference sym)
subvariantMirRefLeaf discrTpr ctx ref idx =
  typedLeafOp "subvariant" (RustEnumRepr discrTpr ctx) ref $ \root path -> do
    let tpr = ctx ! idx
    return $ MirReference tpr root (Variant_RefPath discrTpr ctx path idx)

subvariantMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    TypeRepr discrTp ->
    CtxRepr variantsCtx ->
    MirReferenceMux sym ->
    Index variantsCtx tp ->
    IO (MirReferenceMux sym)
subvariantMirRefIO bak iTypes tp ctx ref idx =
    modifyRefMuxIO bak iTypes (\ref' -> subvariantMirRefLeaf tp ctx ref' idx) ref

subindexMirRefLeaf ::
    IsSymInterface sym =>
    sym ->
    TypeRepr tp ->
    MirReference sym ->
    RegValue sym UsizeType ->
    -- | Size of the element, in bytes
    Word ->
    MuxLeafT sym IO (MirReference sym)
subindexMirRefLeaf _sym elemTpr (MirReference tpr root path) idx _elemSize
  | Just Refl <- testEquality tpr (VectorRepr elemTpr) =
      return $ MirReference elemTpr root (VectorIndex_RefPath elemTpr path idx)
  | AsBaseType btpr <- asBaseType elemTpr,
    Just Refl <- testEquality tpr (UsizeArrayRepr btpr) =
      return $ MirReference elemTpr root (ArrayIndex_RefPath btpr path idx)
  | Just Refl <- testEquality tpr MirAggregateRepr =
      let sz = 1 in -- TODO: hardcoded size=1
      return $ MirReference elemTpr root (AgElem_RefPath idx sz elemTpr path)
  | otherwise = leafAbort $ GenericSimError $
      "subindex requires a reference to a VectorRepr, a UsizeArrayRepr of " ++
      "a Crucible base type, or a MirAggregateRepr, but got a reference to " ++
      show tpr
subindexMirRefLeaf _sym _elemTpr (MirReference_Integer {}) _idx _elemSize =
    leafAbort $ GenericSimError $
        "attempted subindex on the result of an integer-to-pointer cast"

subjustMirRefLeaf ::
    TypeRepr tp ->
    MirReference sym ->
    MuxLeafT sym IO (MirReference sym)
subjustMirRefLeaf tpr ref =
  typedLeafOp "subjust" (MaybeRepr tpr) ref $ \root path -> do
    return $ MirReference tpr root (Just_RefPath tpr path)

subjustMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    IO (MirReferenceMux sym)
subjustMirRefIO bak iTypes tpr ref =
    modifyRefMuxIO bak iTypes (subjustMirRefLeaf tpr) ref

mirRef_agElemLeaf ::
    RegValue sym UsizeType ->
    Word ->
    TypeRepr tp ->
    MirReference sym ->
    MuxLeafT sym IO (MirReference sym)
mirRef_agElemLeaf off sz tpr ref =
  typedLeafOp "MirAggregate element projection" MirAggregateRepr ref $ \root path -> do
    return $ MirReference tpr root (AgElem_RefPath off sz tpr path)

mirRef_agElemIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    RegValue sym UsizeType ->
    Word ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    IO (MirReferenceMux sym)
mirRef_agElemIO bak iTypes off sz tpr ref =
    modifyRefMuxIO bak iTypes (mirRef_agElemLeaf off sz tpr) ref


refRootEq ::
    IsSymInterface sym =>
    sym ->
    MirReferenceRoot sym tp1 ->
    MirReferenceRoot sym tp2 ->
    MuxLeafT sym IO (RegValue sym BoolType)
refRootEq sym (RefCell_RefRoot rc1) (RefCell_RefRoot rc2)
  | Just Refl <- testEquality rc1 rc2 = return $ truePred sym
refRootEq sym (GlobalVar_RefRoot gv1) (GlobalVar_RefRoot gv2)
  | Just Refl <- testEquality gv1 gv2 = return $ truePred sym
refRootEq _sym (Const_RefRoot _ _) (Const_RefRoot _ _) =
    leafAbort $ Unsupported callStack $ "Cannot compare Const_RefRoots"

refRootEq sym (RefCell_RefRoot {}) _ = return $ falsePred sym
refRootEq sym (GlobalVar_RefRoot {}) _ = return $ falsePred sym
refRootEq sym (Const_RefRoot {}) _ = return $ falsePred sym

refPathEq ::
    IsSymInterface sym =>
    sym ->
    MirReferencePath sym tp_base1 tp1 ->
    MirReferencePath sym tp_base2 tp2 ->
    MuxLeafT sym IO (RegValue sym BoolType)
refPathEq sym Empty_RefPath Empty_RefPath = return $ truePred sym
refPathEq sym (Field_RefPath ctx1 p1 idx1) (Field_RefPath ctx2 p2 idx2)
  | Just Refl <- testEquality ctx1 ctx2
  , Just Refl <- testEquality idx1 idx2 = refPathEq sym p1 p2
refPathEq sym (Variant_RefPath _ ctx1 p1 idx1) (Variant_RefPath _ ctx2 p2 idx2)
  | Just Refl <- testEquality ctx1 ctx2
  , Just Refl <- testEquality idx1 idx2 = refPathEq sym p1 p2
refPathEq sym (Just_RefPath tpr1 p1) (Just_RefPath tpr2 p2)
  | Just Refl <- testEquality tpr1 tpr2 = refPathEq sym p1 p2
refPathEq sym (VectorIndex_RefPath tpr1 p1 idx1) (VectorIndex_RefPath tpr2 p2 idx2)
  | Just Refl <- testEquality tpr1 tpr2 = do
    pEq <- refPathEq sym p1 p2
    idxEq <- liftIO $ bvEq sym idx1 idx2
    liftIO $ andPred sym pEq idxEq
refPathEq sym (ArrayIndex_RefPath btpr1 p1 idx1) (ArrayIndex_RefPath btpr2 p2 idx2)
  | Just Refl <- testEquality btpr1 btpr2 = do
    pEq <- refPathEq sym p1 p2
    idxEq <- liftIO $ bvEq sym idx1 idx2
    liftIO $ andPred sym pEq idxEq
refPathEq sym (AgElem_RefPath off1 _sz1 _tpr1 p1) (AgElem_RefPath off2 _sz2 _tpr2 p2) = do
    offEq <- liftIO $ bvEq sym off1 off2
    -- NB: Don't check the following for equality:
    --
   --
    -- * The TypeReprs (_tpr{1,2}), as pointers with the same memory addresses
    --   can have different types if pointer casting is involved (see the
    --   crux-mir/test/conc_eval/tuple/ref_path_equality.rs test case for an
    --   example).
    --
    -- * The sizes (_sz{1,2}), as pointers of different types may have
    --   different layout sizes.
    pEq <- refPathEq sym p1 p2
    liftIO $ andPred sym offEq pEq

refPathEq sym Empty_RefPath _ = return $ falsePred sym
refPathEq sym (Field_RefPath {}) _ = return $ falsePred sym
refPathEq sym (Variant_RefPath {}) _ = return $ falsePred sym
refPathEq sym (Just_RefPath {}) _ = return $ falsePred sym
refPathEq sym (VectorIndex_RefPath {}) _ = return $ falsePred sym
refPathEq sym (ArrayIndex_RefPath {}) _ = return $ falsePred sym
refPathEq sym (AgElem_RefPath {}) _ = return $ falsePred sym

mirRef_eqLeaf ::
    IsSymInterface sym =>
    sym ->
    MirReference sym ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym BoolType)
mirRef_eqLeaf sym (MirReference _ root1 path1) (MirReference _ root2 path2) = do
    rootEq <- refRootEq sym root1 root2
    pathEq <- refPathEq sym path1 path2
    liftIO $ andPred sym rootEq pathEq
mirRef_eqLeaf sym (MirReference_Integer i1) (MirReference_Integer i2) =
    liftIO $ isEq sym i1 i2
mirRef_eqLeaf sym _ _ =
    -- All valid references are disjoint from all integer references.
    return $ falsePred sym

mirRef_eqIO ::
    (IsSymBackend sym bak) =>
    bak ->
    MirReferenceMux sym ->
    MirReferenceMux sym ->
    IO (RegValue sym BoolType)
mirRef_eqIO bak (MirReferenceMux r1) (MirReferenceMux r2) =
    let sym = backendGetSym bak in
    zipFancyMuxTrees' bak (mirRef_eqLeaf sym) (itePred sym) r1 r2

vectorTakeIO ::
    IsSymBackend sym bak =>
    bak ->
    TypeRepr tp ->
    V.Vector (RegValue sym tp) ->
    RegValue sym NatType ->
    IO (V.Vector (RegValue sym tp))
vectorTakeIO bak _tp v idx = case asNat idx of
    Just idx' -> return $ V.take (fromIntegral idx') v
    Nothing -> addFailedAssertion bak $
        GenericSimError "VectorTake index must be concrete"

vectorDropIO ::
    IsSymBackend sym bak =>
    bak ->
    TypeRepr tp ->
    V.Vector (RegValue sym tp) ->
    RegValue sym NatType ->
    IO (V.Vector (RegValue sym tp))
vectorDropIO bak _tpr v idx = case asNat idx of
    Just idx' -> return $ V.drop (fromIntegral idx') v
    Nothing -> addFailedAssertion bak $
        GenericSimError "VectorDrop index must be concrete"

arrayZeroedIO ::
    (IsSymInterface sym, 1 <= w) =>
    sym ->
    Assignment BaseTypeRepr (idxs ::> idx) ->
    NatRepr w ->
    IO (RegValue sym (SymbolicArrayType (idxs ::> idx) (BaseBVType w)))
arrayZeroedIO sym idxs w = do
    zero <- bvZero sym w
    constantArray sym idxs zero

concreteAllocSize ::
    IsSymBackend sym bak =>
    bak ->
    RegValue sym UsizeType ->
    IO Integer
concreteAllocSize bak szSym =
    case asBV szSym of
        Just x -> return (BV.asUnsigned x)
        Nothing -> addFailedAssertion bak $ Unsupported callStack $
            "Attempted to create allocation of symbolic size"


mirAggregate_uninitIO ::
    IsSymBackend sym bak =>
    bak ->
    RegValue sym UsizeType ->
    IO (RegValue sym MirAggregateType)
mirAggregate_uninitIO bak szSym = do
  sz <- concreteAllocSize bak szSym
  return $ MirAggregate (fromIntegral sz) mempty

-- | Construct a 'MirAggregate' value representing a zero-sized type (ZST) such
-- as an empty tuple or array.
mirAggregate_zstSim :: OverrideSim p sym MIR rtp args ret (MirAggregate sym)
mirAggregate_zstSim = liftIO mirAggregate_zstIO

-- | Construct a 'MirAggregate' value representing a zero-sized type (ZST) such
-- as an empty tuple or array.
mirAggregate_zstIO :: IO (MirAggregate sym)
mirAggregate_zstIO = pure $ MirAggregate 0 mempty

mirAggregate_replicateIO ::
    IsSymBackend sym bak =>
    bak ->
    Word ->
    TypeRepr tp ->
    RegValue sym tp ->
    RegValue sym UsizeType ->
    IO (RegValue sym MirAggregateType)
mirAggregate_replicateIO bak elemSz elemTpr elemVal lenSym = do
  let sym = backendGetSym bak
  len <- concreteAllocSize bak lenSym
  let totalSize = fromIntegral len * elemSz
  let entries =
        [(fromIntegral i * fromIntegral elemSz,
          MirAggregateEntry elemSz elemTpr (justPartExpr sym elemVal))
        | i <- init [0 .. len]]
  return $ MirAggregate totalSize (IntMap.fromAscList entries)

mirAggregate_resizeIO ::
    IsSymBackend sym bak =>
    bak ->
    RegValue sym MirAggregateType ->
    RegValue sym UsizeType ->
    IO (RegValue sym MirAggregateType)
mirAggregate_resizeIO bak ag szSym = do
  sz <- concreteAllocSize bak szSym
  return $ resizeMirAggregate ag (fromIntegral sz)

mirAggregate_getIO ::
    IsSymBackend sym bak =>
    bak ->
    Word ->
    Word ->
    TypeRepr tp ->
    MirAggregate sym ->
    IO (RegValue sym tp)
mirAggregate_getIO bak off sz tpr (MirAggregate _ m) = do
  -- TODO: deduplicate logic between this and readMirAg* concrete case?
  MirAggregateEntry sz' tpr' rvPart <- case IntMap.lookup (fromIntegral off) m of
    Just x -> return x
    Nothing -> addFailedAssertion bak $ ReadBeforeWriteSimError $
      "getIO " ++ show off ++ " " ++ show sz ++ " " ++ show tpr ++ " " ++ show m ++ ": no entry at offset " ++ show off
  Refl <- case testEquality tpr tpr' of
    Just x -> return x
    Nothing -> addFailedAssertion bak $ GenericSimError $
      "type mismatch at offset " ++ show off ++ ": " ++ show tpr ++ " != " ++ show tpr'
  when (sz /= sz') $
    addFailedAssertion bak $ GenericSimError $
      "size mismatch at offset " ++ show off ++ ": " ++ show sz ++ " != " ++ show sz'
  rv <- readPartExpr bak rvPart $ ReadBeforeWriteSimError $
    "uninitialized entry at offset " ++ show off
  return rv

mirAggregate_setIO ::
    IsSymBackend sym bak =>
    bak ->
    Word ->
    Word ->
    TypeRepr tp ->
    RegValue sym tp ->
    MirAggregate sym ->
    IO (MirAggregate sym)
mirAggregate_setIO bak off sz tpr rv ag = do
  let sym = backendGetSym bak
  -- Entries are partial, but `mirAggregate_set` always inserts `Just`.  The
  -- `Nothing` case arises only from muxing.
  let rv' = justPartExpr sym rv
  let entry = MirAggregateEntry sz tpr rv'
  case mirAggregate_insert off entry ag of
    Left err -> fail err
    Right ag' -> return ag'


-- | An ordinary `MirReferencePath sym tp tp''` is represented "inside-out": to
-- turn `tp` into `tp''`, we first use a subsidiary `MirReferencePath` to turn
-- `tp` into `tp'`, then perform one last step to turn `tp'` into `tp''`.
-- `ReversedRefPath` is represented "outside-in", so the first/outermost
-- element is the first step of the conversion, not the last.
data ReversedRefPath sym :: CrucibleType -> CrucibleType -> Type where
  RrpNil :: forall sym tp. ReversedRefPath sym tp tp
  RrpCons :: forall sym tp tp' tp''.
    -- | The first step of the path.  For all cases but Empty_RefPath, the
    -- nested initial MirReferencePath is always Empty_RefPath.
    MirReferencePath sym tp tp' ->
    ReversedRefPath sym tp' tp'' ->
    ReversedRefPath sym tp tp''

instance IsSymInterface sym => Show (ReversedRefPath sym tp tp') where
    show RrpNil = "RrpNil"
    show (RrpCons rp rrp) = "(RrpCons " ++ show rp ++ " " ++ show rrp ++ ")"

reverseRefPath :: forall sym tp tp'.
    MirReferencePath sym tp tp' ->
    ReversedRefPath sym tp tp'
reverseRefPath = go RrpNil
  where
    go :: forall tp_ tp_' tp_''.
        ReversedRefPath sym tp_' tp_'' ->
        MirReferencePath sym tp_ tp_' ->
        ReversedRefPath sym tp_ tp_''
    go acc Empty_RefPath = acc
    go acc (Field_RefPath ctx rp idx) =
        go (Field_RefPath ctx Empty_RefPath idx `RrpCons` acc) rp
    go acc (Variant_RefPath tp ctx rp idx) =
        go (Variant_RefPath tp ctx Empty_RefPath idx `RrpCons` acc) rp
    go acc (Just_RefPath tpr rp) =
        go (Just_RefPath tpr Empty_RefPath `RrpCons` acc) rp
    go acc (VectorIndex_RefPath tpr rp idx) =
        go (VectorIndex_RefPath tpr Empty_RefPath idx `RrpCons` acc) rp
    go acc (ArrayIndex_RefPath btpr rp idx) =
        go (ArrayIndex_RefPath btpr Empty_RefPath idx `RrpCons` acc) rp
    go acc (AgElem_RefPath off sz tpr rp) =
        go (AgElem_RefPath off sz tpr Empty_RefPath `RrpCons` acc) rp

-- | If the final step of `path` is an indexing-related `RefPath`, remove it.
-- Otherwise, return `path` unchanged.
popIndex :: MirReferencePath sym tp tp' -> Some (MirReferencePath sym tp)
popIndex (VectorIndex_RefPath _ p _) = Some p
popIndex (ArrayIndex_RefPath _ p _) = Some p
popIndex (AgElem_RefPath _ _ _ p) = Some p
popIndex p = Some p


refRootOverlaps :: IsSymInterface sym => sym ->
    MirReferenceRoot sym tp1 -> MirReferenceRoot sym tp2 ->
    MuxLeafT sym IO (RegValue sym BoolType)
refRootOverlaps sym (RefCell_RefRoot rc1) (RefCell_RefRoot rc2)
  | Just Refl <- testEquality rc1 rc2 = return $ truePred sym
refRootOverlaps sym (GlobalVar_RefRoot gv1) (GlobalVar_RefRoot gv2)
  | Just Refl <- testEquality gv1 gv2 = return $ truePred sym
refRootOverlaps _sym (Const_RefRoot _ _) (Const_RefRoot _ _) =
    leafAbort $ Unsupported callStack $ "Cannot compare Const_RefRoots"

refRootOverlaps sym (RefCell_RefRoot {}) _ = return $ falsePred sym
refRootOverlaps sym (GlobalVar_RefRoot {}) _ = return $ falsePred sym
refRootOverlaps sym (Const_RefRoot {}) _ = return $ falsePred sym

-- | Check whether two `MirReferencePath`s might reference overlapping memory
-- regions, when starting from the same `MirReferenceRoot`.
refPathOverlaps :: forall sym tp_base1 tp1 tp_base2 tp2. IsSymInterface sym =>
    sym ->
    MirReferencePath sym tp_base1 tp1 ->
    MirReferencePath sym tp_base2 tp2 ->
    MuxLeafT sym IO (RegValue sym BoolType)
refPathOverlaps sym path1 path2 = do
    -- We remove the outermost `Index` before comparing, since `offset` allows
    -- modifying the index value arbitrarily, giving access to all elements of
    -- the containing vector.
    Some path1' <- return $ popIndex path1
    Some path2' <- return $ popIndex path2
    -- Essentially, this checks whether `rrp1` is a prefix of `rrp2` or vice
    -- versa.
    go (reverseRefPath path1') (reverseRefPath path2')
  where
    go :: forall tp1_ tp1_' tp2_ tp2_'.
        ReversedRefPath sym tp1_ tp1_' ->
        ReversedRefPath sym tp2_ tp2_' ->
        MuxLeafT sym IO (RegValue sym BoolType)
    -- An empty RefPath (`RrpNil`) covers the whole object, so it overlaps with
    -- all other paths into the same object.
    go RrpNil _ = return $ truePred sym
    go _ RrpNil = return $ truePred sym
    go (Empty_RefPath `RrpCons` rrp1) rrp2 = go rrp1 rrp2
    go rrp1 (Empty_RefPath `RrpCons` rrp2) = go rrp1 rrp2
    go (Field_RefPath ctx1 _ idx1 `RrpCons` rrp1) (Field_RefPath ctx2 _ idx2 `RrpCons` rrp2)
      | Just Refl <- testEquality ctx1 ctx2
      , Just Refl <- testEquality idx1 idx2 = go rrp1 rrp2
    go (Variant_RefPath _ ctx1 _ idx1 `RrpCons` rrp1) (Variant_RefPath _ ctx2 _ idx2 `RrpCons` rrp2)
      | Just Refl <- testEquality ctx1 ctx2
      , Just Refl <- testEquality idx1 idx2 = go rrp1 rrp2
    go (Just_RefPath tpr1 _ `RrpCons` rrp1) (Just_RefPath tpr2 _ `RrpCons` rrp2)
      | Just Refl <- testEquality tpr1 tpr2 = go rrp1 rrp2
    go (VectorIndex_RefPath tpr1 _ idx1 `RrpCons` rrp1) (VectorIndex_RefPath tpr2 _ idx2 `RrpCons` rrp2)
      | Just Refl <- testEquality tpr1 tpr2 = do
        rrpEq <- go rrp1 rrp2
        idxEq <- liftIO $ bvEq sym idx1 idx2
        liftIO $ andPred sym rrpEq idxEq
    go (ArrayIndex_RefPath btpr1 _ idx1 `RrpCons` rrp1) (ArrayIndex_RefPath btpr2 _ idx2 `RrpCons` rrp2)
      | Just Refl <- testEquality btpr1 btpr2 = do
        rrpEq <- go rrp1 rrp2
        idxEq <- liftIO $ bvEq sym idx1 idx2
        liftIO $ andPred sym rrpEq idxEq
    go (AgElem_RefPath off1 sz1 _tpr1 _ `RrpCons` rrp1)
        (AgElem_RefPath off2 sz2 _tpr2 _ `RrpCons` rrp2) = do
        let sizeWidth = knownNat @SizeBits
        let bvSizeLit :: Word -> MuxLeafT sym IO (SymBV sym SizeBits)
            bvSizeLit = liftIO . bvLit sym sizeWidth . BV.mkBV sizeWidth . toInteger
        szBv1 <- bvSizeLit sz1
        szBv2 <- bvSizeLit sz2
        offSz1 <- liftIO $ bvAdd sym off1 szBv1
        offSz2 <- liftIO $ bvAdd sym off2 szBv2
        -- Check that `[off1 .. off1 + sz1]` overlaps `[off2 .. off2 + sz2]`.
        -- This check is unique to AgElem_RefPath because its sub-locations may
        -- not necessarily be disjoint from each other.
        overlapsPart1 <- liftIO $ bvUle sym offSz1 off2
        overlapsPart2 <- liftIO $ bvUle sym offSz2 off1
        overlaps <- liftIO $ andPred sym overlapsPart1 overlapsPart2
        -- NB: Don't check the TypeReprs for equality, as pointers with the
        -- same memory addresses can have different types if pointer casting is
        -- involved (see the crux-mir/test/conc_eval/tuple/ref_path_equality.rs
        -- test case for an example).
        pEq <- go rrp1 rrp2
        liftIO $ andPred sym overlaps pEq

    go (Field_RefPath {} `RrpCons` _) _ = return $ falsePred sym
    go (Variant_RefPath {} `RrpCons` _) _ = return $ falsePred sym
    go (Just_RefPath {} `RrpCons` _) _ = return $ falsePred sym
    go (VectorIndex_RefPath {} `RrpCons` _) _ = return $ falsePred sym
    go (ArrayIndex_RefPath {} `RrpCons` _) _ = return $ falsePred sym
    go (AgElem_RefPath {} `RrpCons` _) _ = return $ falsePred sym

-- | Check whether the memory accessible through `ref1` overlaps the memory
-- accessible through `ref2`.
mirRef_overlapsLeaf ::
    IsSymInterface sym =>
    sym ->
    MirReference sym ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym BoolType)
mirRef_overlapsLeaf sym (MirReference _ root1 path1) (MirReference _ root2 path2) = do
    rootOverlaps <- refRootOverlaps sym root1 root2
    case asConstantPred rootOverlaps of
        Just False -> return $ falsePred sym
        _ -> do
            pathOverlaps <- refPathOverlaps sym path1 path2
            liftIO $ andPred sym rootOverlaps pathOverlaps
-- No memory is accessible through an integer reference, so they can't overlap
-- with anything.
mirRef_overlapsLeaf sym (MirReference_Integer _) _ = return $ falsePred sym
mirRef_overlapsLeaf sym _ (MirReference_Integer _) = return $ falsePred sym

mirRef_overlapsIO ::
    (IsSymBackend sym bak) =>
    bak ->
    MirReferenceMux sym ->
    MirReferenceMux sym ->
    IO (RegValue sym BoolType)
mirRef_overlapsIO bak (MirReferenceMux r1) (MirReferenceMux r2) =
    let sym = backendGetSym bak in
    zipFancyMuxTrees' bak (mirRef_overlapsLeaf sym) (itePred sym) r1 r2


mirRef_offsetLeaf ::
    (IsSymBackend sym bak) =>
    bak ->
    MirReference sym ->
    RegValue sym IsizeType ->
    MuxLeafT sym IO (MirReference sym)
-- TODO: `offset` has a number of preconditions that we should check here:
-- * addition must not overflow
-- * resulting pointer must be in-bounds for the allocation
-- * total offset in bytes must not exceed isize::MAX
mirRef_offsetLeaf = mirRef_offsetWrapLeaf

mirRef_offsetWrapLeaf ::
    (IsSymBackend sym bak) =>
    bak ->
    MirReference sym ->
    RegValue sym IsizeType ->
    MuxLeafT sym IO (MirReference sym)
mirRef_offsetWrapLeaf bak (MirReference tpr root (VectorIndex_RefPath tpr' path idx)) offset = do
    let sym = backendGetSym bak
    -- `wrapping_offset` puts no restrictions on the arithmetic performed.
    idx' <- liftIO $ bvAdd sym idx offset
    return $ MirReference tpr root $ VectorIndex_RefPath tpr' path idx'
mirRef_offsetWrapLeaf bak (MirReference tpr root (ArrayIndex_RefPath btpr path idx)) offset = do
    let sym = backendGetSym bak
    -- `wrapping_offset` puts no restrictions on the arithmetic performed.
    idx' <- liftIO $ bvAdd sym idx offset
    return $ MirReference tpr root $ ArrayIndex_RefPath btpr path idx'
mirRef_offsetWrapLeaf bak (MirReference tpr root (AgElem_RefPath idx sz tpr' path)) offset = do
    let sym = backendGetSym bak
    -- `wrapping_offset` puts no restrictions on the arithmetic performed.
    idx' <- liftIO $ bvAdd sym idx offset
    return $ MirReference tpr root $ AgElem_RefPath idx' sz tpr' path
mirRef_offsetWrapLeaf bak ref@(MirReference _ _ _) offset = do
    let sym = backendGetSym bak
    isZero <- liftIO $ bvEq sym offset =<< bvZero sym knownNat
    leafAssert bak isZero $ Unsupported callStack $
        "pointer arithmetic outside arrays is not yet implemented"
    return ref
mirRef_offsetWrapLeaf bak ref@(MirReference_Integer _) offset = do
    let sym = backendGetSym bak
    -- Offsetting by zero is a no-op, and is always allowed, even on invalid
    -- pointers.  In particular, this permits `(&[])[0..]`.
    isZero <- liftIO $ bvEq sym offset =<< bvZero sym knownNat
    leafAssert bak isZero $ Unsupported callStack $
        "cannot perform pointer arithmetic on invalid pointer"
    return ref

mirRef_tryOffsetFromLeaf ::
    IsSymInterface sym =>
    sym ->
    MirReference sym ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym (MaybeType IsizeType))
mirRef_tryOffsetFromLeaf sym (MirReference _ root1 path1) (MirReference _ root2 path2) = do
    rootEq <- refRootEq sym root1 root2
    case (path1, path2) of
        (VectorIndex_RefPath _ path1' idx1, VectorIndex_RefPath _ path2' idx2) -> do
            pathEq <- refPathEq sym path1' path2'
            similar <- liftIO $ andPred sym rootEq pathEq
            -- TODO: implement overflow checks, similar to `offset`
            offset <- liftIO $ bvSub sym idx1 idx2
            return $ mkPE similar offset
        (ArrayIndex_RefPath _ path1' idx1, ArrayIndex_RefPath _ path2' idx2) -> do
            pathEq <- refPathEq sym path1' path2'
            similar <- liftIO $ andPred sym rootEq pathEq
            -- TODO: implement overflow checks, similar to `offset`
            offset <- liftIO $ bvSub sym idx1 idx2
            return $ mkPE similar offset
        (AgElem_RefPath off1 _ _ path1', AgElem_RefPath off2 _ _ path2') -> do
            pathEq <- refPathEq sym path1' path2'
            similar <- liftIO $ andPred sym rootEq pathEq
            -- TODO: divide by `sz`?  This implements `byte_offset_from`, which
            -- is the same as `offset_from` only when size=1
            offset <- liftIO $ bvSub sym off1 off2
            return $ mkPE similar offset
        _ -> do
            pathEq <- refPathEq sym path1 path2
            similar <- liftIO $ andPred sym rootEq pathEq
            liftIO $ mkPE similar <$> bvZero sym knownNat
mirRef_tryOffsetFromLeaf sym (MirReference_Integer i1) (MirReference_Integer i2) = do
    -- Return zero if `i1 == i2`; otherwise, return `Unassigned`.
    --
    -- For more interesting cases, we would need to know the element size to
    -- use in converting the byte offset `i1 - i2` into an element count.
    eq <- liftIO $ bvEq sym i1 i2
    liftIO $ mkPE eq <$> bvZero sym knownNat
mirRef_tryOffsetFromLeaf _ _ _ = do
    -- MirReference_Integer pointers are always disjoint from all MirReference
    -- pointers, so we report them as being in different objects.
    return Unassigned

mirRef_tryOffsetFromIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    MirReferenceMux sym ->
    IO (RegValue sym (MaybeType IsizeType))
mirRef_tryOffsetFromIO bak iTypes (MirReferenceMux r1) (MirReferenceMux r2) =
    let sym = backendGetSym bak in
    zipFancyMuxTrees' bak (mirRef_tryOffsetFromLeaf sym)
            (muxRegForType sym iTypes (MaybeRepr IsizeRepr)) r1 r2

mirRef_peelIndexLeaf ::
    IsSymInterface sym =>
    sym ->
    MirReference sym ->
    MuxLeafT sym IO
        (RegValue sym (StructType (EmptyCtx ::> MirReferenceType ::> UsizeType)))
mirRef_peelIndexLeaf sym (MirReference tpr root (VectorIndex_RefPath _tpr' path idx)) = do
    let ref = MirReferenceMux $ toFancyMuxTree sym $ MirReference (VectorRepr tpr) root path
    return $ Empty :> RV ref :> RV idx
mirRef_peelIndexLeaf sym (MirReference _tpr root (ArrayIndex_RefPath btpr path idx)) = do
    let ref = MirReferenceMux $ toFancyMuxTree sym $ MirReference (UsizeArrayRepr btpr) root path
    return $ Empty :> RV ref :> RV idx
mirRef_peelIndexLeaf sym (MirReference _tpr root (AgElem_RefPath idx _sz _tpr' path)) = do
    -- TODO: assumes hardcoded size=1
    let ref = MirReferenceMux $ toFancyMuxTree sym $ MirReference MirAggregateRepr root path
    return $ Empty :> RV ref :> RV idx
mirRef_peelIndexLeaf _sym (MirReference _ _ _) =
    leafAbort $ Unsupported callStack $
        "peelIndex is not yet implemented for this RefPath kind"
mirRef_peelIndexLeaf _sym _ = do
    leafAbort $ Unsupported callStack $
        "cannot perform peelIndex on invalid pointer"

mirRef_peelIndexIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    IO (RegValue sym (StructType (EmptyCtx ::> MirReferenceType ::> UsizeType)))
mirRef_peelIndexIO bak iTypes (MirReferenceMux ref) =
    let sym = backendGetSym bak
        tpr' = StructRepr (Empty :> MirReferenceRepr :> IsizeRepr) in
    readFancyMuxTree' bak (mirRef_peelIndexLeaf sym)
        (muxRegForType sym iTypes tpr') ref

-- | Compute the index of `ref` within its containing allocation, along with
-- the length of that allocation.  This is useful for determining the amount of
-- memory accessible through all valid offsets of `ref`.
--
-- Note that unlike `peelIndex`:
--
-- * This operation is /not/ valid on `ArrayIndex_RefPath`s, as SMT arrays do
--   not have a finite length.
--
-- * This operation is valid on other `MirReference` references (on which it
--   returns @(0, 1)@) and also on `MirReference_Integer` (returning @(0, 0)@).
mirRef_indexAndLenLeaf ::
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym UsizeType, RegValue sym UsizeType)
mirRef_indexAndLenLeaf bak gs iTypes (MirReference tpr root (VectorIndex_RefPath _tpr' path idx)) = do
    let sym = backendGetSym bak
    let parentTpr = VectorRepr tpr
    let parent = MirReference parentTpr root path
    parentVec <- readMirRefLeaf bak gs iTypes parentTpr parent
    let lenInteger = toInteger $ V.length parentVec
    len <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat lenInteger
    return (idx, len)
mirRef_indexAndLenLeaf _bak _gs _iTypes (MirReference _tpr _root (ArrayIndex_RefPath {})) =
    leafAbort $ Unsupported callStack
        "can't compute allocation length for Array, which is unbounded"
mirRef_indexAndLenLeaf bak gs iTypes (MirReference _tpr root (AgElem_RefPath idx _sz _tpr' path)) = do
    let sym = backendGetSym bak
    let parentTpr = MirAggregateRepr
    let parent = MirReference parentTpr root path
    parentAg <- readMirRefLeaf bak gs iTypes parentTpr parent
    let MirAggregate totalSize _ = parentAg
    -- TODO: hardcoded size=1 (implied in conversion of `totalSize` to `lenWord`)
    let lenWord = totalSize
    --when (totalSize `mod` sz /= 0) $
    --    leafAbort $ Unsupported callStack $
    --        "exepcted aggregate size (" ++ show totalSize ++ ") to be a multiple of "
    --            ++ "element size (" ++ show sz ++ ")"
    --let lenWord = totalSize `div` sz
    len <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral lenWord
    -- TODO: also divide `idx` by `sz`, and assert that it's divisible
    return (idx, len)
mirRef_indexAndLenLeaf bak _ _ (MirReference _ _ _) = do
    let sym = backendGetSym bak
    idx <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat 0
    len <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat 1
    return (idx, len)
mirRef_indexAndLenLeaf bak _ _ (MirReference_Integer _) = do
    let sym = backendGetSym bak
    -- No offset of `MirReference_Integer` is dereferenceable, so `len` is
    -- zero.
    zero <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat 0
    return (zero, zero)

mirRef_indexAndLenIO ::
    (IsSymBackend sym bak) =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    IO (PartExpr (Pred sym) (RegValue sym UsizeType, RegValue sym UsizeType))
mirRef_indexAndLenIO bak gs iTypes (MirReferenceMux ref) = do
    let sym = backendGetSym bak
    readPartialFancyMuxTree bak
        (mirRef_indexAndLenLeaf bak gs iTypes)
        (\c (tIdx, tLen) (eIdx, eLen) -> do
            idx <- baseTypeIte sym c tIdx eIdx
            len <- baseTypeIte sym c tLen eLen
            return (idx, len))
        ref

mirRef_indexAndLenSim ::
    IsSymInterface sym =>
    MirReferenceMux sym ->
    OverrideSim p sym MIR rtp args ret
        (PartExpr (Pred sym) (RegValue sym UsizeType, RegValue sym UsizeType))
mirRef_indexAndLenSim ref = do
  ovrWithBackend $ \bak ->
    do s <- get
       let gs = s ^. stateTree.actFrame.gpGlobals
       let iTypes = ctxIntrinsicTypes $ s ^. stateContext
       liftIO $ mirRef_indexAndLenIO bak gs iTypes ref


execMirStmt :: forall p sym. IsSymInterface sym => EvalStmtFunc p sym MIR
execMirStmt stmt s = withBackend ctx $ \bak ->
  case stmt of
       MirNewRef tp ->
            readOnly s $ newMirRefIO sym halloc tp

       MirIntegerToRef (regValue -> i) ->
         do let r' = MirReference_Integer i
            return (mkRef r', s)

       MirGlobalRef gv ->
         do let r = MirReference (globalType gv) (GlobalVar_RefRoot gv) Empty_RefPath
            return (mkRef r, s)

       MirConstRef tpr (regValue -> v) ->
         do let r = MirReference tpr (Const_RefRoot tpr v) Empty_RefPath
            return (mkRef r, s)

       MirReadRef tpr (regValue -> ref) ->
         readOnly s $ readMirRefIO bak gs iTypes tpr ref
       MirWriteRef tpr (regValue -> ref) (regValue -> x) ->
         writeOnly s $ writeMirRefIO bak gs iTypes tpr ref x
       MirDropRef (regValue -> ref) ->
         writeOnly s $ dropMirRefIO bak gs ref
       MirSubfieldRef ctx0 (regValue -> ref) idx ->
         readOnly s $ subfieldMirRefIO bak iTypes ctx0 ref idx
       MirSubfieldRef_Untyped (regValue -> ref) idx expectedTy ->
         readOnly s $ subfieldMirRef_UntypedIO bak iTypes ref idx expectedTy
       MirSubvariantRef tp0 ctx0 (regValue -> ref) idx ->
         readOnly s $ subvariantMirRefIO bak iTypes tp0 ctx0 ref idx
       MirSubindexRef tpr (regValue -> ref) (regValue -> idx) elemSize ->
         readOnly s $ subindexMirRefIO bak iTypes tpr ref idx elemSize
       MirSubjustRef tpr (regValue -> ref) ->
         readOnly s $ subjustMirRefIO bak iTypes tpr ref
       MirRef_AgElem (regValue -> off) sz tpr (regValue -> ref) ->
         readOnly s $ mirRef_agElemIO bak iTypes off sz tpr ref
       MirRef_Eq (regValue -> r1) (regValue -> r2) ->
         readOnly s $ mirRef_eqIO bak r1 r2
       MirRef_Offset (regValue -> ref) (regValue -> off) ->
         readOnly s $ mirRef_offsetIO bak iTypes ref off
       MirRef_OffsetWrap (regValue -> ref) (regValue -> off) ->
         readOnly s $ mirRef_offsetWrapIO bak iTypes ref off
       MirRef_TryOffsetFrom (regValue -> r1) (regValue -> r2) ->
         readOnly s $ mirRef_tryOffsetFromIO bak iTypes r1 r2
       MirRef_PeelIndex (regValue -> ref) -> do
         readOnly s $ mirRef_peelIndexIO bak iTypes ref

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
       VectorTake tp (regValue -> v) (regValue -> idx) ->
            readOnly s $ vectorTakeIO bak tp v idx
       VectorDrop tp (regValue -> v) (regValue -> idx) ->
            readOnly s $ vectorDropIO bak tp v idx
       ArrayZeroed idxs w ->
            readOnly s $ arrayZeroedIO sym idxs w

       MirAggregate_Uninit (regValue -> sz) -> do
            readOnly s $ mirAggregate_uninitIO bak sz
       MirAggregate_Replicate elemSz elemTpr (regValue -> elemVal) (regValue -> lenSym) -> do
            readOnly s $ mirAggregate_replicateIO bak elemSz elemTpr elemVal lenSym
       MirAggregate_Resize (regValue -> ag) (regValue -> szSym) -> do
            readOnly s $ mirAggregate_resizeIO bak ag szSym
       MirAggregate_Get off sz tpr (regValue -> ag) -> do
            readOnly s $ mirAggregate_getIO bak off sz tpr ag
       MirAggregate_Set off sz tpr (regValue -> rv) (regValue -> ag) -> do
            readOnly s $ mirAggregate_setIO bak off sz tpr rv ag
  where
    gs = s ^. stateTree.actFrame.gpGlobals
    ctx = s ^. stateContext
    iTypes = ctxIntrinsicTypes ctx
    sym = ctx ^. ctxSymInterface
    halloc = simHandleAllocator ctx

    mkRef :: MirReference sym -> MirReferenceMux sym
    mkRef ref = MirReferenceMux $ toFancyMuxTree sym ref

    readOnly :: SimState p sym ext rtp f a -> IO b ->
        IO (b, SimState p sym ext rtp f a)
    readOnly s' act = act >>= \x -> return (x, s')

    writeOnly ::
        SimState p sym ext rtp f a ->
        IO (SymGlobalState sym) ->
        IO ((), SimState p sym ext rtp f a)
    writeOnly s0 act = do
      gs' <- act
      let s1 = s0 & stateTree.actFrame.gpGlobals .~ gs'
      return ((), s1)


-- MirReferenceType manipulation within the OverrideSim and IO monads. These are
-- useful for implementing overrides that work with MirReferences.

newMirRefSim :: IsSymInterface sym =>
    TypeRepr tp ->
    OverrideSim m sym MIR rtp args ret (MirReferenceMux sym)
newMirRefSim tpr = do
    sym <- getSymInterface
    s <- get
    let halloc = simHandleAllocator $ s ^. stateContext
    liftIO $ newMirRefIO sym halloc tpr

newMirRefIO ::
    IsSymInterface sym =>
    sym ->
    HandleAllocator ->
    TypeRepr tp ->
    IO (MirReferenceMux sym)
newMirRefIO sym halloc tpr = do
    rc <- freshRefCell halloc tpr
    let ref = MirReference tpr (RefCell_RefRoot rc) Empty_RefPath
    return $ MirReferenceMux $ toFancyMuxTree sym ref

readRefMuxSim :: IsSymInterface sym =>
    TypeRepr tp' ->
    (MirReference sym -> MuxLeafT sym IO (RegValue sym tp')) ->
    MirReferenceMux sym ->
    OverrideSim m sym MIR rtp args ret (RegValue sym tp')
readRefMuxSim tpr' f ref =
  ovrWithBackend $ \bak -> do
    ctx <- getContext
    let iTypes = ctxIntrinsicTypes ctx
    liftIO $ readRefMuxIO bak iTypes tpr' f ref

readRefMuxIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    TypeRepr tp' ->
    (MirReference sym -> MuxLeafT sym IO (RegValue sym tp')) ->
    MirReferenceMux sym ->
    IO (RegValue sym tp')
readRefMuxIO bak iTypes tpr' f (MirReferenceMux ref) =
    readFancyMuxTree' bak f (muxRegForType (backendGetSym bak) iTypes tpr') ref

modifyRefMuxSim :: IsSymInterface sym =>
    (MirReference sym -> MuxLeafT sym IO (MirReference sym)) ->
    MirReferenceMux sym ->
    OverrideSim m sym MIR rtp args ret (MirReferenceMux sym)
modifyRefMuxSim f ref =
  ovrWithBackend $ \bak -> do
    ctx <- getContext
    let iTypes = ctxIntrinsicTypes ctx
    liftIO $ modifyRefMuxIO bak iTypes f ref

modifyRefMuxIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    (MirReference sym -> MuxLeafT sym IO (MirReference sym)) ->
    MirReferenceMux sym ->
    IO (MirReferenceMux sym)
modifyRefMuxIO bak iTypes f (MirReferenceMux ref) = do
    let sym = backendGetSym bak
    MirReferenceMux <$> mapFancyMuxTree bak (muxRef' sym iTypes) f ref

readMirRefSim :: IsSymInterface sym =>
    TypeRepr tp -> MirReferenceMux sym ->
    OverrideSim m sym MIR rtp args ret (RegValue sym tp)
readMirRefSim tpr ref =
   ovrWithBackend $ \bak ->
   do s <- get
      let gs = s ^. stateTree.actFrame.gpGlobals
      let iTypes = ctxIntrinsicTypes $ s ^. stateContext
      liftIO $ readMirRefIO bak gs iTypes tpr ref

readMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    IO (RegValue sym tp)
readMirRefIO bak gs iTypes tpr ref =
    readRefMuxIO bak iTypes tpr (readMirRefLeaf bak gs iTypes tpr) ref

writeMirRefSim ::
    IsSymInterface sym =>
    TypeRepr tp ->
    MirReferenceMux sym ->
    RegValue sym tp ->
    OverrideSim m sym MIR rtp args ret ()
writeMirRefSim tpr ref x = do
    s <- get
    let gs0 = s ^. stateTree.actFrame.gpGlobals
    let iTypes = ctxIntrinsicTypes $ s ^. stateContext
    ovrWithBackend $ \bak -> do
      gs1 <- liftIO $ writeMirRefIO bak gs0 iTypes tpr ref x
      put $ s & stateTree.actFrame.gpGlobals .~ gs1

writeMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    RegValue sym tp ->
    IO (SymGlobalState sym)
writeMirRefIO bak gs iTypes tpr (MirReferenceMux ref) x =
    foldFancyMuxTree
        bak
        (\gs' ref' -> writeMirRefLeaf bak gs' iTypes tpr ref' x)
        gs
        ref

subindexMirRefSim ::
    IsSymInterface sym =>
    sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    RegValue sym UsizeType ->
    -- | Size of the element, in bytes
    Word ->
    OverrideSim m sym MIR rtp args ret (MirReferenceMux sym)
subindexMirRefSim sym tpr ref idx elemSize = do
    modifyRefMuxSim (\ref' -> subindexMirRefLeaf sym tpr ref' idx elemSize) ref

subindexMirRefIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    RegValue sym UsizeType ->
    -- | Size of the element, in bytes
    Word ->
    IO (MirReferenceMux sym)
subindexMirRefIO bak iTypes tpr ref x elemSize =
    modifyRefMuxIO bak iTypes (\ref' -> subindexMirRefLeaf (backendGetSym bak) tpr ref' x elemSize) ref

mirRef_offsetSim :: IsSymInterface sym =>
    MirReferenceMux sym -> RegValue sym IsizeType ->
    OverrideSim m sym MIR rtp args ret (MirReferenceMux sym)
mirRef_offsetSim ref off =
    ovrWithBackend $ \bak ->
      modifyRefMuxSim (\ref' -> mirRef_offsetLeaf bak ref' off) ref

mirRef_offsetIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    RegValue sym IsizeType ->
    IO (MirReferenceMux sym)
mirRef_offsetIO bak iTypes ref off =
    modifyRefMuxIO bak iTypes (\ref' -> mirRef_offsetLeaf bak ref' off) ref

mirRef_offsetWrapSim :: IsSymInterface sym =>
    MirReferenceMux sym -> RegValue sym IsizeType ->
    OverrideSim m sym MIR rtp args ret (MirReferenceMux sym)
mirRef_offsetWrapSim ref off = do
    ovrWithBackend $ \bak ->
      modifyRefMuxSim (\ref' -> mirRef_offsetWrapLeaf bak ref' off) ref

mirRef_offsetWrapIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    RegValue sym IsizeType ->
    IO (MirReferenceMux sym)
mirRef_offsetWrapIO bak iTypes ref off =
    modifyRefMuxIO bak iTypes (\ref' -> mirRef_offsetWrapLeaf bak ref' off) ref


writeRefPath ::
  (IsSymBackend sym bak) =>
  bak ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  RegValue sym tp' ->
  MuxLeafT sym IO (RegValue sym tp)
-- Special case: when the final path segment is `Just_RefPath`, we can write to
-- it by replacing `Nothing` with `Just`.  This is useful for writing to
-- uninitialized struct fields.  Using `adjust` here would fail, since it can't
-- read the old value out of the `Nothing`.
--
-- There is a similar special case above for MirWriteRef with Empty_RefPath,
-- which allows writing to an uninitialized MirReferenceRoot.
writeRefPath bak iTypes v (Just_RefPath _tp path) x =
  adjustRefPath bak iTypes v path (\_ -> return $ justPartExpr (backendGetSym bak) x)
writeRefPath bak iTypes v (VectorIndex_RefPath tp path idx) x = do
  adjustRefPath bak iTypes v path (\vec ->
    leafAdjustVectorWithSymIndex bak (muxRegForType (backendGetSym bak) iTypes tp) vec idx (\_ ->
      return x))
writeRefPath bak iTypes v (ArrayIndex_RefPath _btp path idx) x = do
  adjustRefPath bak iTypes v path (\arr ->
    liftIO $ arrayUpdate (backendGetSym bak) arr (Empty :> idx) x)
-- For `MirAggregate`, `writeRefPath` with a concrete index can insert a new
-- entry into the aggregate.
writeRefPath bak iTypes v (AgElem_RefPath idx sz tpr path) x = do
  adjustRefPath bak iTypes v path (\v' -> do
    writeMirAggregateWithSymOffset bak (muxRegForType (backendGetSym bak) iTypes tpr)
      idx sz tpr x v')
writeRefPath bak iTypes v path x =
  adjustRefPath bak iTypes v path (\_ -> return x)

adjustRefPath ::
  (IsSymBackend sym bak) =>
  bak ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  (RegValue sym tp' -> MuxLeafT sym IO (RegValue sym tp')) ->
  MuxLeafT sym IO (RegValue sym tp)
adjustRefPath bak iTypes v path0 adj = case path0 of
  Empty_RefPath -> adj v
  Field_RefPath _ctx path fld ->
      adjustRefPath bak iTypes v path
        (\x -> adjustM (\x' -> RV <$> adj (unRV x')) fld x)
  Variant_RefPath _ _ctx path fld ->
      -- TODO: report an error if variant `fld` is not selected
      adjustRefPath bak iTypes v path (field @1 (\(RV x) ->
        RV <$> adjustM (\x' -> VB <$> mapM adj (unVB x')) fld x))
  Just_RefPath tp path ->
      adjustRefPath bak iTypes v path $ \v' -> do
          let msg = ReadBeforeWriteSimError $
                  "attempted to modify uninitialized Maybe of type " ++ show tp
          v'' <- leafReadPartExpr bak v' msg
          mv <- adj v''
          return $ justPartExpr (backendGetSym bak) mv
  VectorIndex_RefPath tp path idx ->
      adjustRefPath bak iTypes v path (\v' ->
        leafAdjustVectorWithSymIndex bak (muxRegForType (backendGetSym bak) iTypes tp) v' idx adj)
  ArrayIndex_RefPath _btp path idx ->
      adjustRefPath bak iTypes v path (\arr -> do
        let sym = backendGetSym bak
        let arrIdx = Empty :> idx
        x <- liftIO $ arrayLookup sym arr arrIdx
        x' <- adj x
        liftIO $ arrayUpdate sym arr arrIdx x')
  AgElem_RefPath idx _sz tpr path ->
      adjustRefPath bak iTypes v path (\v' -> do
        adjustMirAggregateWithSymOffset bak (muxRegForType (backendGetSym bak) iTypes tpr)
          idx tpr adj v')

readRefPath ::
  (IsSymBackend sym bak) =>
  bak ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  MuxLeafT sym IO (RegValue sym tp')
readRefPath bak iTypes v = \case
  Empty_RefPath -> return v
  Field_RefPath _ctx path fld ->
    do flds <- readRefPath bak iTypes v path
       return $ unRV $ flds ! fld
  Variant_RefPath _ ctx path fld ->
    do (Empty :> _discr :> RV variant) <- readRefPath bak iTypes v path
       let msg = GenericSimError $
               "attempted to read from wrong variant (" ++ show fld ++ " of " ++ show ctx ++ ")"
       leafReadPartExpr bak (unVB $ variant ! fld) msg
  Just_RefPath tp path ->
    do v' <- readRefPath bak iTypes v path
       let msg = ReadBeforeWriteSimError $
               "attempted to read from uninitialized Maybe of type " ++ show tp
       leafReadPartExpr bak v' msg
  VectorIndex_RefPath tp path idx ->
    do v' <- readRefPath bak iTypes v path
       leafIndexVectorWithSymIndex bak (muxRegForType (backendGetSym bak) iTypes tp) v' idx
  ArrayIndex_RefPath _btp path idx ->
    do arr <- readRefPath bak iTypes v path
       liftIO $ arrayLookup (backendGetSym bak) arr (Empty :> idx)
  AgElem_RefPath off _sz tpr path -> do
    ag <- readRefPath bak iTypes v path
    readMirAggregateWithSymOffset bak (muxRegForType (backendGetSym bak) iTypes tpr) off tpr ag


mirExtImpl :: forall sym p. IsSymInterface sym => ExtensionImpl p sym MIR
mirExtImpl = ExtensionImpl
             { extensionEval = \_sym _iTypes _log _f _state -> \case
             , extensionExec = execMirStmt
             }

--------------------------------------------------------------------------------
-- ** Slices

-- A Slice is a sequence of values plus an index to the first element
-- and a length.

type MirSlice = StructType (EmptyCtx ::>
                            MirReferenceType ::> -- first element
                            UsizeType)       --- length

pattern MirSliceRepr :: () => tp ~ MirSlice => TypeRepr tp
pattern MirSliceRepr <- StructRepr
     (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignEmpty)
         MirReferenceRepr)
         UsizeRepr)
 where MirSliceRepr = StructRepr (Empty :> MirReferenceRepr :> UsizeRepr)

mirSliceCtxRepr :: CtxRepr (EmptyCtx ::>
                            MirReferenceType ::>
                            UsizeType)
mirSliceCtxRepr = (Empty :> MirReferenceRepr :> UsizeRepr)

mkSlice ::
    Expr MIR s MirReferenceType ->
    Expr MIR s UsizeType ->
    Expr MIR s MirSlice
mkSlice vec len = App $ MkStruct mirSliceCtxRepr $
    Empty :> vec :> len

getSlicePtr :: Expr MIR s MirSlice -> Expr MIR s MirReferenceType
getSlicePtr e = getStruct i1of2 e

getSliceLen :: Expr MIR s MirSlice -> Expr MIR s UsizeType
getSliceLen e = getStruct i2of2 e


--------------------------------------------------------------------------------
-- ** MethodSpec and MethodSpecBuilder
--
-- We define the intrinsics here so they can be used in `TransTy.tyToRepr`, and
-- also define their interfaces (as typeclasses), but we don't provide any
-- concrete implementations in `crux-mir`.  Instead, implementations of these
-- types are in `saw-script/crux-mir-comp`, since they depend on some SAW
-- components, such as `saw-script`'s `MethodSpec`.

class MethodSpecImpl sym ms where
    -- | Pretty-print the MethodSpec, returning the result as a Rust string
    -- (`&str`).
    msPrettyPrint ::
        forall p rtp args ret.
        ms ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue sym MirSlice)

    -- | Enable the MethodSpec for use as an override for the remainder of the
    -- current test.
    msEnable ::
        forall p rtp args ret.
        ms ->
        OverrideSim (p sym) sym MIR rtp args ret ()

data MethodSpec sym = forall ms. MethodSpecImpl sym ms => MethodSpec {
    msData :: ms,
    msNonce :: Word64
}

type MethodSpecSymbol = "MethodSpec"
type MethodSpecType = IntrinsicType MethodSpecSymbol EmptyCtx

pattern MethodSpecRepr :: () => tp' ~ MethodSpecType => TypeRepr tp'
pattern MethodSpecRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MethodSpecSymbol) -> Just Refl) Empty
 where MethodSpecRepr = IntrinsicRepr (knownSymbol @MethodSpecSymbol) Empty

type family MethodSpecFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MethodSpecFam sym EmptyCtx = MethodSpec sym
  MethodSpecFam sym ctx = TypeError
    ('Text "MethodSpecType expects no arguments, but was given" :<>: 'ShowType ctx)
instance IsSymInterface sym => IntrinsicClass sym MethodSpecSymbol where
  type Intrinsic sym MethodSpecSymbol ctx = MethodSpecFam sym ctx

  muxIntrinsic _sym _iTypes _nm Empty _p ms1 ms2
    | msNonce ms1 == msNonce ms2 = return ms1
    | otherwise = fail "can't mux MethodSpecs"
  muxIntrinsic _sym _tys nm ctx _ _ _ = typeError nm ctx


class MethodSpecBuilderImpl sym msb where
    msbAddArg :: forall p rtp args ret tp.
        TypeRepr tp -> MirReferenceMux sym -> msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbSetReturn :: forall p rtp args ret tp.
        TypeRepr tp -> MirReferenceMux sym -> msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbGatherAssumes :: forall p rtp args ret.
        msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbGatherAsserts :: forall p rtp args ret.
        msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbFinish :: forall p rtp args ret.
        msb ->
        OverrideSim (p sym) sym MIR rtp args ret (MethodSpec sym)

data MethodSpecBuilder sym = forall msb. MethodSpecBuilderImpl sym msb => MethodSpecBuilder msb

type MethodSpecBuilderSymbol = "MethodSpecBuilder"
type MethodSpecBuilderType = IntrinsicType MethodSpecBuilderSymbol EmptyCtx

pattern MethodSpecBuilderRepr :: () => tp' ~ MethodSpecBuilderType => TypeRepr tp'
pattern MethodSpecBuilderRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MethodSpecBuilderSymbol) -> Just Refl) Empty
 where MethodSpecBuilderRepr = IntrinsicRepr (knownSymbol @MethodSpecBuilderSymbol) Empty

type family MethodSpecBuilderFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MethodSpecBuilderFam sym EmptyCtx = MethodSpecBuilder sym
  MethodSpecBuilderFam sym ctx = TypeError
    ('Text "MethodSpecBuilderType expects no arguments, but was given" :<>: 'ShowType ctx)
instance IsSymInterface sym => IntrinsicClass sym MethodSpecBuilderSymbol where
  type Intrinsic sym MethodSpecBuilderSymbol ctx = MethodSpecBuilderFam sym ctx

  muxIntrinsic _sym _iTypes _nm Empty _ _ _ =
    fail "can't mux MethodSpecBuilders"
  muxIntrinsic _sym _tys nm ctx _ _ _ = typeError nm ctx


-- Table of all MIR-specific intrinsic types.  Must be at the end so it can see
-- past all previous TH calls.

mirIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
mirIntrinsicTypes =
   MapF.insert (knownSymbol @MirReferenceSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MirAggregateSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MethodSpecSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MethodSpecBuilderSymbol) IntrinsicMuxFn $
   MapF.empty
