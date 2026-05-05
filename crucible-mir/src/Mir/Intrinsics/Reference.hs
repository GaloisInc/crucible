{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- TODO(#1786): refine exports
module Mir.Intrinsics.Reference
  ( MirReferenceSymbol,
    MirReferenceType,
    pattern MirReferenceRepr,
    MirReferenceFam,
    MirReferenceRoot (..),
    MirReferencePath (..),
    MirReference (..),
    MirReferenceMux (..),
    refRootType,
    readRefRoot,
    writeRefRoot,
    dropRefRoot,
    muxRefRoot,
    readRefPath,
    writeRefPath,
    adjustRefPath,
    muxRefPath,
    muxRef',
    muxRef,
    readRefMuxSim,
    readRefMuxMA,
    modifyRefMuxSim,
    modifyRefMuxMA,
    readBeforeWriteMsg,
    newMirRefSim,
    newMirRefIO,
    newConstMirRef,
    typedLeafOp,
    readMirRefSim,
    readMirRefMA,
    readMirRefLeaf,
    writeMirRefSim,
    writeMirRefIO,
    writeMirRefLeaf,
    dropMirRefLeaf,
    dropMirRefIO,
    subfieldMirRefLeaf,
    subfieldMirRef_UntypedLeaf,
    subfieldMirRefIO,
    subfieldMirRef_UntypedIO,
    subvariantMirRefLeaf,
    subvariantMirRefIO,
    subindexMirRefSim,
    subindexMirRefIO,
    subindexMirRefLeaf,
    subjustMirRefLeaf,
    subjustMirRefIO,
    mirRef_agElemLeaf,
    mirRef_agElemIO,
    refRootEq,
    refPathEq,
    mirRef_eqLeaf,
    mirRef_eqIO,
    ReversedRefPath (..),
    reverseRefPath,
    popIndex,
    refRootOverlaps,
    refPathOverlaps,
    mirRef_overlapsLeaf,
    mirRef_overlapsIO,
    mirRef_offsetSim,
    mirRef_offsetMA,
    mirRef_offsetLeaf,
    mirRef_offsetWrapIO,
    mirRef_offsetWrapSim,
    mirRef_offsetWrapLeaf,
    mirRef_tryOffsetFromLeaf,
    mirRef_tryOffsetFromIO,
    mirRef_peelIndexLeaf,
    mirRef_peelIndexMA,
    mirRef_peelFieldLeaf,
    mirRef_peelFieldMA,
    mirRef_peelJustLeaf,
    mirRef_peelJustMA,
    mirRef_indexAndLenLeaf,
    mirRef_indexAndLenIO,
    mirRef_indexAndLenSim,
    mirRef_aggregateAsChunksLeaf,
    mirRef_aggregateAsChunksIO,
  )
where

import GHC.Stack (callStack)
import GHC.TypeLits
  ( ErrorMessage (ShowType, Text, (:<>:)),
    TypeError,
  )

import Control.Monad (MonadPlus (..), when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Class (get, put)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Lens.Micro ((^.), (.~))

import Data.BitVector.Sized qualified as BV
import Data.Function ((&))
import Data.Kind (Type)
import Data.Parameterized.Context
  ( Ctx,
    EmptyCtx,
    Index,
    adjustM,
    field,
    intIndex,
    size,
    (!),
    (::>),
    pattern Empty,
    pattern (:>),
  )
import Data.Parameterized.NatRepr (knownNat)
import Data.Parameterized.Some (Some (..))
import Data.Parameterized.SymbolRepr (knownSymbol)
import Data.Type.Equality (TestEquality (testEquality), pattern Refl)
import Data.Vector qualified as V

import Lang.Crucible.Backend (IsSymBackend, IsSymInterface, backendGetSym)
import Lang.Crucible.CFG.Common (GlobalVar, globalType)
import Lang.Crucible.FunctionHandle (HandleAllocator, RefCell, freshRefCell, refType)
import Lang.Crucible.Simulator.ExecutionTree
  ( actFrame,
    ctxIntrinsicTypes,
    gpGlobals,
    simHandleAllocator,
    stateContext,
    stateTree,
  )
import Lang.Crucible.Simulator.GlobalState
  ( SymGlobalState,
    insertGlobal,
    lookupGlobal,
    lookupRef,
    updateRef,
  )
import Lang.Crucible.Simulator.Intrinsics (IntrinsicClass (..), IntrinsicTypes, typeError)
import Lang.Crucible.Simulator.OverrideSim
  ( OverrideSim,
    getContext,
    getSymInterface,
    ovrWithBackend,
  )
import Lang.Crucible.Simulator.RegMap (muxRegForType)
import Lang.Crucible.Simulator.RegValue
  ( RegValue,
    RegValue' (RV, unRV),
    VariantBranch (VB, unVB),
  )
import Lang.Crucible.Simulator.SimError (SimErrorReason (..))
import Lang.Crucible.Types
  ( AsBaseType (..),
    BaseToType,
    BaseTypeRepr,
    BoolType,
    CrucibleType,
    CtxRepr,
    IntrinsicType,
    MaybeType,
    StructType,
    TypeRepr (..),
    VectorType,
    asBaseType,
  )

import What4.Interface (IsExprBuilder (..), Pred, asBV, asConstantPred, bvZero, printSymExpr)
import What4.Partial (PartExpr, justPartExpr, mkPE, pattern Unassigned)

import Mir.FancyMuxTree
  ( FancyMuxTree,
    MonadAssert,
    MuxLeafT,
    OrdSkel (..),
    compareSkelF,
    compareSkelF2,
    foldFancyMuxTree,
    leafAbort,
    leafAssert,
    leafClearPartExpr,
    leafPredicate,
    leafReadPartExpr,
    leafUpdatePartExpr,
    mapFancyMuxTree,
    mergeFancyMuxTree,
    readFancyMuxTree',
    readPartialFancyMuxTree,
    toFancyMuxTree,
    zipFancyMuxTrees',
  )
import Mir.Intrinsics.Aggregate
  ( MirAggregate (..),
    MirAggregateType,
    adjustMirAggregateWithSymOffset,
    mirAggregate_concat,
    mirAggregate_fromChunks,
    mirAggregate_split3,
    mirAggregate_toChunks,
    readMirAggregateWithSymOffset,
    writeMirAggregateWithSymOffset,
    pattern MirAggregateRepr,
  )
import Mir.Intrinsics.Array (UsizeArrayType, pattern UsizeArrayRepr)
import Mir.Intrinsics.Enum (RustEnumType, pattern RustEnumRepr)
import Mir.Intrinsics.Size (IsizeType, UsizeType, wordLit, pattern IsizeRepr)
import Mir.Intrinsics.Vector (leafAdjustVectorWithSymIndex, leafIndexVectorWithSymIndex)


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
  -- | Reinterpret a portion of a `MirAggregate` as an array of equal-sized
  -- chunks.  This is used to implement @<[T]>::as_chunks@ and several related
  -- methods.  We can get rid of this once `MirAggregate` flattening is
  -- implemented.
  AggregateAsChunks_RefPath ::
    -- | Starting offset within the input aggregate
    !Word ->
    -- | Size in bytes of each chunk
    !Word ->
    -- | Number of chunks to produce
    !Word ->
    -- | Path to the input aggregate
    !(MirReferencePath sym tp_base MirAggregateType) ->
    MirReferencePath sym tp_base MirAggregateType

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
    show (AggregateAsChunks_RefPath off chunkSize numChunks p) = "(AggregateAsChunks_RefPath " ++ show off ++ " " ++ show chunkSize ++ " " ++ show numChunks ++ " " ++ show p ++ ")"

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
        cmpPath (AgElem_RefPath _ _ _ _) _ = LT
        cmpPath _ (AgElem_RefPath _ _ _ _) = GT
        cmpPath (AggregateAsChunks_RefPath off1 chunkSize1 numChunks1 p1)
                (AggregateAsChunks_RefPath off2 chunkSize2 numChunks2 p2) =
            compare off1 off2 <> compare chunkSize1 chunkSize2 <> compare numChunks1 numChunks2
              <> cmpPath p1 p2

refRootType :: MirReferenceRoot sym tp -> TypeRepr tp
refRootType (RefCell_RefRoot r) = refType r
refRootType (GlobalVar_RefRoot r) = globalType r
refRootType (Const_RefRoot tpr _) = tpr

readRefRoot :: (MonadAssert sym bak m) =>
    bak ->
    SymGlobalState sym ->
    MirReferenceRoot sym tp ->
    MuxLeafT sym m (RegValue sym tp)
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


readRefPath ::
  (MonadAssert sym bak m) =>
  bak ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  MuxLeafT sym m (RegValue sym tp')
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
  AggregateAsChunks_RefPath off chunkSize numChunks path -> do
    let sym = backendGetSym bak
    ag <- readRefPath bak iTypes v path
    chunkedAg <- case mirAggregate_toChunks sym off chunkSize numChunks ag of
      Left err -> die $ "mirAggregate_toChunks: " ++ err
      Right x -> return x
    return chunkedAg
  where
    die msg = leafAbort $ Unsupported callStack $ "readRefPath: " ++ msg

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
-- TODO remove these cases?  should be equivalent to the `adjustRefPath` cases below
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
  AggregateAsChunks_RefPath off chunkSize numChunks path ->
      adjustRefPath bak iTypes v path $ \ag -> do
        let sym = backendGetSym bak
        (beforeAg, midAg, afterAg) <-
          case mirAggregate_split3 off (off + chunkSize * numChunks) ag of
            Left err -> die $ "mirAggregate_split3: " ++ err
            Right x -> return x
        chunkedAg <- case mirAggregate_toChunks sym 0 chunkSize numChunks midAg of
          Left err -> die $ "mirAggregate_toChunks: " ++ err
          Right x -> return x
        chunkedAg' <- adj chunkedAg
        midAg' <- liftIO (mirAggregate_fromChunks sym chunkedAg') >>= \case
          Left err -> die $ "mirAggregate_fromChunks: " ++ err
          Right x -> return x
        let ag' = (beforeAg `mirAggregate_concat` midAg') `mirAggregate_concat` afterAg
        return ag'
  where
    die msg = leafAbort $ Unsupported callStack $ "adjustRefPath: " ++ msg

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
  -- TODO: I think this is only called in cases where `compareSkel` returns
  -- `EQ`, so the cases below can assume all the non-symbolic parts are equal.
  -- But it seems like the cases above don't assume this and instead check
  -- those parts for equality.
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
  (AggregateAsChunks_RefPath off chunkSize numChunks p1, AggregateAsChunks_RefPath _ _ _ p2) ->
         do p' <- muxRefPath sym c p1 p2
            return (AggregateAsChunks_RefPath off chunkSize numChunks p')

  (Empty_RefPath {}, _) -> mzero
  (Field_RefPath {}, _) -> mzero
  (Variant_RefPath {}, _) -> mzero
  (Just_RefPath {}, _) -> mzero
  (VectorIndex_RefPath {}, _) -> mzero
  (ArrayIndex_RefPath {}, _) -> mzero
  (AgElem_RefPath {}, _) -> mzero
  (AggregateAsChunks_RefPath {}, _) -> mzero


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


readRefMuxSim :: IsSymInterface sym =>
    TypeRepr tp' ->
    (MirReference sym -> MuxLeafT sym IO (RegValue sym tp')) ->
    MirReferenceMux sym ->
    OverrideSim m sym ext rtp args ret (RegValue sym tp')
readRefMuxSim tpr' f ref =
  ovrWithBackend $ \bak -> do
    ctx <- getContext
    let iTypes = ctxIntrinsicTypes ctx
    liftIO $ readRefMuxMA bak iTypes tpr' f ref

readRefMuxMA ::
    MonadAssert sym bak m =>
    bak ->
    IntrinsicTypes sym ->
    TypeRepr tp' ->
    (MirReference sym -> MuxLeafT sym m (RegValue sym tp')) ->
    MirReferenceMux sym ->
    m (RegValue sym tp')
readRefMuxMA bak iTypes tpr' f (MirReferenceMux ref) =
    readFancyMuxTree' bak f (muxRegForType (backendGetSym bak) iTypes tpr') ref


modifyRefMuxSim :: IsSymInterface sym =>
    (MirReference sym -> MuxLeafT sym IO (MirReference sym)) ->
    MirReferenceMux sym ->
    OverrideSim m sym ext rtp args ret (MirReferenceMux sym)
modifyRefMuxSim f ref =
  ovrWithBackend $ \bak -> do
    ctx <- getContext
    let iTypes = ctxIntrinsicTypes ctx
    liftIO $ modifyRefMuxMA bak iTypes f ref

modifyRefMuxMA ::
    MonadAssert sym bak m =>
    bak ->
    IntrinsicTypes sym ->
    (MirReference sym -> MuxLeafT sym m (MirReference sym)) ->
    MirReferenceMux sym ->
    m (MirReferenceMux sym)
modifyRefMuxMA bak iTypes f (MirReferenceMux ref) = do
    let sym = backendGetSym bak
    MirReferenceMux <$> mapFancyMuxTree bak (muxRef' sym iTypes) f ref


readBeforeWriteMsg :: SimErrorReason
readBeforeWriteMsg = ReadBeforeWriteSimError
    "Attempted to read uninitialized reference cell"

newMirRefSim :: IsSymInterface sym =>
    TypeRepr tp ->
    OverrideSim m sym ext rtp args ret (MirReferenceMux sym)
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

newConstMirRef :: IsSymInterface sym =>
    sym ->
    TypeRepr tp ->
    RegValue sym tp ->
    MirReferenceMux sym
newConstMirRef sym tpr v = MirReferenceMux $ toFancyMuxTree sym $
    MirReference tpr (Const_RefRoot tpr v) Empty_RefPath


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


readMirRefSim :: IsSymInterface sym =>
    TypeRepr tp -> MirReferenceMux sym ->
    OverrideSim m sym ext rtp args ret (RegValue sym tp)
readMirRefSim tpr ref =
  ovrWithBackend $ \bak ->
   do s <- get
      let gs = s ^. stateTree.actFrame.gpGlobals
      let iTypes = ctxIntrinsicTypes $ s ^. stateContext
      liftIO $ readMirRefMA bak gs iTypes tpr ref

readMirRefMA ::
    MonadAssert sym bak m =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    m (RegValue sym tp)
readMirRefMA bak gs iTypes tpr ref =
    readRefMuxMA bak iTypes tpr (readMirRefLeaf bak gs iTypes tpr) ref

readMirRefLeaf ::
    (MonadAssert sym bak m) =>
    bak ->
    SymGlobalState sym ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReference sym ->
    MuxLeafT sym m (RegValue sym tp)
readMirRefLeaf bak gs iTypes tpr ref =
  typedLeafOp "read" tpr ref $ \root path -> do
    v <- readRefRoot bak gs root
    v' <- readRefPath bak iTypes v path
    return v'


writeMirRefSim ::
    IsSymInterface sym =>
    TypeRepr tp ->
    MirReferenceMux sym ->
    RegValue sym tp ->
    OverrideSim m sym ext rtp args ret ()
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
              case intIndex fieldNum (size structCtx) of
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
    modifyRefMuxMA bak iTypes (\ref' -> subfieldMirRefLeaf ctx ref' idx) ref

subfieldMirRef_UntypedIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    Int ->
    Maybe (Some TypeRepr) ->
    IO (MirReferenceMux sym)
subfieldMirRef_UntypedIO bak iTypes ref fieldNum expectedTy =
    modifyRefMuxMA bak iTypes (\ref' -> subfieldMirRef_UntypedLeaf ref' fieldNum expectedTy) ref


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
    modifyRefMuxMA bak iTypes (\ref' -> subvariantMirRefLeaf tp ctx ref' idx) ref


subindexMirRefSim ::
    IsSymInterface sym =>
    sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    RegValue sym UsizeType ->
    -- | Size of the element, in bytes
    Word ->
    OverrideSim m sym ext rtp args ret (MirReferenceMux sym)
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
    modifyRefMuxMA bak iTypes (\ref' -> subindexMirRefLeaf (backendGetSym bak) tpr ref' x elemSize) ref

subindexMirRefLeaf ::
    IsSymInterface sym =>
    sym ->
    TypeRepr tp ->
    MirReference sym ->
    RegValue sym UsizeType ->
    -- | Size of the element, in bytes
    Word ->
    MuxLeafT sym IO (MirReference sym)
subindexMirRefLeaf sym elemTpr (MirReference tpr root path) idx elemSize
  | Just Refl <- testEquality tpr (VectorRepr elemTpr) =
      return $ MirReference elemTpr root (VectorIndex_RefPath elemTpr path idx)
  | AsBaseType btpr <- asBaseType elemTpr,
    Just Refl <- testEquality tpr (UsizeArrayRepr btpr) =
      return $ MirReference elemTpr root (ArrayIndex_RefPath btpr path idx)
  | Just Refl <- testEquality tpr MirAggregateRepr = do
      offset <- liftIO $ bvMul sym idx =<< wordLit sym elemSize
      return $ MirReference elemTpr root (AgElem_RefPath offset elemSize elemTpr path)
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
    modifyRefMuxMA bak iTypes (subjustMirRefLeaf tpr) ref


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
    modifyRefMuxMA bak iTypes (mirRef_agElemLeaf off sz tpr) ref


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
refPathEq sym (AggregateAsChunks_RefPath off1 chunkSize1 numChunks1 p1)
        (AggregateAsChunks_RefPath off2 chunkSize2 numChunks2 p2)
  | off1 == off2, chunkSize1 == chunkSize2, numChunks1 == numChunks2 = do
    refPathEq sym p1 p2

refPathEq sym Empty_RefPath _ = return $ falsePred sym
refPathEq sym (Field_RefPath {}) _ = return $ falsePred sym
refPathEq sym (Variant_RefPath {}) _ = return $ falsePred sym
refPathEq sym (Just_RefPath {}) _ = return $ falsePred sym
refPathEq sym (VectorIndex_RefPath {}) _ = return $ falsePred sym
refPathEq sym (ArrayIndex_RefPath {}) _ = return $ falsePred sym
refPathEq sym (AgElem_RefPath {}) _ = return $ falsePred sym
refPathEq sym (AggregateAsChunks_RefPath {}) _ = return $ falsePred sym

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
    go acc (AggregateAsChunks_RefPath off chunkSize numChunks rp) =
        go (AggregateAsChunks_RefPath off chunkSize numChunks Empty_RefPath `RrpCons` acc) rp

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
        szBv1 <- wordLit sym sz1
        szBv2 <- wordLit sym sz2
        offSz1 <- liftIO $ bvAdd sym off1 szBv1
        offSz2 <- liftIO $ bvAdd sym off2 szBv2
        -- FIXME: is this math correct?
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

    go (AggregateAsChunks_RefPath off1 chunkSize1 numChunks1 _ `RrpCons` rrp1)
          (AggregateAsChunks_RefPath off2 chunkSize2 numChunks2 _ `RrpCons` rrp2)
      | (off1, chunkSize1, numChunks1) == (off2, chunkSize2, numChunks2) = do
        -- Conversions match exactly.  We can recurse on `rrp1` and `rrp2`
        -- since they'll both be applied to the same shape of aggregate.
        go rrp1 rrp2
      | end1 <- toInteger off1 + (toInteger chunkSize1 * toInteger numChunks1),
        end2 <- toInteger off2 + (toInteger chunkSize2 * toInteger numChunks2),
        toInteger off1 < end2 && toInteger off2 < end1 = do
        -- Conversion regions overlap.  Rather than try to handle `rrp1` and
        -- `rrp2` precisely (accounting for possibly different starting offsets
        -- and chunk shapes), we conservatively assume that the remaining paths
        -- may also overlap.
        return $ truePred sym
      | otherwise = do
        -- Conversion regions don't overlap at all.
        return $ falsePred sym
    -- `AggregateAsChunks_RefPath` overlaps with some `AgElem_RefPath` paths.
    go (AggregateAsChunks_RefPath off1 chunkSize1 numChunks1 _ `RrpCons` _rrp1)
          (AgElem_RefPath off2 sz2 _tpr2 _ `RrpCons` _rrp2) = do
      let end1 = off1 + (chunkSize1 * numChunks1)
      szBv2 <- wordLit sym sz2
      end2 <- liftIO $ bvAdd sym off2 szBv2
      -- Check `off1 < end2 && off2 < end1`
      offBv1 <- wordLit sym off1
      endBv1 <- wordLit sym end1
      overlapsPart1 <- liftIO $ bvUlt sym offBv1 end2
      overlapsPart2 <- liftIO $ bvUlt sym off2 endBv1
      -- If the two regions overlap, conservatively assume that the rest of the
      -- path may also overlap, and return true without considering `rrp1` and
      -- `rrp2`.
      liftIO $ andPred sym overlapsPart1 overlapsPart2
    go (AgElem_RefPath off1 sz1 _tpr1 _ `RrpCons` _rrp1)
          (AggregateAsChunks_RefPath off2 chunkSize2 numChunks2 _ `RrpCons` _rrp2) = do
      let end2 = off2 + (chunkSize2 * numChunks2)
      szBv1 <- wordLit sym sz1
      end1 <- liftIO $ bvAdd sym off1 szBv1
      -- Check `off1 < end2 && off2 < end1`
      offBv2 <- wordLit sym off2
      endBv2 <- wordLit sym end2
      overlapsPart1 <- liftIO $ bvUlt sym off1 endBv2
      overlapsPart2 <- liftIO $ bvUlt sym offBv2 end1
      -- If the two regions overlap, conservatively assume that the rest of the
      -- path may also overlap, and return true without considering `rrp1` and
      -- `rrp2`.
      liftIO $ andPred sym overlapsPart1 overlapsPart2
    -- Any other cases involving `AggregateAsChunks_RefPath` we conservatively
    -- assume may overlap.
    go (AggregateAsChunks_RefPath {} `RrpCons` _) _ = return $ truePred sym
    go _ (AggregateAsChunks_RefPath {} `RrpCons` _) = return $ truePred sym

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


mirRef_offsetSim ::
    IsSymInterface sym =>
    MirReferenceMux sym ->
    -- | The number of elements by which to offset
    RegValue sym IsizeType ->
    -- | The size of each element, in bytes
    Word ->
    OverrideSim m sym ext rtp args ret (MirReferenceMux sym)
mirRef_offsetSim ref off elemSize =
    ovrWithBackend $ \bak ->
      modifyRefMuxSim (\ref' -> mirRef_offsetLeaf bak ref' off elemSize) ref

mirRef_offsetMA ::
    MonadAssert sym bak m =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    -- | The number of elements by which to offset
    RegValue sym IsizeType ->
    -- | The size of each element, in bytes
    Word ->
    m (MirReferenceMux sym)
mirRef_offsetMA bak iTypes ref off elemSize =
    modifyRefMuxMA bak iTypes (\ref' -> mirRef_offsetLeaf bak ref' off elemSize) ref

mirRef_offsetLeaf ::
    (MonadAssert sym bak m) =>
    bak ->
    MirReference sym ->
    -- | The number of elements by which to offset
    RegValue sym IsizeType ->
    -- | The size of each element, in bytes
    Word ->
    MuxLeafT sym m (MirReference sym)
-- TODO: `offset` has a number of preconditions that we should check here:
-- * addition must not overflow
-- * resulting pointer must be in-bounds for the allocation
-- * total offset in bytes must not exceed isize::MAX
mirRef_offsetLeaf = mirRef_offsetWrapLeaf


mirRef_offsetWrapSim ::
    IsSymInterface sym =>
    MirReferenceMux sym ->
    -- | The number of elements by which to offset
    RegValue sym IsizeType ->
    -- | The size of each element, in bytes
    Word ->
    OverrideSim m sym ext rtp args ret (MirReferenceMux sym)
mirRef_offsetWrapSim ref off elemSize = do
    ovrWithBackend $ \bak ->
      modifyRefMuxSim (\ref' -> mirRef_offsetWrapLeaf bak ref' off elemSize) ref

mirRef_offsetWrapIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    -- | The number of elements by which to offset
    RegValue sym IsizeType ->
    -- | The size of each element, in bytes
    Word ->
    IO (MirReferenceMux sym)
mirRef_offsetWrapIO bak iTypes ref off elemSize =
    modifyRefMuxMA bak iTypes (\ref' -> mirRef_offsetWrapLeaf bak ref' off elemSize) ref

mirRef_offsetWrapLeaf ::
    (MonadAssert sym bak m) =>
    bak ->
    MirReference sym ->
    -- | The number of elements by which to offset
    RegValue sym IsizeType ->
    -- | The size of each element, in bytes
    Word ->
    MuxLeafT sym m (MirReference sym)
mirRef_offsetWrapLeaf bak (MirReference tpr root (VectorIndex_RefPath tpr' path idx)) numElems  _elemSize = do
    let sym = backendGetSym bak
    -- `wrapping_offset` puts no restrictions on the arithmetic performed.
    idx' <- liftIO $ bvAdd sym idx numElems
    return $ MirReference tpr root $ VectorIndex_RefPath tpr' path idx'
mirRef_offsetWrapLeaf bak (MirReference tpr root (ArrayIndex_RefPath btpr path idx)) numElems _elemSize = do
    let sym = backendGetSym bak
    -- `wrapping_offset` puts no restrictions on the arithmetic performed.
    idx' <- liftIO $ bvAdd sym idx numElems
    return $ MirReference tpr root $ ArrayIndex_RefPath btpr path idx'
mirRef_offsetWrapLeaf bak (MirReference tpr root (AgElem_RefPath elemOff _elemSize tpr' path)) numElems elemSize = do
    -- Note that we ignore the element size associated with the `AgElem_RefPath`
    -- we're processing in favor of the one we're given as a parameter. This
    -- accommodates patterns like casting `*const u32` to `*const u8`, using
    -- `offset` on the latter, then casting back to the former. The cast isn't
    -- (currently) implemented to change the element size in the
    -- `AgElem_RefPath`, so to use that size in that case would have us
    -- improperly offset by 4 bytes (i.e. the size of a `u32`) at a time.
    let sym = backendGetSym bak
    -- `wrapping_offset` puts no restrictions on the arithmetic performed.
    extraOff <- liftIO $ bvMul sym numElems =<< wordLit sym elemSize
    elemOff' <- liftIO $ bvAdd sym elemOff extraOff
    return $ MirReference tpr root $ AgElem_RefPath elemOff' elemSize tpr' path
mirRef_offsetWrapLeaf bak ref@(MirReference _ _ _) offset _elemSize = do
    let sym = backendGetSym bak
    isZero <- liftIO $ bvEq sym offset =<< bvZero sym knownNat
    leafAssert bak isZero $ Unsupported callStack $
        "pointer arithmetic outside arrays is not yet implemented"
    return ref
mirRef_offsetWrapLeaf bak ref@(MirReference_Integer _) offset _elemSize = do
    let sym = backendGetSym bak
    -- Offsetting by zero is a no-op, and is always allowed, even on invalid
    -- pointers.  In particular, this permits `(&[])[0..]`.
    isZero <- liftIO $ bvEq sym offset =<< bvZero sym knownNat
    leafAssert bak isZero $ Unsupported callStack $
        "cannot perform pointer arithmetic on invalid pointer"
    return ref


mirRef_tryOffsetFromLeaf ::
    IsSymBackend sym bak =>
    bak ->
    -- | The size of the pointee type, in bytes
    Word ->
    MirReference sym ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym (MaybeType IsizeType))
mirRef_tryOffsetFromLeaf bak elemSize (MirReference _ root1 path1) (MirReference _ root2 path2) = do
    let sym = backendGetSym bak
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
            -- Use the `elemSize` parameter instead of the element size stored in the
            -- reference path to avoid using a type-incorrect size when
            -- operating on a reference that's been cast to a type that doesn't
            -- match its original representation. (Same rationale as described
            -- in `mirRef_offsetWrapLeaf`.)
            pathEq <- refPathEq sym path1' path2'
            similar <- liftIO $ andPred sym rootEq pathEq
            byteOffset <- liftIO $ bvSub sym off1 off2
            elemSize' <- liftIO $ wordLit sym elemSize
            elemOffset <- liftIO $ bvSdiv sym byteOffset elemSize'

            when (elemSize > 1) $ do
              byteOffset' <- liftIO $ bvMul sym elemOffset elemSize'
              byteOffsetIsSizeMultiple <- liftIO $ bvEq sym byteOffset byteOffset'
              leafAssert bak byteOffsetIsSizeMultiple $
                GenericSimError $
                  "offset_from: byte offset not a multiple of `size_of::<T>` (" <> show elemSize <> ")"

            return $ mkPE similar elemOffset
        _ -> do
            pathEq <- refPathEq sym path1 path2
            similar <- liftIO $ andPred sym rootEq pathEq
            liftIO $ mkPE similar <$> bvZero sym knownNat
mirRef_tryOffsetFromLeaf bak _elemSize (MirReference_Integer i1) (MirReference_Integer i2) = do
    -- Return zero if `i1 == i2`; otherwise, return `Unassigned`.
    --
    -- For more interesting cases, we would need to know the element size to
    -- use in converting the byte offset `i1 - i2` into an element count.
    let sym = backendGetSym bak
    eq <- liftIO $ bvEq sym i1 i2
    liftIO $ mkPE eq <$> bvZero sym knownNat
mirRef_tryOffsetFromLeaf _ _ _ _ = do
    -- MirReference_Integer pointers are always disjoint from all MirReference
    -- pointers, so we report them as being in different objects.
    return Unassigned

mirRef_tryOffsetFromIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    -- | The size of the pointee element, in bytes
    Word ->
    MirReferenceMux sym ->
    MirReferenceMux sym ->
    IO (RegValue sym (MaybeType IsizeType))
mirRef_tryOffsetFromIO bak iTypes elemSize (MirReferenceMux r1) (MirReferenceMux r2) =
    let sym = backendGetSym bak in
    zipFancyMuxTrees' bak (mirRef_tryOffsetFromLeaf bak elemSize)
            (muxRegForType sym iTypes (MaybeRepr IsizeRepr)) r1 r2


mirRef_peelIndexLeaf ::
    MonadAssert sym bak m =>
    bak ->
    -- | The size of the element, in bytes
    Word ->
    MirReference sym ->
    MuxLeafT sym m
        (RegValue sym (StructType (EmptyCtx ::> MirReferenceType ::> UsizeType)))
mirRef_peelIndexLeaf bak _elemSize (MirReference tpr root (VectorIndex_RefPath _tpr' path idx)) = do
    let sym = backendGetSym bak
    let ref = MirReferenceMux $ toFancyMuxTree sym $ MirReference (VectorRepr tpr) root path
    return $ Empty :> RV ref :> RV idx
mirRef_peelIndexLeaf bak _elemSize (MirReference _tpr root (ArrayIndex_RefPath btpr path idx)) = do
    let sym = backendGetSym bak
    let ref = MirReferenceMux $ toFancyMuxTree sym $ MirReference (UsizeArrayRepr btpr) root path
    return $ Empty :> RV ref :> RV idx
mirRef_peelIndexLeaf bak elemSize (MirReference _tpr root (AgElem_RefPath off _sz _tpr' path)) = do
    let sym = backendGetSym bak
    elemSizeBV <- liftIO $ wordLit sym elemSize

    offModSz <- liftIO $ bvUrem sym off elemSizeBV
    offModSzIsZero <- liftIO $ bvEq sym offModSz =<< wordLit sym 0
    leafAssert bak offModSzIsZero $ Unsupported callStack $
        "expected element offset to be a multiple of element size (" ++ show elemSize ++ ")"

    idx <- liftIO $ bvUdiv sym off elemSizeBV
    let ref = MirReferenceMux $ toFancyMuxTree sym $ MirReference MirAggregateRepr root path
    return $ Empty :> RV ref :> RV idx
mirRef_peelIndexLeaf _bak _elemSize (MirReference _ _ _) =
    leafAbort $ Unsupported callStack $
        "peelIndex is not yet implemented for this RefPath kind"
mirRef_peelIndexLeaf _bak _elemSize _ = do
    leafAbort $ Unsupported callStack $
        "cannot perform peelIndex on invalid pointer"

mirRef_peelIndexMA ::
    MonadAssert sym bak m =>
    bak ->
    IntrinsicTypes sym ->
    MirReferenceMux sym ->
    -- | The size of the element, in bytes
    Word ->
    m (RegValue sym (StructType (EmptyCtx ::> MirReferenceType ::> UsizeType)))
mirRef_peelIndexMA bak iTypes (MirReferenceMux ref) elemSize =
    let sym = backendGetSym bak
        tpr' = StructRepr (Empty :> MirReferenceRepr :> IsizeRepr) in
    readFancyMuxTree' bak (mirRef_peelIndexLeaf bak elemSize)
        (muxRegForType sym iTypes tpr') ref


-- | Peel off an outermost 'Field_RefPath'. Given a pointer to a field of a
-- struct, this produces a pointer to the containing struct.
--
-- This function takes in the expected struct type (in the form of the field
-- 'TypeRepr's) and the expected index of the field within the struct. If the
-- 'Field_RefPath' is actually for a different field type or a different index,
-- it will raise an error.
--
-- If the outermost path segment isn't 'Field_RefPath', this operation raises an
-- error. This means that for non-initializable fields which are wrapped in a
-- 'MaybeRepr', you will need to peel off the 'Just_RefPath' first with the
-- @mirRef_peelJust@ family of functions.
mirRef_peelFieldLeaf ::
    (IsSymInterface sym, MonadIO m) =>
    sym ->
    CtxRepr ctx {-^ The expected struct type -} ->
    Index ctx tp {-^ The expected field index -} ->
    MirReference sym {-^ The field pointer -} ->
    MuxLeafT sym m (MirReferenceMux sym)
mirRef_peelFieldLeaf sym fieldReprs idx (MirReference _tpr root path) =
    case path of
      Field_RefPath fieldReprs' path' idx'
        | Just Refl <- testEquality fieldReprs fieldReprs'
        , Just Refl <- testEquality idx idx' ->
          return $ MirReferenceMux $
            toFancyMuxTree sym $ MirReference (StructRepr fieldReprs) root path'
        | otherwise ->
          leafAbort $ Unsupported callStack $
            "peelField type/index mismatch; expected " ++ show (fieldReprs, idx)
            ++ ", but got " ++ show (fieldReprs', idx')
      _ ->
        leafAbort $ Unsupported callStack $
          "peelField not implemented for this RefPath kind"
mirRef_peelFieldLeaf _ _ _ _ =
    leafAbort $ Unsupported callStack $
      "cannot perform peelField on invalid pointer"

mirRef_peelFieldMA ::
    MonadAssert sym bak m =>
    bak ->
    IntrinsicTypes sym ->
    CtxRepr ctx ->
    Index ctx tp ->
    MirReferenceMux sym ->
    m (MirReferenceMux sym)
mirRef_peelFieldMA bak iTypes fieldReprs idx (MirReferenceMux ref) =
    let sym = backendGetSym bak in
    readFancyMuxTree' bak (mirRef_peelFieldLeaf sym fieldReprs idx)
        (muxRegForType sym iTypes MirReferenceRepr) ref


-- | Peel off an outermost 'Just_RefPath'. Given a pointer to a @tp@, this
-- produces a pointer to the containing @MaybeType tp@.
--
-- If the outermost path segment isn't 'Just_RefPath', this operation raises an
-- error.
mirRef_peelJustLeaf ::
    (IsSymInterface sym, MonadIO m) =>
    sym ->
    TypeRepr tp {-^ The type inside the @MaybeType@ -} ->
    MirReference sym ->
    MuxLeafT sym m (MirReferenceMux sym)
mirRef_peelJustLeaf sym tpr ref =
  typedLeafOp "peelJust" tpr ref $ \root path ->
    case path of
      Just_RefPath _ path' ->
        return $ MirReferenceMux $
          toFancyMuxTree sym $ MirReference (MaybeRepr tpr) root path'
      _ ->
        leafAbort $ Unsupported callStack $
          "peelJust not implemented for this RefPath kind"

mirRef_peelJustMA ::
    MonadAssert sym bak m =>
    bak ->
    IntrinsicTypes sym ->
    TypeRepr tp ->
    MirReferenceMux sym ->
    m (MirReferenceMux sym)
mirRef_peelJustMA bak iTypes tpr (MirReferenceMux ref) =
    let sym = backendGetSym bak in
    readFancyMuxTree' bak (mirRef_peelJustLeaf sym tpr)
        (muxRegForType sym iTypes MirReferenceRepr) ref


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
    -- | The size of the pointee element, in bytes
    Word ->
    MirReference sym ->
    MuxLeafT sym IO (RegValue sym UsizeType, RegValue sym UsizeType)
mirRef_indexAndLenLeaf bak gs iTypes _elemSize (MirReference tpr root (VectorIndex_RefPath _tpr' path idx)) = do
    let sym = backendGetSym bak
    let parentTpr = VectorRepr tpr
    let parent = MirReference parentTpr root path
    parentVec <- readMirRefLeaf bak gs iTypes parentTpr parent
    let lenInteger = toInteger $ V.length parentVec
    len <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat lenInteger
    return (idx, len)
mirRef_indexAndLenLeaf _bak _gs _iTypes _elemSize (MirReference _tpr _root (ArrayIndex_RefPath {})) =
    leafAbort $ Unsupported callStack
        "can't compute allocation length for Array, which is unbounded"
mirRef_indexAndLenLeaf bak gs iTypes elemSize (MirReference _tpr root (AgElem_RefPath elemOff _elemSize _tpr' path)) = do
    -- Use an `elemSize` parameter instead of the element size stored in the
    -- reference path to avoid using a type-incorrect size when operating on a
    -- reference that's been cast to a type that doesn't match its original
    -- representation. (Same rationale as described in `mirRef_offsetWrapLeaf`.)
    let sym = backendGetSym bak
    let parentTpr = MirAggregateRepr
    let parent = MirReference parentTpr root path
    parentAg <- readMirRefLeaf bak gs iTypes parentTpr parent
    let MirAggregate totalSize _ = parentAg
    when (totalSize `mod` elemSize /= 0) $
       leafAbort $ Unsupported callStack $
           "expected aggregate size (" ++ show totalSize ++ ") to be a multiple of "
               ++ "element size (" ++ show elemSize ++ ")"
    let lenWord = totalSize `div` elemSize
    len <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat $ fromIntegral lenWord

    elemSizeBV <- liftIO $ wordLit sym elemSize
    offModSz <- liftIO $ bvUrem sym elemOff elemSizeBV
    offModSzIsZero <- liftIO $ bvEq sym offModSz =<< wordLit sym 0
    leafAssert bak offModSzIsZero $ Unsupported callStack $
        "expected element offset to be a multiple of element size (" ++ show elemSize ++ ")"

    offDivSz <- liftIO $ bvUdiv sym elemOff elemSizeBV
    return (offDivSz, len)
mirRef_indexAndLenLeaf bak _ _ _elemSize (MirReference _ _ _) = do
    let sym = backendGetSym bak
    idx <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat 0
    len <- liftIO $ bvLit sym knownNat $ BV.mkBV knownNat 1
    return (idx, len)
mirRef_indexAndLenLeaf bak _ _ _elemSize (MirReference_Integer _) = do
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
    -- | The size of the pointee element, in bytes
    Word ->
    IO (PartExpr (Pred sym) (RegValue sym UsizeType, RegValue sym UsizeType))
mirRef_indexAndLenIO bak gs iTypes (MirReferenceMux ref) elemSize = do
    let sym = backendGetSym bak
    readPartialFancyMuxTree bak
        (mirRef_indexAndLenLeaf bak gs iTypes elemSize)
        (\c (tIdx, tLen) (eIdx, eLen) -> do
            idx <- baseTypeIte sym c tIdx eIdx
            len <- baseTypeIte sym c tLen eLen
            return (idx, len))
        ref

mirRef_indexAndLenSim ::
    IsSymInterface sym =>
    MirReferenceMux sym ->
    -- | The size of the pointee element, in bytes
    Word ->
    OverrideSim p sym ext rtp args ret
        (PartExpr (Pred sym) (RegValue sym UsizeType, RegValue sym UsizeType))
mirRef_indexAndLenSim ref elemSize = do
  ovrWithBackend $ \bak ->
    do s <- get
       let gs = s ^. stateTree.actFrame.gpGlobals
       let iTypes = ctxIntrinsicTypes $ s ^. stateContext
       liftIO $ mirRef_indexAndLenIO bak gs iTypes ref elemSize


mirRef_aggregateAsChunksLeaf ::
    IsSymInterface sym =>
    RegValue sym UsizeType ->
    RegValue sym UsizeType ->
    MirReference sym ->
    MuxLeafT sym IO (MirReference sym)
mirRef_aggregateAsChunksLeaf chunkSizeSym numChunksSym
        (MirReference _tpr root (AgElem_RefPath offSym _sz _tpr' path)) = do
    chunkSize <- requireConcrete "chunk size" chunkSizeSym
    numChunks <- requireConcrete "number of chunks" numChunksSym
    off <- requireConcrete "slice offset within parent array" offSym
    return $ MirReference MirAggregateRepr root
      (AggregateAsChunks_RefPath off chunkSize numChunks path)
  where
    requireConcrete desc symExp =
      case asBV symExp of
        Just bv -> return $ fromIntegral $ BV.asUnsigned bv
        Nothing -> leafAbort $ GenericSimError $
          "aggregateAsChunks requires " ++ desc ++ " to be concrete"
mirRef_aggregateAsChunksLeaf _ _ (MirReference _ _ _) =
    leafAbort $ Unsupported callStack $
        "aggregateAsChunks requires a pointer to an aggregate element (AgElem_RefPath)"
mirRef_aggregateAsChunksLeaf _ _ _ = do
    leafAbort $ Unsupported callStack $
        "cannot perform aggregateAsChunks on invalid pointer"

mirRef_aggregateAsChunksIO ::
    IsSymBackend sym bak =>
    bak ->
    IntrinsicTypes sym ->
    RegValue sym UsizeType ->
    RegValue sym UsizeType ->
    MirReferenceMux sym ->
    IO (MirReferenceMux sym)
mirRef_aggregateAsChunksIO bak iTypes chunkSizeSym numChunksSym ref =
    modifyRefMuxMA bak iTypes (mirRef_aggregateAsChunksLeaf chunkSizeSym numChunksSym) ref
