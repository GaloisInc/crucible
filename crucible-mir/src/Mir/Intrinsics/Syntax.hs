{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

-- TODO(#1786): refine exports, if necessary
module Mir.Intrinsics.Syntax
  ( MIR,
    MirStmt (..),
    traverseMirStmt,
    execMirStmt,
  )
where

import GHC.TypeLits (type (<=))

import Control.Lens ((&), (.~), (^.))

import Data.Kind (Type)
import Data.Parameterized.Classes (OrdF (..), TestEquality (..))
import Data.Parameterized.Context
  ( Assignment,
    EmptyCtx,
    Index,
    (::>),
    pattern Empty,
    pattern (:>),
  )
import Data.Parameterized.NatRepr (NatRepr)
import Data.Parameterized.Some (Some)
import Data.Parameterized.TH.GADT qualified as U
import Data.Parameterized.TraversableFC
  ( FoldableFC (..),
    FunctorFC (..),
    OrdFC (..),
    TestEqualityFC (..),
    TraversableFC (..),
    fmapFCDefault,
    foldMapFCDefault,
  )
import Data.Vector qualified as V

import Prettyprinter (pretty, viaShow, (<+>))

import What4.Interface (printSymExpr)
import What4.Partial (maybePartExpr)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.CFG.Common (GlobalVar, globalType)
import Lang.Crucible.CFG.Extension
  ( EmptyExprExtension,
    ExprExtension,
    IsSyntaxExtension,
    PrettyApp (..),
    StmtExtension,
    TypeApp (..),
  )
import Lang.Crucible.Simulator
  ( EvalStmtFunc,
    SimState,
    SymGlobalState,
    regValue,
  )
import Lang.Crucible.Simulator.ExecutionTree
  ( actFrame,
    ctxIntrinsicTypes,
    ctxSymInterface,
    gpGlobals,
    simHandleAllocator,
    stateContext,
    stateTree,
    withStateBackend,
  )
import Lang.Crucible.Types
  ( BaseBVType,
    BaseTypeRepr,
    BoolType,
    CrucibleType,
    CtxRepr,
    MaybeType,
    NatType,
    StringType,
    StructType,
    SymbolicArrayType,
    TypeRepr (..),
    Unicode,
    UnitType,
    VectorType,
    pattern BaseBVRepr,
  )

import Mir.FancyMuxTree (toFancyMuxTree)
import Mir.Intrinsics.Aggregate
  ( MirAggregateType,
    mirAggregate_getIO,
    mirAggregate_replicateIO,
    mirAggregate_resizeIO,
    mirAggregate_setIO,
    mirAggregate_uninitIO,
    pattern MirAggregateRepr,
  )
import Mir.Intrinsics.Array (arrayZeroedIO)
import Mir.Intrinsics.Reference
  ( MirReference (..),
    MirReferenceMux (..),
    MirReferencePath (..),
    MirReferenceRoot (..),
    MirReferenceType,
    dropMirRefIO,
    mirRef_agElemIO,
    mirRef_aggregateAsChunksIO,
    mirRef_eqIO,
    mirRef_offsetMA,
    mirRef_offsetWrapIO,
    mirRef_peelIndexMA,
    mirRef_tryOffsetFromIO,
    newMirRefIO,
    readMirRefMA,
    subfieldMirRefIO,
    subfieldMirRef_UntypedIO,
    subindexMirRefIO,
    subjustMirRefIO,
    subvariantMirRefIO,
    writeMirRefIO,
    pattern MirReferenceRepr,
  )
import Mir.Intrinsics.Size
  ( IsizeType,
    UsizeType,
    pattern IsizeRepr,
    pattern UsizeRepr,
  )
import Mir.Intrinsics.Vector (vectorDropIO, vectorTakeIO)

-- | Sigil type indicating the MIR syntax extension
data MIR

type instance ExprExtension MIR = EmptyExprExtension
type instance StmtExtension MIR = MirStmt

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
     -- | The number of elements by which to offset
     !(f IsizeType) ->
     -- | The size of each element, i.e. @size_of::<T>@
     !Word ->
     MirStmt f MirReferenceType
  -- Rust `ptr::wrapping_offset`.  Steps by `count` units of `size_of::<T>`,
  -- with no additional restrictions.
  MirRef_OffsetWrap ::
     !(f MirReferenceType) ->
     -- | The number of elements by which to offset
     !(f IsizeType) ->
     -- | The size of each element, i.e. @size_of::<T>@
     !Word ->
     MirStmt f MirReferenceType
  -- | Try to subtract two references, as in `pointer::offset_from`.  If both
  -- point into the same array, return their difference; otherwise, return
  -- Nothing.  The `Nothing` result is useful for overlap checks: slices from
  -- different arrays cannot overlap.
  MirRef_TryOffsetFrom ::
     !(f MirReferenceType) ->
     !(f MirReferenceType) ->
     -- | The size of the pointee, i.e. @size_of::<T>@
     !Word ->
     MirStmt f (MaybeType IsizeType)
  -- | Peel off an outermost `Index_RefPath`.  Given a pointer to an element of
  -- a vector, this produces a pointer to the parent vector and the index of
  -- the element.  If the outermost path segment isn't `Index_RefPath`, this
  -- operation raises an error.
  MirRef_PeelIndex ::
     !(f MirReferenceType) ->
     -- | The size of the element, in bytes
     !Word ->
     MirStmt f (StructType (EmptyCtx ::> MirReferenceType ::> UsizeType))
  -- | Given a pointer to an element, return a pointer to an array constructed
  -- by viewing the next @chunkSize * numChunks@ elements as an array of
  -- arrays.
  MirRef_AggregateAsChunks ::
     -- | Size in bytes of each chunk (must be concrete)
     !(f UsizeType) ->
     -- | Number of chunks to produce (must be concrete)
     !(f UsizeType) ->
     !(f MirReferenceType) ->
     MirStmt f MirReferenceType
  -- | Print the internal representation of a `MirReference` for debugging.
  -- This is similar to the behavior of @crucible::dump_rv@, but it's easier to
  -- call an intrinsic from inside `Mir.Trans` / `Mir.TransCustom` cases than
  -- it is to call a Rust function.
  --
  -- This could likely be expanded to accept all `RegValue`s (not just
  -- `MirReferenceType`) in the future if needed.
  DebugPrintMirRef ::
     !(f (StringType Unicode)) ->
     !(f MirReferenceType) ->
     MirStmt f UnitType
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
    MirRef_Offset _ _ _ -> MirReferenceRepr
    MirRef_OffsetWrap _ _ _ -> MirReferenceRepr
    MirRef_TryOffsetFrom _ _ _ -> MaybeRepr IsizeRepr
    MirRef_PeelIndex _ _ -> StructRepr (Empty :> MirReferenceRepr :> UsizeRepr)
    MirRef_AggregateAsChunks _ _ _ -> MirReferenceRepr
    DebugPrintMirRef _ _ -> UnitRepr
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
    MirRef_Offset p o s -> "mirRef_offset" <+> pp p <+> pp o <+> viaShow s
    MirRef_OffsetWrap p o s -> "mirRef_offsetWrap" <+> pp p <+> pp o <+> viaShow s
    MirRef_TryOffsetFrom p o s -> "mirRef_tryOffsetFrom" <+> pp p <+> pp o <+> viaShow s
    MirRef_PeelIndex p s -> "mirRef_peelIndex" <+> pp p <+> viaShow s
    MirRef_AggregateAsChunks chunkSize numChunks p -> "mirRef_aggregateAsChunks" <+> pp chunkSize <+> pp numChunks <+> pp p
    DebugPrintMirRef s p -> "debugPrintMirRef" <+> pp s <+> pp p
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


execMirStmt :: forall p sym. IsSymInterface sym => EvalStmtFunc p sym MIR
execMirStmt stmt s = withStateBackend s $ \bak ->
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
         readOnly s $ readMirRefMA bak gs iTypes tpr ref
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
       MirRef_Offset (regValue -> ref) (regValue -> off) elemSize ->
         readOnly s $ mirRef_offsetMA bak iTypes ref off elemSize
       MirRef_OffsetWrap (regValue -> ref) (regValue -> off) elemSize ->
         readOnly s $ mirRef_offsetWrapIO bak iTypes ref off elemSize
       MirRef_TryOffsetFrom (regValue -> r1) (regValue -> r2) elemSize ->
         readOnly s $ mirRef_tryOffsetFromIO bak iTypes elemSize r1 r2
       MirRef_PeelIndex (regValue -> ref) elemSize -> do
         readOnly s $ mirRef_peelIndexMA bak iTypes ref elemSize
       MirRef_AggregateAsChunks (regValue -> chunkSize) (regValue -> numChunks) (regValue -> ref) -> do
         readOnly s $ mirRef_aggregateAsChunksIO bak iTypes chunkSize numChunks ref
       DebugPrintMirRef (regValue -> desc) (regValue -> ref) -> do
         readOnly s $ putStrLn $ "debugPrintMirRef (" ++ show (printSymExpr desc)
           ++ "): " ++ show ref

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
