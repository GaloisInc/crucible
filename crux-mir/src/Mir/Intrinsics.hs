{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}

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
, TaggedUnion
, MirSlice
, pattern MirSliceRepr
  -- * Translation-specific types
, VarMap
, VarInfo (..)
, varInfoRepr
, LabelMap
, AdtMap
, TraitMap (..)
, TraitImpls (..)
, vtableTyRepr
, methodIndex
, vtables
, traitImpls
, FnState (..)
, MirExp (..)
, MirHandle (..)
, HandleMap
, varMap
, labelMap
, adtMap
, handleMap
, traitMap
, MirValue(..)
, valueToExpr
  , getTraitImplementation  
  -- * MIR Syntax extension
, MIR
, MirStmt(..)
, mirExtImpl
) -} where

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

import qualified Text.Regex as Regex
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.TH.GADT as U

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Expr
--import           Lang.Crucible.CFG.Extension
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

import           What4.Interface
import           What4.Utils.MonadST

import           Mir.DefId
import           Mir.Mir
import           Mir.PP

import           Debug.Trace

import           Unsafe.Coerce

-- A MirReference is a Crucible RefCell paired with a path to a subcomponent

type MirReferenceSymbol = "MirReference"
type MirReferenceType tp = IntrinsicType MirReferenceSymbol (EmptyCtx ::> tp)

pattern MirReferenceRepr :: () => tp' ~ MirReferenceType tp => TypeRepr tp -> TypeRepr tp'
pattern MirReferenceRepr tp <-
     IntrinsicRepr (testEquality (knownSymbol @MirReferenceSymbol) -> Just Refl) (Empty :> tp)
 where MirReferenceRepr tp = IntrinsicRepr (knownSymbol @MirReferenceSymbol) (Empty :> tp)

type family MirReferenceFam (sym :: *) (ctx :: Ctx CrucibleType) :: * where
  MirReferenceFam sym (EmptyCtx ::> tp) = MirReference sym tp
  MirReferenceFam sym ctx = TypeError ('Text "MirRefeence expects a single argument, but was given" ':<>:
                                       'ShowType ctx)
instance IsExprBuilder sym => IntrinsicClass sym MirReferenceSymbol where
  type Intrinsic sym MirReferenceSymbol ctx = MirReferenceFam sym ctx

  muxIntrinsic sym _tys _nm (Empty :> _tp) = muxRef sym
  muxIntrinsic _sym _tys nm ctx = typeError nm ctx

data MirReferencePath sym :: CrucibleType -> CrucibleType -> * where
  Empty_RefPath :: MirReferencePath sym tp tp
  Field_RefPath ::
    !(CtxRepr ctx) ->
    !(MirReferencePath sym tp_base TaggedUnion) ->
    !(Index ctx tp) ->
    MirReferencePath sym tp_base tp
  Index_RefPath ::
    !(TypeRepr tp) ->
    !(MirReferencePath sym tp_base (VectorType tp)) ->
    !(RegValue sym NatType) ->
    MirReferencePath sym tp_base tp

data MirReference sym (tp :: CrucibleType) where
  MirReference ::
    !(RefCell tpr) ->
    !(MirReferencePath sym tpr tp) ->
    MirReference sym tp

muxRefPath ::
  IsExprBuilder sym =>
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
  (Index_RefPath tp p1 i1, Index_RefPath _ p2 i2) ->
         do p' <- muxRefPath sym c p1 p2
            i' <- lift $ natIte sym c i1 i2
            return (Index_RefPath tp p' i')
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
    do Refl <- MaybeT (return $ testEquality (refType r1) (refType r2))
       Refl <- MaybeT (return $ testEquality r1 r2)
       p' <- muxRefPath sym c p1 p2
       return (MirReference r1 p')

-- | Sigil type indicating the MIR syntax extension
data MIR
type instance ExprExtension MIR = EmptyExprExtension
type instance StmtExtension MIR = MirStmt
type instance Instantiate subst MIR = MIR
instance Closed MIR where closed _ = Refl

type TaggedUnion = StructType (EmptyCtx ::> NatType ::> AnyType)

data MirStmt :: (CrucibleType -> *) -> CrucibleType -> * where
  MirNewRef ::
     !(TypeRepr tp) ->
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
  MirSubfieldRef ::
     !(CtxRepr ctx) ->
     !(f (MirReferenceType TaggedUnion)) ->
     !(Index ctx tp) ->
     MirStmt f (MirReferenceType tp)
  MirSubindexRef ::
     !(TypeRepr tp) ->
     !(f (MirReferenceType (VectorType tp))) ->
     !(f NatType) ->
     MirStmt f (MirReferenceType tp)

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
       , (U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testEquality|])
       ])
instance TestEquality f => TestEquality (MirStmt f) where
  testEquality = testEqualityFC testEquality

instance OrdFC MirStmt where
  compareFC compareSubterm =
    $(U.structuralTypeOrd [t|MirStmt|]
       [ (U.DataArg 0 `U.TypeApp` U.AnyType, [|compareSubterm|])
       , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareF|])
       ])
instance OrdF f => OrdF (MirStmt f) where
  compareF = compareFC compareF

instance TypeApp MirStmt where
  appType = \case
    MirNewRef tp    -> MirReferenceRepr tp
    MirReadRef tp _ -> tp
    MirWriteRef _ _ -> UnitRepr
    MirDropRef _    -> UnitRepr
    MirSubfieldRef ctx _ idx -> MirReferenceRepr (ctx ! idx)
    MirSubindexRef tp _ _ -> MirReferenceRepr tp

instance PrettyApp MirStmt where
  ppApp pp = \case 
    MirNewRef tp -> "newMirRef" <+> pretty tp
    MirReadRef _ x  -> "readMirRef" <+> pp x
    MirWriteRef x y -> "writeMirRef" <+> pp x <+> "<-" <+> pp y
    MirDropRef x    -> "dropMirRef" <+> pp x
    MirSubfieldRef _ x idx -> "subfieldRef" <+> pp x <+> text (show idx)
    MirSubindexRef _ x idx -> "subindexRef" <+> pp x <+> pp idx

instance FunctorFC MirStmt where
  fmapFC = fmapFCDefault
instance FoldableFC MirStmt where
  foldMapFC = foldMapFCDefault
instance TraversableFC MirStmt where
  traverseFC = traverseMirStmt

type instance Instantiate subst MirStmt = MirStmt
instance Closed MirStmt where closed _ = Refl
instance InstantiateFC MirStmt where
  instantiateFC subst stmt =
    case stmt of
      MirNewRef t -> MirNewRef (instantiate subst t)
      MirReadRef t r -> MirReadRef (instantiate subst t) (instantiate subst r)
      MirWriteRef r1 r2 -> MirWriteRef (instantiate subst r1) (instantiate subst r2)
      MirDropRef r1 -> MirDropRef (instantiate subst r1)
      MirSubfieldRef ctx r1 idx -> MirSubfieldRef (instantiate subst ctx) (instantiate subst r1) (instantiate subst idx)
      MirSubindexRef ty r1 idx -> MirSubindexRef (instantiate subst ty) (instantiate subst r1) (instantiate subst idx)      

instance IsSyntaxExtension MIR

execMirStmt :: IsSymInterface sym => EvalStmtFunc p sym MIR
execMirStmt stmt s =
  let ctx = s^.stateContext
      sym = ctx^.ctxSymInterface
      halloc = simHandleAllocator ctx
      iTypes = ctxIntrinsicTypes ctx
  in case stmt of
       MirNewRef tp ->
         do r <- liftST (freshRefCell halloc tp)
            let r' = MirReference r Empty_RefPath
            return (r', s)

       MirDropRef (regValue -> MirReference r path) ->
         case path of
           Empty_RefPath ->
             do let s' = s & stateTree . actFrame . gpGlobals %~ dropRef r
                return ((), s')
           _ -> addFailedAssertion sym (GenericSimError "Cannot drop an interior reference")

       MirReadRef _tp (regValue -> MirReference r path) ->
         do let msg = ReadBeforeWriteSimError
                       "Attempted to read uninitialized reference cell"
            v <- readPartExpr sym (lookupRef r (s ^. stateTree . actFrame . gpGlobals)) msg
            v' <- readRefPath sym iTypes v path
            return (v', s)

       MirWriteRef (regValue -> MirReference r Empty_RefPath) (regValue -> x) ->
         do let s' = s & stateTree . actFrame . gpGlobals %~ insertRef sym r x
            return ((), s')
       MirWriteRef (regValue -> MirReference r path) (regValue -> x) ->
         do let msg = ReadBeforeWriteSimError
                       "Attempted to read uninitialized reference cell"
            v <- readPartExpr sym (lookupRef r (s ^. stateTree . actFrame . gpGlobals)) msg
            v' <- writeRefPath sym iTypes v path x
            let s' = s & stateTree . actFrame . gpGlobals %~ insertRef sym r v'
            return ((), s')
       MirSubfieldRef ctx0 (regValue -> MirReference r path) idx ->
         do let r' = MirReference r (Field_RefPath ctx0 path idx)
            return (r', s)
       MirSubindexRef tp (regValue -> MirReference r path) (regValue -> idx) ->
         do let r' = MirReference r (Index_RefPath tp path idx)
            return (r', s)

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
  Field_RefPath ctx path fld ->
      adjustRefPath sym iTypes v path (field @1 (\(RV (AnyValue vtp x)) ->
         case testEquality vtp (StructRepr ctx) of
           Nothing -> fail ("Variant type mismatch! Expected: " ++ show (StructRepr ctx) ++
                            "\nbut got: " ++ show vtp)
           Just Refl -> RV . AnyValue vtp <$> adjustM (\x' -> RV <$> adj (unRV x')) fld x
         ))

  Index_RefPath tp path idx ->
      adjustRefPath sym iTypes v path (\v' ->
        adjustVectorWithSymNat sym (muxRegForType sym iTypes tp) v' idx adj)


readRefPath :: IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  RegValue sym tp ->
  MirReferencePath sym tp tp' ->
  IO (RegValue sym tp')
readRefPath sym iTypes v = \case
  Empty_RefPath -> return v
  Field_RefPath ctx path fld ->
    do (Empty :> _disc :> RV (AnyValue vtp variant)) <- readRefPath sym iTypes v path
       case testEquality vtp (StructRepr ctx) of
         Nothing -> fail ("Variant type mismatch expected: " ++ show (StructRepr ctx) ++ 
                           "\nbut got: " ++ show vtp)
         Just Refl -> return (unRV (variant ! fld))
  Index_RefPath tp path idx ->
    do v' <- readRefPath sym iTypes v path
       indexVectorWithSymNat sym (muxRegForType sym iTypes tp) v' idx


mirExtImpl :: forall sym p. IsSymInterface sym => ExtensionImpl p sym MIR
mirExtImpl = ExtensionImpl
             { extensionEval = \_sym -> \case
             , extensionExec = execMirStmt
             }

--------------------------------------------------------------------------------

type MirSlice tp     = StructType (EmptyCtx ::>
                           MirReferenceType (VectorType tp) ::>
                           NatType ::>    --- lower bound
                           NatType)       --- upper bound

pattern MirSliceRepr :: () => tp' ~ MirSlice tp => TypeRepr tp -> TypeRepr tp'
pattern MirSliceRepr tp <- StructRepr
     (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignEmpty)
         (MirReferenceRepr (VectorRepr tp)))
         NatRepr)
         NatRepr)
 where MirSliceRepr tp = StructRepr (Empty :> MirReferenceRepr (VectorRepr tp) :> NatRepr :> NatRepr)

mirSliceCtxRepr :: TypeRepr tp -> CtxRepr (EmptyCtx ::>
                           MirReferenceType (VectorType tp) ::>
                           NatType ::> 
                           NatType)  
mirSliceCtxRepr tp = (Empty :> MirReferenceRepr (VectorRepr tp) :> NatRepr :> NatRepr)

getSliceLB :: Expr MIR s (MirSlice tp) -> Expr MIR s NatType
getSliceLB e = getStruct i2of3 e 

getSliceLen :: Expr MIR s (MirSlice tp) -> Expr MIR s NatType
getSliceLen e = getStruct i3of3 e

updateSliceLB :: TypeRepr tp -> Expr MIR s (MirSlice tp) -> Expr MIR s NatType ->  Expr MIR s (MirSlice tp)
updateSliceLB tp e start = setStruct (mirSliceCtxRepr tp) e i2of3 ns where
   os = getStruct i2of3 e
   ns = os .+ start

updateSliceLen :: TypeRepr tp -> Expr MIR s (MirSlice tp) -> Expr MIR s NatType -> Expr MIR s (MirSlice tp)
updateSliceLen tp e end = setStruct (mirSliceCtxRepr tp) e i3of3 end where
--   oe = getStruct i3of3 e
--   ne = oe .- end 


--------------------------------------------------------------------------------
-- ** Generator state for MIR translation to Crucible
--
-- | Generator state for MIR translation
data FnState (s :: Type)
  = FnState { _varMap    :: !(VarMap s),
              _labelMap  :: !(LabelMap s),
              _handleMap :: !HandleMap,
              _adtMap    :: !AdtMap,
              _traitMap  :: !(TraitMap s),
              _staticTraitMap :: !StaticTraitMap,
              _debugLevel :: !Int,
              _preds     :: [Predicate]
            }


---------------------------------------------------------------------------
-- *** VarMap

-- | The VarMap maps identifier names to registers (if the id
--   corresponds to a local variable) or an atom (if the id
--   corresponds to a function argument)
type VarMap s = Map Text.Text (Some (VarInfo s))
data VarInfo s tp where
  VarRegister  :: Reg s tp -> VarInfo s tp
  VarReference :: Reg s (MirReferenceType tp) -> VarInfo s tp
  VarAtom      :: Atom s tp -> VarInfo s tp

varInfoRepr :: VarInfo s tp -> TypeRepr tp
varInfoRepr (VarRegister reg0)  = typeOfReg reg0
varInfoRepr (VarReference reg0) =
  case typeOfReg reg0 of
    MirReferenceRepr tp -> tp
    _ -> error "impossible: varInfoRepr"
varInfoRepr (VarAtom a) = typeOfAtom a

-- *** LabelMap

-- | The LabelMap maps identifiers to labels of their corresponding basicblock
type LabelMap s = Map.Map BasicBlockInfo (Label s)


-- *** HandleMap

data MirHandle where
    MirHandle :: MethName -> FnSig -> [Predicate] -> FnHandle init ret -> MirHandle

instance Show MirHandle where
    show (MirHandle _nm sig preds c) = show c ++ ":" ++ show sig ++ " where " ++ show preds

instance Pretty MirHandle where
    pretty (MirHandle nm sig preds _c) = text (show nm) <> colon <> pretty sig <+> text "where" <+> pretty preds

-- | The HandleMap maps mir functions to their corresponding function
-- handle. Function handles include the original method name (for
-- convenience) and original Mir type (for trait resolution).
type HandleMap = Map.Map MethName MirHandle

-- *** AdtMap

-- | The AdtMap maps ADT names to their definitions
type AdtMap = Map.Map AdtName [Variant]

-- *** TraitMap and StaticTraitMap

-- | A TraitMap maps trait names to their vtables and instances
data TraitMap (s::Type) = TraitMap (Map TraitName (Some (TraitImpls s)))

-- | A StaticTraitMap maps trait method names to all traits that contain them
-- (There could be multiple, and will need to use type info to resolve further)
type StaticTraitMap = Map.Map MethName [TraitName]


-- | The implementation of a Trait.
-- The 'ctx' parameter lists the required members of the trait
-- NOTE: the vtables are an instance of the more general type
-- listed in the vtableTyRepr
data TraitImpls (s::Type) ctx = TraitImpls
  {_vtableTyRepr :: CtxRepr ctx
   -- ^ Describes the types of Crucible structs that store the VTable
   -- of implementations
  ,_methodIndex :: Map MethName (Some (Index ctx))
   -- ^ Tells which fields (indices) of the struct correspond to
   -- method names of the given trait
  ,_vtables :: Map Ty (Assignment (MirValue s) ctx)
   -- ^ gives the vtable for each type implementing a given trait
   -- the type Ty may have free type variables, in which case the lookup
   -- function will match against the type to resolve the instance 
  }


-- Map 0 -> implTy and decrement all other type variables
--type ImplementSubst implTy = ('ExtendSubst implTy 'IdSubst)
--implementSubst :: TypeRepr implTy -> SubstRepr (ImplementSubst implTy)
--implementSubst implTy = ExtendRepr implTy IdRepr

type family ImplementTrait (implSubst :: Substitution) (arg :: k) :: k where
  -- Ctx k
  ImplementTrait implSubst EmptyCtx = EmptyCtx
  ImplementTrait implSubst (ctx ::> ty) = ImplementTrait implSubst ctx ::> ImplementTrait implSubst ty
  -- CrucibleType
  ImplementTrait implSubst (PolyFnType k args ret) =
      PolyFnType k  (Instantiate implSubst args) (Instantiate implSubst ret )
-- ImplementTrait implSubst (ty :: CrucibleType)  = Instantiate implSubst ty                                               

implementRepr :: SubstRepr implSubst -> TypeRepr ty -> TypeRepr (ImplementTrait implSubst ty)
implementRepr implSubst (PolyFnRepr k args ret) =
  PolyFnRepr k (instantiate implSubst args) (instantiate implSubst ret)
--implementRepr implSubst ty = instantiate implSubst ty

implementCtxRepr :: SubstRepr implSubst -> CtxRepr ctx -> CtxRepr (ImplementTrait implSubst ctx)
implementCtxRepr _implSubst Empty = Empty
implementCtxRepr implSubst (ctx :> ty) = implementCtxRepr implSubst ctx :> implementRepr implSubst ty

implementIdx :: SubstRepr implSubst -> Index ctx a -> Index (ImplementTrait implSubst ctx) (ImplementTrait implSubst a)
implementIdx _implSubst idx = unsafeCoerce idx

-- | Compute the type of values stored in the vtables. 
-- This type must be a specialization of the expected type of the vtable
data MirValue s ty where
  MirValue :: SubstRepr implSubst
           -> TypeRepr   (ImplementTrait implSubst ty)
           -> Expr MIR s (ImplementTrait implSubst ty)  
           -> MirValue s ty

valueToExpr :: SubstRepr implSubst -> MirValue s ty -> Expr MIR s (ImplementTrait implSubst ty)
valueToExpr wantedImpl (MirValue implRepr _ e)
  | Just Refl <- testEquality wantedImpl implRepr
  = e
  | otherwise 
  = error $ "Invalid implementation type. "

vtblToStruct :: SubstRepr implSubst -> Assignment (MirValue s) ctx
             -> Assignment (Expr MIR s) (ImplementTrait implSubst ctx)
vtblToStruct _implSubst Empty = Empty
vtblToStruct implSubst (ctx :> val) = vtblToStruct implSubst ctx :> valueToExpr implSubst val

------------------------------------------------------------------------------------
-- ** Working with generic traits (i.e. not specialized to any particular translation)

data GenericMirValue ty    = GenericMirValue   (forall (s::Type). MirValue s ty)
data GenericTraitImpls ctx = GenericTraitImpls (forall (s::Type). TraitImpls s ctx)
data GenericTraitMap       = GenericTraitMap   (forall (s::Type). Map TraitName (Some (TraitImpls s)))


mkGenericTraitMap :: [(TraitName,Some GenericTraitImpls)] -> GenericTraitMap
mkGenericTraitMap [] = GenericTraitMap Map.empty
mkGenericTraitMap ((tn,Some (GenericTraitImpls impls)):rest) =
  case mkGenericTraitMap rest of
    GenericTraitMap m ->
      GenericTraitMap (Map.insert tn (Some impls) m)

mkGenericTraitImpls ::  CtxRepr ctx
           -> Map.Map MethName (Some (Index ctx))
           -> Map.Map Ty (Assignment GenericMirValue ctx)
           -> GenericTraitImpls ctx
mkGenericTraitImpls str midx vtbls' =
  GenericTraitImpls $
  let g (GenericMirValue mv) = mv
      vtbls = fmap (fmapFC g) vtbls'
  in
    TraitImpls {_vtableTyRepr = str
               ,_methodIndex  = midx
               ,_vtables      = vtbls
               }


mkStaticTraitMap :: [(TraitName,Some GenericTraitImpls)] -> Map.Map MethName [TraitName]
mkStaticTraitMap impls = foldr g Map.empty impls where
  g :: (TraitName, Some GenericTraitImpls) -> StaticTraitMap -> StaticTraitMap
  g (tn, Some (GenericTraitImpls (TraitImpls _ mi _))) stm =
    let meths = Map.keys mi in
      foldr (\n m -> Map.insertWith (++) n [tn] m) stm meths

-- | The main data type for values, bundling the term-level type tp along with a crucible expression of type tp.
data MirExp s where
    MirExp :: TypeRepr tp -> Expr MIR s tp -> MirExp s
instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)
   

addVTable :: forall s implSubst. TraitName -> Ty -> SubstRepr implSubst -> [ (MethName, MirExp s) ] -> TraitMap s -> TraitMap s
addVTable tname ty implSubst meths (TraitMap tm) =
  case Map.lookup tname tm of
    Nothing -> error "Trait not found"
    Just (Some (timpl@(TraitImpls ctxr _mi vtab))) ->
      let go :: Index ctx ty -> TypeRepr ty -> Identity (MirValue s ty)
          go idx tyr2 = do
            let i = indexVal idx
            let (_implName, smv) = if i < length meths then meths !! i else error "impl_vtable: BUG"
            case smv of
              (MirExp tyr e) ->                
                case testEquality tyr (implementRepr implSubst tyr2)  of
                  Just Refl -> return (MirValue implSubst tyr e)
                  Nothing   -> error "Invalid type for addVTable"
                   
          asgn'  = runIdentity (traverseWithIndex go ctxr)
          timpl' = timpl { _vtables = Map.insert ty asgn' vtab } in
      TraitMap (Map.insert tname (Some timpl') tm)
         

------------------------------------------------------------------------------------
-- ** helper function for traits


-- | Smart constructor
traitImpls :: CtxRepr ctx
           -> Map.Map MethName (Some (Index ctx))
           -> Map.Map Ty (Assignment (MirValue s) ctx)
           -> TraitImpls s ctx
traitImpls str midx vtbls =
  TraitImpls {_vtableTyRepr = str
             ,_methodIndex  = midx
             ,_vtables      = vtbls
             }

combineMaps :: Map Integer Ty -> Map Integer Ty -> Maybe (Map Integer Ty)
combineMaps m1 m2 = Map.foldrWithKey go (Just m2) m1 where
  go :: Integer -> Ty -> Maybe (Map Integer Ty) -> Maybe (Map Integer Ty)
  go _k _ty Nothing = Nothing
  go k ty (Just res) =
    case Map.lookup k res of
      Just ty' -> if ty == ty' then Just res else Nothing
      Nothing ->  Just (Map.insert k ty res)

-- | Try to match an implementation type against a trait type
matchSig :: FnSig -> FnSig -> Maybe (Map Integer Ty)
matchSig (FnSig instArgs instRet) (FnSig genArgs genRet) = do
  m1 <- matchTys instArgs genArgs
  m2 <- matchTy  instRet  genRet
  combineMaps m1 m2

-- | Try to match an implementation type against a trait type  
matchTy :: Ty -> Ty -> Maybe (Map Integer Ty)
matchTy inst arg
  | inst == arg
  = return Map.empty
matchTy ty (TyParam i) 
  = return  (Map.insert i ty Map.empty)
matchTy (TyTuple instTys) (TyTuple genTys) =
  matchTys instTys genTys
matchTy (TySlice t1) (TySlice t2) = matchTy t1 t2
matchTy (TyArray t1 i1) (TyArray t2 i2) | i1 == i2 = matchTy t1 t2
matchTy (TyRef t1 m1) (TyRef t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyAdt d1 s1) (TyAdt d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyFnDef d1 s1) (TyFnDef d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyClosure d1 s1) (TyClosure d2 s2) | d1 == d2 =  matchSubsts s1 s2
matchTy (TyFnPtr sig1) (TyFnPtr sig2) = matchSig sig1 sig2
matchTy (TyRawPtr t1 m1)(TyRawPtr t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyDowncast t1 i1) (TyDowncast t2 i2) | i1 == i2 = matchTy t1 t2
matchTy (TyProjection d1 s1) (TyProjection d2 s2) | d1 == d2 = matchSubsts s1 s2
-- more
matchTy _ _ = Nothing

matchSubsts :: Substs -> Substs -> Maybe (Map Integer Ty)
matchSubsts (Substs tys1) (Substs tys2) = matchTys tys1 tys2

matchTys :: [Ty] -> [Ty] -> Maybe (Map Integer Ty)
matchTys [] [] = return Map.empty
matchTys (t1:instTys) (t2:genTys) = do
  m1 <- matchTy t1 t2
  m2 <- matchTys instTys genTys
  combineMaps m1 m2
matchTys _ _ = Nothing  
  
-- | Decide whether the given method definition is an implementation method for
-- a declared trait. If so, return it along with the trait.
  
getTraitImplementation :: [Trait] ->
                          (MethName,MirHandle) ->
                          Maybe (MethName, TraitName, MirHandle, Substs)
getTraitImplementation trts (name, handle@(MirHandle _mname sig _ _fh)) = do
  -- find just the text of the method name
  methodEntry <- parseImplName name
  
  -- find signature of methods that share this name
  let hasTraitMethod (TraitMethod tm ts) = if sameTraitMethod methodEntry tm then Just (tm,ts) else Nothing
      hasTraitMethod _ = Nothing

  let namedTraits = [ (tn, tm, ts) | (Trait tn items) <- trts, Just (tm,ts) <- map hasTraitMethod items ]
  
  let typedTraits = Maybe.mapMaybe (\(tn,tm,ts) -> (tn,tm,ts,) <$> matchSig sig ts) namedTraits

  (traitName,_,_,instMap) <- Maybe.listToMaybe typedTraits

  -- TODO: hope all of the params actually appear....
  -- otherwise there will be a gap
  let substs = Substs (Map.elems instMap)


{-
  when (namedTraits /= []) $ do
      traceM $ "Method sig is: " ++ show (pretty sig)
      traceM $ "Potential implementations of these " ++ show namedTraits
      traceM $ "Found implementations are " ++ show typedTraits
-}
      
  
  return (name, traitName, handle, substs)

-------------------------------------------------------------------------------------------------------

makeLenses ''TraitImpls
makeLenses ''FnState


$(return [])

------------------------------------------------------------------------------------

first :: (a -> Maybe b) -> [a] -> Maybe b
first f [] = Nothing
first f (x:xs) = case f x of Just y   -> Just y
                             Nothing  -> first f xs

-- TODO: remove errors and return Nothing instead
resolveStaticTrait :: StaticTraitMap -> TraitMap s -> MethName -> Substs -> Maybe (MirExp s)
resolveStaticTrait stm tm mn sub =
  case  Map.lookup mn stm of
    Just ts -> case sub of
      (Substs (_:_)) -> first (\tn -> resolveTraitMethod tm tn sub mn) ts
      Substs []      -> error $ "Cannot resolve trait " ++ show mn ++ " without type arguments"
    Nothing -> Nothing

resolveTraitMethod :: TraitMap s -> TraitName -> Substs -> MethName -> Maybe (MirExp s)
resolveTraitMethod (TraitMap tmap) tn (Substs subs@(ty:_)) mn
  | Just (Some timpls) <- Map.lookup tn tmap
  , Just (Some idx)    <- Map.lookup mn (timpls^.methodIndex)
  = do
     let vtab = timpls^.vtables
     case Map.lookup ty vtab of
       Just assn -> case assn ! idx of 
         MirValue _ tye e -> return (MirExp tye e)
       Nothing   ->
         let -- go :: Ty -> Assignment (MirValue s) ctx -> Maybe (MirExp s) -> Maybe (MirExp s)
             go keyTy assn res =
               case matchTy ty keyTy of
                 Nothing -> res
                 Just _inst -> case (assn ! idx) of
                   MirValue _ ty e -> Just $ MirExp ty e
         in                     
            Map.foldrWithKey go Nothing vtab
            
resolveTraitMethod _ tn (Substs (_:_)) mn = 
  error $ "Cannot find trait " ++ show tn ++ " or its method " ++ show mn
resolveTraitMethod (TraitMap tmap) tn (Substs []) mn =
  error $ "Cannot resolve trait without type arguments"


-------------------------------------------------------------------------------------------------------

--  LocalWords:  ty ImplementTrait ctx vtable
