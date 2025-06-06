{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Mir.TransTy where

import Control.Monad
import Control.Lens
import qualified Data.BitVector.Sized as BV
import Data.List (findIndices)
import           Data.String (fromString)
import           Data.Text (Text)
import qualified Data.Vector as V

import GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC


-- crucible
import qualified Lang.Crucible.Types as C

import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.Syntax as S

import qualified Mir.DefId as M
import qualified Mir.Mir as M
import qualified Debug.Trace as Debug

import           Mir.Generator
    ( MirExp(..), MirPlace(..), PtrMetadata(..), MirGenerator, mirFail
    , subfieldRef, subvariantRef, subjustRef
    , mirVector_fromVector
    , cs, collection, discrMap, findAdt, mirVector_uninit, arrayZeroed )
import           Mir.Intrinsics
    ( MIR, pattern MirSliceRepr, pattern MirReferenceRepr, MirReferenceType
    , pattern MirVectorRepr
    , SizeBits, pattern UsizeRepr, pattern IsizeRepr
    , isizeLit
    , RustEnumType, pattern RustEnumRepr, SomeRustEnumRepr(..)
    , mkRustEnum, rustEnumVariant, rustEnumDiscriminant
    , pattern MethodSpecRepr, pattern MethodSpecBuilderRepr
    , DynRefType, usizeLit , pattern BaseUsizeRepr )


-----------------------------------------------------------------------
-- ** Type translation: MIR types to Crucible types

-- Type translation and type-level list utilities.
-- References have the exact same semantics as their referent type.
-- Arrays and slices are both crucible vectors; no difference between them.
-- Tuples are crucible structs.

-- Non-custom ADTs are encoded either as a Struct or a variant of Structs,
-- depending on whether the Rust type is a struct or enum.
--
-- Custom type translation is on the bottom of this file.

type TransTyConstraint = (HasCallStack)   -- (HasCallStack, ?col::M.Collection)


-- | convert a baseSize to a nat repr
-- Precondition: The BaseSize must *not* be USize.
baseSizeToNatCont :: HasCallStack => M.BaseSize -> (forall w. (1 <= w) => C.NatRepr w -> a) -> a
baseSizeToNatCont M.B8   k = k (knownNat :: NatRepr 8)
baseSizeToNatCont M.B16  k = k (knownNat :: NatRepr 16)
baseSizeToNatCont M.B32  k = k (knownNat :: NatRepr 32)
baseSizeToNatCont M.B64  k = k (knownNat :: NatRepr 64)
baseSizeToNatCont M.B128 k = k (knownNat :: NatRepr 128)
baseSizeToNatCont M.USize k = k (knownNat :: NatRepr SizeBits)


-- Custom type aliases
pattern CTyInt512 <- M.TyAdt _ $(M.explodedDefIdPat ["int512", "Int512"]) (M.Substs [])
pattern CTyBox t <- M.TyAdt _ $(M.explodedDefIdPat ["alloc", "boxed", "Box"]) (M.Substs [t])

pattern CTyMaybeUninit t <- M.TyAdt _ $(M.explodedDefIdPat ["$lang", "MaybeUninit"]) (M.Substs [t])

maybeUninitExplodedDefId :: M.ExplodedDefId
maybeUninitExplodedDefId = ["$lang", "MaybeUninit"]

-- `UnsafeCell` isn't handled specially inside baseline `crucible-mir`, but
-- `crux-mir-comp` looks for it (using this pattern synonym).
pattern CTyUnsafeCell t <- M.TyAdt _ $(M.explodedDefIdPat ["$lang", "UnsafeCell"]) (M.Substs [t])

pattern CTyVector t <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "vector", "Vector"]) (M.Substs [t])

vectorExplodedDefId :: M.ExplodedDefId
vectorExplodedDefId = ["crucible", "vector", "Vector"]

pattern CTyArray t <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "array", "Array"]) (M.Substs [t])

pattern CTyBvSize128 <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "bitvector", "_128"]) (M.Substs [])
pattern CTyBvSize256 <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "bitvector", "_256"]) (M.Substs [])
pattern CTyBvSize512 <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "bitvector", "_512"]) (M.Substs [])
pattern CTyBv t <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "bitvector", "Bv"]) (M.Substs [t])

bvExplodedDefId :: M.ExplodedDefId
bvExplodedDefId = ["crucible", "bitvector", "Bv"]

pattern CTyAny <- M.TyAdt _ $(M.explodedDefIdPat ["core", "crucible", "any", "Any"]) (M.Substs [])

pattern CTyMethodSpec <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "method_spec", "raw", "MethodSpec"]) (M.Substs [])

pattern CTyMethodSpecBuilder <- M.TyAdt _ $(M.explodedDefIdPat ["crucible", "method_spec", "raw", "MethodSpecBuilder"]) (M.Substs [])


-- These don't have custom representation, but are referenced in various
-- places.
pattern CTyOption t <- M.TyAdt _ $(M.explodedDefIdPat ["$lang", "Option"]) (M.Substs [t])

optionExplodedDefId :: M.ExplodedDefId
optionExplodedDefId = ["$lang", "Option"]
optionDiscrNone :: Int
optionDiscrNone = 0
optionDiscrSome :: Int
optionDiscrSome = 1


tyBvSize :: M.Ty -> Maybe BVSize
tyBvSize ty = case ty of
    CTyBvSize128 -> Just $ BVSize $ knownNat @128
    CTyBvSize256 -> Just $ BVSize $ knownNat @256
    CTyBvSize512 -> Just $ BVSize $ knownNat @512
    _ -> Nothing

data BVSize where
  BVSize :: forall w. (1 <= w) => NatRepr w -> BVSize


tyToRepr :: TransTyConstraint => M.Collection -> M.Ty -> Some C.TypeRepr
tyToRepr col t0 = case t0 of
  CTyInt512 -> Some $ C.BVRepr (knownNat :: NatRepr 512)
  CTyBv (tyBvSize -> Just (BVSize w)) -> Some $ C.BVRepr w
  CTyVector t -> tyToReprCont col t $ \repr -> Some (C.VectorRepr repr)
  CTyArray t
    | Some tpr <- tyToRepr col t
    , C.AsBaseType btr <- C.asBaseType tpr ->
      Some (C.SymbolicArrayRepr (Ctx.Empty Ctx.:> C.BaseBVRepr (knownNat @SizeBits)) btr)
    | otherwise -> error $ "unsupported: crucible arrays of non-base type"
  CTyAny -> Some C.AnyRepr
  CTyMethodSpec -> Some MethodSpecRepr
  CTyMethodSpecBuilder -> Some MethodSpecBuilderRepr

  -- CMaybeUninit is handled by the normal repr(transparent) TyAdt case.

  M.TyBool -> Some C.BoolRepr
  M.TyTuple [] -> Some C.UnitRepr

  -- non-empty tuples are mapped to structures of "maybe" types so
  -- that they can be allocated without being initialized
  M.TyTuple ts    -> tyListToCtxMaybe col ts $ \repr -> Some (C.StructRepr repr)

  -- Closures are just tuples with a fancy name
  M.TyClosure ts  -> tyListToCtxMaybe col ts $ \repr -> Some (C.StructRepr repr)

  M.TyArray t _sz -> tyToReprCont col t $ \repr -> Some (MirVectorRepr repr)

  M.TyInt M.USize  -> Some IsizeRepr
  M.TyUint M.USize -> Some UsizeRepr
  M.TyInt base  -> baseSizeToNatCont base $ \n -> Some $ C.BVRepr n
  M.TyUint base -> baseSizeToNatCont base $ \n -> Some $ C.BVRepr n

  -- These definitions are *not* compositional
  M.TyRef (M.TySlice _) _ -> Some MirSliceRepr
  M.TyRef M.TyStr _       -> Some MirSliceRepr

  -- Both `&dyn Tr` and `&mut dyn Tr` use the same representation: a pair of a
  -- data value (which is either `&Ty` or `&mut Ty`) and a vtable. The vtable
  -- is type-erased (`AnyRepr`).
  M.TyRef (M.TyDynamic _) _ -> Some $ C.StructRepr $
    Ctx.empty Ctx.:> MirReferenceRepr Ctx.:> C.AnyRepr

  -- TODO: DSTs not behind a reference - these should never appear in real code
  M.TySlice _ -> Some MirSliceRepr
  M.TyStr -> Some MirSliceRepr

  M.TyRef _ _       -> Some MirReferenceRepr
  -- Raw pointers are represented like references, including the fat pointer
  -- cases that are special-cased above.
  M.TyRawPtr t mutbl -> tyToRepr col (M.TyRef t mutbl)

  M.TyChar -> Some $ C.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes

  -- An ADT type is a Struct (for structs) or a variant of Structs (for enums)
  M.TyAdt name _ _ ->
    let adt =
          case col ^. M.adts . at name of
            Just x -> x
            Nothing -> error $ "unknown ADT " ++ show name in
    case adt ^. M.adtkind of
      _ | Just ty <- reprTransparentFieldTy col adt ->
          tyToRepr col ty
      M.Struct ->
        case variantFields' col (M.onlyVariant adt) of
          Some fctx -> Some $ C.StructRepr $ fieldCtxType fctx
      M.Enum discrTy ->
        tyToReprCont col discrTy $ \discrTp ->
        case enumVariants col adt of
          SomeRustEnumRepr _ ctx -> Some $ RustEnumRepr discrTp ctx
      M.Union ->
        error $ "Union types are unsupported, for " ++ show name
  M.TyDowncast _adt _i   -> Some C.AnyRepr

  M.TyFloat _ -> Some C.RealValRepr

  -- non polymorphic function types go to FunctionHandleRepr
  M.TyFnPtr sig@(M.FnSig args ret _abi _spread) ->
     tyListToCtx col args $ \argsr  ->
     tyToReprCont col ret $ \retr ->
        Some (C.FunctionHandleRepr argsr retr)

  -- We don't support unsized rvalues.  Currently we error only for standalone
  -- standalone (i.e., not under `TyRef`/`TyRawPtr`) use of `TyDynamic` - we
  -- should do the same for TySlice and TyStr as well.
  M.TyDynamic _trait -> error $ unwords ["standalone use of `dyn` is not supported:", show t0]

  -- Values of these types are zero-sized, which we represent as a unit value on
  -- the Crucible side.
  M.TyFnDef _def -> Some C.UnitRepr
  M.TyNever -> Some C.UnitRepr

  M.TyLifetime -> Some C.AnyRepr
  M.TyForeign -> Some C.AnyRepr
  M.TyErased -> Some C.AnyRepr
  _ -> error $ unwords ["unknown type?", show t0]


pattern DynRefCtx :: () => (ctx ~ (Ctx.EmptyCtx Ctx.::> MirReferenceType Ctx.::> C.AnyType)) => Ctx.Assignment C.TypeRepr ctx
pattern DynRefCtx = Ctx.Empty Ctx.:> MirReferenceRepr Ctx.:> C.AnyRepr

pattern DynRefRepr :: () => (tp ~ DynRefType) => C.TypeRepr tp
pattern DynRefRepr = C.StructRepr DynRefCtx


tyToReprM :: M.Ty -> MirGenerator h s ret (Some C.TypeRepr)
tyToReprM ty = do
  col <- use $ cs . collection
  return $ tyToRepr col ty



-- Checks whether a type can be default-initialized.  Any time this returns
-- `True`, `Trans.initialValue` must also return `Just`.  Non-initializable ADT
-- fields are wrapped in `Maybe` to support field-by-field initialization.
canInitialize :: M.Collection -> M.Ty -> Bool
canInitialize col ty = case ty of
    -- Custom types
    CTyAny -> False
    CTyMethodSpec -> False
    CTyMethodSpecBuilder -> False

    -- Primitives
    M.TyBool -> True
    M.TyChar -> True
    M.TyInt _ -> True
    M.TyUint _ -> True
    -- ADTs and related data structures
    M.TyTuple _ -> True
    M.TyAdt _ _ _
      | Just ty' <- tyAdtDef col ty >>= reprTransparentFieldTy col -> canInitialize col ty'
      | otherwise -> True
    M.TyClosure _ -> True
    -- Others
    M.TyArray _ _ -> True
    -- TODO: workaround for a ref init bug - see initialValue for details
    --M.TyRef ty' _ -> canInitialize col ty'
    _ -> False

isUnsized :: M.Ty -> Bool
isUnsized ty = case ty of
    M.TyStr -> True
    M.TySlice _ -> True
    M.TyDynamic _ -> True
    -- TODO: struct types whose last field is unsized ("custom DSTs")
    _ -> False

isZeroSized :: M.Collection -> M.Ty -> Bool
isZeroSized col ty = go ty
  where
    go ty = case ty of
      M.TyTuple tys -> all go tys
      M.TyClosure tys -> all go tys
      M.TyArray ty n -> n == 0 || go ty
      M.TyAdt name _ _ | Just adt <- col ^? M.adts . ix name -> adt ^. M.adtSize == 0
      M.TyNever -> True
      _ -> False


-- | Look up the `Adt` definition, if this `Ty` is `TyAdt`.
tyAdtDef :: M.Collection -> M.Ty -> Maybe M.Adt
tyAdtDef col (M.TyAdt name _ _) = col ^? M.adts . ix name
tyAdtDef _ _ = Nothing

-- | If the `Adt` is a `repr(transparent)` struct with at most one
-- non-zero-sized field, return the index of that field.
findReprTransparentField :: M.Collection -> M.Adt -> Maybe Int
findReprTransparentField col adt = do
  guard $ adt ^. M.adtReprTransparent
  [v] <- return $ adt ^. M.adtvariants
  -- We want to always return a valid field index, which we can't do if there
  -- are no fields.
  guard $ not $ null $ v ^. M.vfields
  let idxs = findIndices (\f -> not $ isZeroSized col $ f ^. M.fty) (v ^. M.vfields)
  guard $ length idxs <= 1
  return $ maybe 0 id (idxs ^? ix 0)

reprTransparentFieldTy :: M.Collection -> M.Adt -> Maybe M.Ty
reprTransparentFieldTy col adt = do
  idx <- findReprTransparentField col adt
  adt ^? M.adtvariants . ix 0 . M.vfields . ix idx . M.fty



variantFields :: TransTyConstraint => M.Collection -> M.Variant -> Some C.CtxRepr
variantFields col (M.Variant _vn _vd vfs _vct _mbVal _inh) =
    tyReprListToCtx
        (map (mapSome fieldType . tyToFieldRepr col . (^. M.fty)) vfs)
        (\repr -> Some repr)

variantFieldsM :: TransTyConstraint => M.Variant -> MirGenerator h s ret (Some C.CtxRepr)
variantFieldsM v = do
  col <- use $ cs . collection
  return $ variantFields col v

data FieldRepr tp' = forall tp. FieldRepr (FieldKind tp tp')

instance Show (FieldRepr tp') where
    showsPrec d (FieldRepr kind) = showParen (d > 10) $
        showString "FieldRepr " . showsPrec 11 kind
instance ShowF FieldRepr

fieldType :: FieldRepr tp -> C.TypeRepr tp
fieldType (FieldRepr (FkInit tpr)) = tpr
fieldType (FieldRepr (FkMaybe tpr)) = C.MaybeRepr tpr

-- `FieldCtxRepr ctx` is like `C.CtxRepr ctx`, but also records whether each
-- field is wrapped or not.
type FieldCtxRepr = Ctx.Assignment FieldRepr

fieldCtxType :: FieldCtxRepr ctx -> C.CtxRepr ctx
fieldCtxType Ctx.Empty = Ctx.Empty
fieldCtxType (ctx Ctx.:> fr) = fieldCtxType ctx Ctx.:> fieldType fr

tyToFieldRepr :: M.Collection -> M.Ty -> Some FieldRepr
tyToFieldRepr col ty
  | canInitialize col ty = viewSome (\tpr -> Some $ FieldRepr $ FkInit tpr) (tyToRepr col ty)
  | otherwise = viewSome (\tpr -> Some $ FieldRepr $ FkMaybe tpr) (tyToRepr col ty)

variantFields' :: TransTyConstraint => M.Collection -> M.Variant -> Some FieldCtxRepr
variantFields' col (M.Variant _vn _vd vfs _vct _mbVal _inh) =
    fieldReprListToCtx
        (map (tyToFieldRepr col . (^. M.fty)) vfs)
        (\x -> Some x)

variantFieldsM' :: TransTyConstraint => M.Variant -> MirGenerator h s ret (Some FieldCtxRepr)
variantFieldsM' v = do
  col <- use $ cs . collection
  return $ variantFields' col v

enumVariants :: TransTyConstraint => M.Collection -> M.Adt -> SomeRustEnumRepr
enumVariants col (M.Adt name kind vs _ _ _ _) =
  case kind of
    M.Enum discrTy
      |  Some discrTpr <- tyToRepr col discrTy
      -> reprsToCtx variantReprs $ \variantsCxt ->
         SomeRustEnumRepr discrTpr variantsCxt
    _ -> error $ "expected " ++ show name ++ " to have kind Enum"
  where
    variantReprs :: [Some C.TypeRepr]
    variantReprs = map (\v ->
        viewSome (\ctx -> Some $ C.StructRepr ctx) $
        variantFields col v) vs

enumVariantsM :: TransTyConstraint => M.Adt -> MirGenerator h s ret SomeRustEnumRepr
enumVariantsM adt = do
  col <- use $ cs . collection
  return $ enumVariants col adt

-- As in the CPS translation, functions which manipulate types must be
-- in CPS form, since type tags are generally hidden underneath an
-- existential.

tyToReprCont :: forall a. TransTyConstraint =>
  M.Collection -> M.Ty -> (forall tp. HasCallStack => C.TypeRepr tp -> a) -> a
tyToReprCont col t f = case tyToRepr col t of
                 Some x -> f x
tyReprListToCtx :: forall a. TransTyConstraint => [Some C.TypeRepr] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyReprListToCtx ts f =  go ts Ctx.empty
 where go :: forall ctx. [Some C.TypeRepr] -> C.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)

fieldReprListToCtx :: forall a. TransTyConstraint => [Some FieldRepr] -> (forall ctx. FieldCtxRepr ctx -> a) -> a
fieldReprListToCtx frs f =  go frs Ctx.empty
 where go :: forall ctx. [Some FieldRepr] -> FieldCtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some fr:frs) ctx = go frs (ctx Ctx.:> fr)

tyListToCtx :: forall a. TransTyConstraint =>
  M.Collection -> [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyListToCtx col ts f = tyReprListToCtx (map (tyToRepr col) ts) f

reprsToCtx :: forall a. [Some C.TypeRepr] -> (forall ctx. C.CtxRepr ctx -> a) -> a
reprsToCtx rs f = go rs Ctx.empty
 where go :: forall ctx. [Some C.TypeRepr] -> C.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)


-- same as tyListToCtx, but each type in the list is wrapped in a Maybe
tyListToCtxMaybe :: forall a. TransTyConstraint =>
  M.Collection -> [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyListToCtxMaybe col ts f =  go (map (tyToRepr col) ts) Ctx.empty
 where go :: forall ctx. [Some C.TypeRepr] -> C.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> C.MaybeRepr tp)

-----------------------------------------------------------------------
-- ** Basic operations

exp_to_assgn :: HasCallStack => [MirExp s] -> (forall ctx. C.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> a) -> a
exp_to_assgn =
    go Ctx.empty Ctx.empty
        where go :: C.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> [MirExp s] -> (forall ctx'. C.CtxRepr ctx' -> Ctx.Assignment (R.Expr MIR s) ctx' -> a) -> a
              go ctx asgn [] k = k ctx asgn
              go ctx asgn ((MirExp tyr ex):vs) k = go (ctx Ctx.:> tyr) (asgn Ctx.:> ex) vs k

exp_to_assgn_Maybe :: HasCallStack => M.Collection -> [M.Ty] -> [Maybe (MirExp s)]
  -> (forall ctx. C.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> a) -> a
exp_to_assgn_Maybe col =
    go Ctx.empty Ctx.empty
        where go :: C.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> [M.Ty] -> [Maybe (MirExp s)]
                -> (forall ctx'. C.CtxRepr ctx' -> Ctx.Assignment (R.Expr MIR s) ctx' -> a) -> a
              go ctx asgn [] [] k = k ctx asgn
              go ctx asgn (_:tys) (Just (MirExp tyr ex):vs) k =
                go (ctx Ctx.:> C.MaybeRepr tyr) (asgn Ctx.:> (R.App $ E.JustValue tyr ex)) tys vs k
              go ctx asgn (ty:tys) (Nothing:vs) k =
                tyToReprCont col ty $ \tyr ->
                   go (ctx Ctx.:> C.MaybeRepr tyr) (asgn Ctx.:> (R.App $ E.NothingValue tyr)) tys vs k
              go _ _ _ _ _ = error "BUG in crux-mir: exp_to_assgn_Maybe"




packAny ::  MirExp s -> (MirExp s)
packAny (MirExp e_ty e) = MirExp C.AnyRepr (S.app $ E.PackAny e_ty e)


-- array in haskell -> crucible array
buildArrayLit :: forall h s tp ret.  C.TypeRepr tp -> [MirExp s] -> MirGenerator h s ret (MirExp s)
buildArrayLit trep exps = do
    vec <- go exps V.empty
    exp <- mirVector_fromVector trep $ S.app $ E.VectorLit trep vec
    return $ MirExp (MirVectorRepr trep) exp
  where go :: [MirExp s] -> V.Vector (R.Expr MIR s tp) -> MirGenerator h s ret (V.Vector (R.Expr MIR s tp))
        go [] v = return v
        go ((MirExp erepr e):es) v = do
          case (testEquality erepr trep) of
            Just Refl -> do
                v' <- go es v
                return $ V.cons e v'
            Nothing -> mirFail "bad type in build array"

buildTuple :: [MirExp s] -> MirExp s
buildTuple xs = exp_to_assgn (xs) $ \ctx asgn ->
    MirExp (C.StructRepr ctx) (S.app $ E.MkStruct ctx asgn)

buildTupleMaybe :: M.Collection -> [M.Ty] -> [Maybe (MirExp s)] -> MirExp s
buildTupleMaybe col tys xs = exp_to_assgn_Maybe col tys xs $ \ctx asgn ->
    MirExp (C.StructRepr ctx) (S.app $ E.MkStruct ctx asgn)

buildTupleMaybeM :: [M.Ty] -> [Maybe (MirExp s)] -> MirGenerator h s ret (MirExp s)
buildTupleMaybeM tys xs = do
  col <- use $ cs . collection
  return $ buildTupleMaybe col tys xs

accessAggregateMaybe :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregateMaybe (MirExp (C.StructRepr ctx) ag) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      case tpr of
        C.MaybeRepr tpr' ->
            let mv = R.App $ E.FromJustValue tpr' (S.getStruct idx ag)
                    (R.App $ E.StringLit "Unitialized aggregate value")
            in return $ MirExp tpr' mv
        _ -> mirFail "accessAggregateMaybe: non-maybe struct"

accessAggregateMaybe (MirExp ty a) b = mirFail $ "invalid access of " ++ show ty ++ " at field (maybe) " ++ (show b)

modifyAggregateIdxMaybe :: MirExp s -> -- aggregate to modify
                      MirExp s -> -- thing to insert
                      Int -> -- index
                      MirGenerator h s ret (MirExp s)
modifyAggregateIdxMaybe (MirExp (C.StructRepr agctx) ag) (MirExp instr ins) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size agctx) = do
      let tpr = agctx Ctx.! idx
      case tpr of
         C.MaybeRepr tpr' ->
            case (testEquality tpr' instr) of
                Just Refl -> do
                    let ins' = R.App (E.JustValue tpr' ins)
                    return $ MirExp (C.StructRepr agctx) (S.setStruct agctx ag idx ins')
                _ -> mirFail "bad modify"
         _ -> mirFail "modifyAggregateIdxMaybe: expecting maybe type for struct component"
  | otherwise = mirFail ("modifyAggregateIdxMaybe: Index " ++ show i ++ " out of range for struct")
modifyAggregateIdxMaybe (MirExp ty _) _ _ =
  do mirFail ("modifyAggregateIdxMaybe: Expected Crucible structure type, but got:" ++ show ty)


readEnumVariant :: C.TypeRepr discrTp -> C.CtxRepr variantsCtx -> Ctx.Index variantsCtx tp ->
    R.Expr MIR s (RustEnumType discrTp variantsCtx) -> MirGenerator h s ret (R.Expr MIR s tp)
readEnumVariant tp ctx idx e = do
    let tpr = ctx Ctx.! idx
    let optVal = R.App $ E.ProjectVariant ctx idx $ R.App $ rustEnumVariant ctx e
    readJust' tpr optVal $
        "readEnumVariant: wrong variant; expected " ++ show idx

buildEnumVariant :: C.TypeRepr discrTp -> C.CtxRepr variantsCtx -> Ctx.Index variantsCtx tp ->
    R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s (RustEnumType discrTp variantsCtx))
buildEnumVariant tp ctx idx e = do
    discr <- enumDiscrLit tp $ fromIntegral $ Ctx.indexVal idx
    let var = R.App $ E.InjectVariant ctx idx e
    return $ R.App $ mkRustEnum tp ctx (R.App discr) var

adjustEnumVariant :: C.TypeRepr discrTp -> C.CtxRepr variantsCtx -> Ctx.Index variantsCtx tp ->
    (R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)) ->
    R.Expr MIR s (RustEnumType discrTp variantsCtx) -> MirGenerator h s ret (R.Expr MIR s (RustEnumType discrTp variantsCtx))
adjustEnumVariant tp ctx idx f e = do
    x <- readEnumVariant tp ctx idx e
    y <- f x
    buildEnumVariant tp ctx idx y


readStructField :: C.CtxRepr ctx -> Ctx.Index ctx tp ->
    R.Expr MIR s (C.StructType ctx) -> MirGenerator h s ret (R.Expr MIR s tp)
readStructField ctx idx e = do
    let tpr = ctx Ctx.! idx
    return $ R.App $ E.GetStruct e idx tpr

writeStructField :: C.CtxRepr ctx -> Ctx.Index ctx tp ->
    R.Expr MIR s (C.StructType ctx) -> R.Expr MIR s tp ->
    MirGenerator h s ret (R.Expr MIR s (C.StructType ctx))
writeStructField ctx idx e e' = do
    let tpr = ctx Ctx.! idx
    return $ R.App $ E.SetStruct ctx e idx e'

adjustStructField :: C.CtxRepr ctx -> Ctx.Index ctx tp ->
    (R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)) ->
    R.Expr MIR s (C.StructType ctx) -> MirGenerator h s ret (R.Expr MIR s (C.StructType ctx))
adjustStructField ctx idx f e = do
    x <- readStructField ctx idx e
    y <- f x
    writeStructField ctx idx e y


readJust' :: C.TypeRepr tp -> R.Expr MIR s (C.MaybeType tp) -> String ->
    MirGenerator h s ret (R.Expr MIR s tp)
readJust' tpr e msg =
    G.fromJustExpr e $ R.App $ E.StringLit $ fromString msg

buildNothing :: C.TypeRepr tp ->
    MirGenerator h s ret (R.Expr MIR s (C.MaybeType tp))
buildNothing tpr = return $ R.App $ E.NothingValue tpr

buildJust :: C.TypeRepr tp -> R.Expr MIR s tp ->
    MirGenerator h s ret (R.Expr MIR s (C.MaybeType tp))
buildJust tpr e = return $ R.App $ E.JustValue tpr e

adjustJust' :: C.TypeRepr tp -> String ->
    (R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)) ->
    R.Expr MIR s (C.MaybeType tp) -> MirGenerator h s ret (R.Expr MIR s (C.MaybeType tp))
adjustJust' tpr msg f e = do
    x <- readJust' tpr e msg
    y <- f x
    buildJust tpr y


-- `tp` is the type of the inner data.  `tp'` is the type of the struct field,
-- which may involve a wrapper.
data FieldKind (tp :: C.CrucibleType) (tp' :: C.CrucibleType) where
    FkInit :: forall tp. C.TypeRepr tp -> FieldKind tp tp
    FkMaybe :: forall tp. C.TypeRepr tp -> FieldKind tp (C.MaybeType tp)

instance Show (FieldKind tp tp') where
    showsPrec d (FkInit tpr) = showParen (d > 10) $
        showString "FkInit " . showsPrec 11 tpr
    showsPrec d (FkMaybe tpr) = showParen (d > 10) $
        showString "FkMaybe " . showsPrec 11 tpr

fieldDataType :: FieldKind tp tp' -> C.TypeRepr tp
fieldDataType (FkInit tpr) = tpr
fieldDataType (FkMaybe tpr) = tpr

readFieldData' :: FieldKind tp tp' -> String ->
    R.Expr MIR s tp' -> MirGenerator h s ret (R.Expr MIR s tp)
readFieldData' (FkInit tpr) msg e = return e
readFieldData' (FkMaybe tpr) msg e = readJust' tpr e msg

buildFieldData :: FieldKind tp tp' ->
    R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp')
buildFieldData (FkInit tpr) e = return e
buildFieldData (FkMaybe tpr) e = buildJust tpr e

-- Adjust the data inside a field.  If `wrapped`, then `tp' ~ MaybeType tp`,
-- and we expect the value to be `Just`.  Otherwise, `tp' ~ tp`, and we modify
-- the value directly.
adjustFieldData :: FieldKind tp tp' ->
    (R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)) ->
    R.Expr MIR s tp' -> MirGenerator h s ret (R.Expr MIR s tp')
adjustFieldData (FkInit tpr) f e = f e
adjustFieldData (FkMaybe tpr) f e =
    adjustJust' tpr "adjustFieldData: expected Just, but got Nothing" f e


data StructInfo = forall ctx tp tp'. StructInfo
    (C.CtxRepr ctx)
    (Ctx.Index ctx tp')
    (FieldKind tp tp')

-- First argument is `True` if a wrapper is expected.
checkFieldKind :: Bool -> C.TypeRepr tp -> C.TypeRepr tp' -> String ->
    MirGenerator h s ret (FieldKind tp tp')
checkFieldKind False tpr tpr' desc = do
    Refl <- testEqualityOrFail tpr tpr' $
        "checkFieldKind: type mismatch: " ++ show tpr ++ " /= " ++ show tpr' ++
        "(at " ++ desc ++ ")"
    return $ FkInit tpr
checkFieldKind True tpr tpr' desc = do
    Refl <- testEqualityOrFail (C.MaybeRepr tpr) tpr' $
        "checkFieldKind: type mismatch: " ++ show (C.MaybeRepr tpr) ++ " /= " ++ show tpr' ++
        "(at " ++ desc ++ ")"
    return $ FkMaybe tpr

structInfo :: M.Adt -> Int -> MirGenerator h s ret StructInfo
structInfo adt i = do
    when (adt ^. M.adtkind /= M.Struct) $ mirFail $
        "expected struct, but got adt " ++ show (adt ^. M.adtname)

    let var = M.onlyVariant adt
    fldTy <- case var ^? M.vfields . ix i of
        Just fld -> return $ fld ^. M.fty
        Nothing -> mirFail errFieldIndex

    Some ctx <- variantFieldsM var
    Some idx <- case Ctx.intIndex (fromIntegral i) (Ctx.size ctx) of
        Just x -> return x
        Nothing -> mirFail errFieldIndex
    let tpr' = ctx Ctx.! idx
    Some tpr <- tyToReprM fldTy

    col <- use $ cs . collection
    kind <- checkFieldKind (not $ canInitialize col fldTy) tpr tpr' $
        "field " ++ show i ++ " of struct " ++ show (adt ^. M.adtname)

    return $ StructInfo ctx idx kind
  where
    errFieldIndex = "field index " ++ show i ++ " is out of range for struct " ++
        show (adt ^. M.adtname)

getStructField :: M.Adt -> Int -> MirExp s -> MirGenerator h s ret (MirExp s)
getStructField adt i (MirExp structTpr e) = do
    StructInfo ctx idx fld <- structInfo adt i
    Refl <- expectStructOrFail ctx structTpr
    e <- readStructField ctx idx e
    e <- readFieldData' fld errFieldUninit e
    return $ MirExp (fieldDataType fld) e
  where
    errFieldUninit = "field " ++ show i ++ " of " ++ show (adt^.M.adtname) ++
        " read while uninitialized"

setStructField :: M.Adt -> Int ->
    MirExp s -> MirExp s -> MirGenerator h s ret (MirExp s)
setStructField adt i (MirExp structTpr e) (MirExp fldTpr e') = do
    StructInfo ctx idx fld <- structInfo adt i
    Refl <- expectStructOrFail ctx structTpr
    Refl <- testEqualityOrFail fldTpr (fieldDataType fld) (errFieldType fld)
    e' <- buildFieldData fld e'
    MirExp structTpr <$> writeStructField ctx idx e e'
  where
    errFieldType :: FieldKind tp tp' -> String
    errFieldType fld = "expected field value for " ++ show (adt^.M.adtname, i) ++
        " to have type " ++ show (fieldDataType fld) ++ ", but got " ++ show fldTpr

-- Run `f`, checking that its return type is the same as its argument.  Fails
-- if `f` returns a different type.
checkSameType :: String ->
    (MirExp s -> MirGenerator h s ret (MirExp s)) ->
    R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)
checkSameType desc f e = do
    let tpr = R.exprType e
    MirExp tpr' e' <- f (MirExp tpr e)
    Refl <- testEqualityOrFail tpr tpr' $ "checkSameType: bad result type: expected " ++
        show tpr ++ ", but got " ++ show tpr' ++ " (in " ++ show desc ++ ")"
    return e

mapStructField :: M.Adt -> Int ->
    (MirExp s -> MirGenerator h s ret (MirExp s)) ->
    MirExp s -> MirGenerator h s ret (MirExp s)
mapStructField adt i f (MirExp structTpr e) = do
    StructInfo ctx idx fld <- structInfo adt i
    Refl <- expectStructOrFail ctx structTpr
    let f' =
            adjustStructField ctx idx $
            adjustFieldData fld $
            checkSameType ("mapStructField " ++ show i ++ " of " ++ show (adt ^. M.adtname)) $
            f
    MirExp structTpr <$> f' e


data EnumInfo = forall discrTp ctx ctx' tp tp'. EnumInfo
    (C.TypeRepr discrTp)
    (C.CtxRepr ctx)
    (Ctx.Index ctx (C.StructType ctx'))
    (C.CtxRepr ctx')
    (Ctx.Index ctx' tp')
    (FieldKind tp tp')

data IsStructType (tp :: C.CrucibleType) where
    IsStructType :: forall ctx. C.CtxRepr ctx -> IsStructType (C.StructType ctx)

checkStructType :: C.TypeRepr tp -> Maybe (IsStructType tp)
checkStructType (C.StructRepr ctx) = Just (IsStructType ctx)
checkStructType _ = Nothing

enumInfo :: M.Adt -> Int -> Int -> MirGenerator h s ret EnumInfo
enumInfo adt i j = do
    Some discrTp <- case adt ^. M.adtkind of
        M.Enum discrTy -> tyToReprM discrTy
        _ -> mirFail $ "expected enum, but got adt " ++ show (adt ^. M.adtname)

    when (isn't M._Enum (adt ^. M.adtkind)) $ mirFail $
        "expected enum, but got adt " ++ show (adt ^. M.adtname)

    var <- case adt ^? M.adtvariants . ix i of
        Just var -> return var
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)
    fldTy <- case var ^? M.vfields . ix j of
        Just fld -> return $ fld ^. M.fty
        Nothing -> mirFail $ "field index " ++ show j ++ " is out of range for enum " ++
            show (adt ^. M.adtname) ++ " variant " ++ show i

    SomeRustEnumRepr _ ctx <- enumVariantsM adt
    Some idx <- case Ctx.intIndex (fromIntegral i) (Ctx.size ctx) of
        Just x -> return x
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)
    IsStructType ctx' <- case checkStructType $ ctx Ctx.! idx of
        Just x -> return x
        Nothing -> mirFail $ "variant " ++ show i ++ " of enum " ++
            show (adt ^. M.adtname) ++ " is not a struct?"
    Some idx' <- case Ctx.intIndex (fromIntegral j) (Ctx.size ctx') of
        Just x -> return x
        Nothing -> mirFail $ "field index " ++ show j ++ " is out of range for enum " ++
            show (adt ^. M.adtname) ++ " variant " ++ show i
    let tpr' = ctx' Ctx.! idx'
    Some tpr <- tyToReprM fldTy

    col <- use $ cs . collection
    kind <- checkFieldKind (not $ canInitialize col fldTy) tpr tpr' $
        "field " ++ show j ++ " of enum " ++ show (adt ^. M.adtname) ++ " variant " ++ show i

    return $ EnumInfo discrTp ctx idx ctx' idx' kind

getEnumField :: M.Adt -> Int -> Int -> MirExp s -> MirGenerator h s ret (MirExp s)
getEnumField adt i j (MirExp enumTpr e) = do
    EnumInfo discrTp ctx idx ctx' idx' fld <- enumInfo adt i j
    Refl <- expectEnumOrFail discrTp ctx enumTpr
    e <- readEnumVariant discrTp ctx idx e
    e <- readStructField ctx' idx' e
    e <- readFieldData' fld errFieldUninit e
    return $ MirExp (R.exprType e) e
  where
    errFieldUninit = "field " ++ show j ++ " of " ++ show (adt^.M.adtname) ++
        " variant " ++ show i ++ " read while uninitialized"


setEnumField :: M.Adt -> Int -> Int ->
    MirExp s -> MirExp s -> MirGenerator h s ret (MirExp s)
setEnumField adt i j (MirExp enumTpr e) (MirExp fldTpr e') = do
    EnumInfo discrTp ctx idx ctx' idx' fld <- enumInfo adt i j
    Refl <- expectEnumOrFail discrTp ctx enumTpr
    Refl <- testEqualityOrFail fldTpr (fieldDataType fld) (errFieldType fld)
    e' <- buildFieldData fld e'
    let f' = adjustEnumVariant discrTp ctx idx $
            \e -> writeStructField ctx' idx' e e'
    MirExp enumTpr <$> f' e
  where
    errFieldType :: FieldKind tp tp' -> String
    errFieldType fld = "expected field value for " ++ show (adt^.M.adtname, i, j) ++
        " to have type " ++ show (fieldDataType fld) ++ ", but got " ++ show fldTpr



buildStructAssign' :: HasCallStack => FieldCtxRepr ctx -> [Maybe (Some (R.Expr MIR s))] ->
    Either String (Ctx.Assignment (R.Expr MIR s) ctx)
buildStructAssign' ctx es = go ctx $ reverse es
  where
    go :: forall ctx s. FieldCtxRepr ctx -> [Maybe (Some (R.Expr MIR s))] ->
        Either String (Ctx.Assignment (R.Expr MIR s) ctx)
    go ctx [] = case Ctx.viewAssign ctx of
        Ctx.AssignEmpty -> return Ctx.empty
        _ -> Left "not enough expressions"
    go ctx (optExp : rest) = case Ctx.viewAssign ctx of
        Ctx.AssignExtend ctx' fldr -> case (fldr, optExp) of
            (FieldRepr (FkInit tpr), Nothing) ->
                case tpr of
                    C.UnitRepr -> continue ctx' rest tpr (R.App $ E.NothingValue tpr)
                    _ -> Left $ "got Nothing for mandatory field " ++ show (length rest) ++ " type:" ++ show tpr
            (FieldRepr (FkInit tpr), Just (Some e)) ->
                continue ctx' rest tpr e
            (FieldRepr (FkMaybe tpr), Nothing) ->
                continue ctx' rest (C.MaybeRepr tpr) (R.App $ E.NothingValue tpr)
            (FieldRepr (FkMaybe tpr), Just (Some e)) ->
                continue ctx' rest (C.MaybeRepr tpr)
                    (R.App $ E.JustValue (R.exprType e) e)
        _ -> Left "too many expressions"

    continue :: forall ctx tp tp' s. FieldCtxRepr ctx -> [Maybe (Some (R.Expr MIR s))] ->
        C.TypeRepr tp -> R.Expr MIR s tp' ->
        Either String (Ctx.Assignment (R.Expr MIR s) (ctx Ctx.::> tp))
    continue ctx' rest tpr e = case testEquality tpr (R.exprType e) of
        Just Refl -> go ctx' rest >>= \flds -> return $ Ctx.extend flds e
        Nothing -> Left $ "type mismatch: expected " ++ show tpr ++ " but got " ++
            show (R.exprType e) ++ " in field " ++ show (length rest) ++ ": " ++ show (ctx, es)

buildStruct' :: HasCallStack => M.Adt -> [Maybe (MirExp s)] ->
    MirGenerator h s ret (MirExp s)
buildStruct' adt es = do
    when (adt ^. M.adtkind /= M.Struct) $ mirFail $
        "expected struct, but got adt " ++ show (adt ^. M.adtname)
    let var = M.onlyVariant adt
    Some fctx <- variantFieldsM' var
    asn <- case buildStructAssign' fctx $ map (fmap (\(MirExp _ e) -> Some e)) es of
        Left err -> mirFail $ "error building struct " ++ show (var^.M.vname) ++ ": " ++ err
        Right x -> return x
    let ctx = fieldCtxType fctx
    pure $ MirExp (C.StructRepr ctx) $ R.App $ E.MkStruct ctx asn

buildStruct :: HasCallStack => M.Adt -> [MirExp s] ->
    MirGenerator h s ret (MirExp s)
buildStruct adt es =
    buildStruct' adt (map Just es)


buildEnum' :: HasCallStack => M.Adt -> Int -> [Maybe (MirExp s)] ->
    MirGenerator h s ret (MirExp s)
buildEnum' adt i es = do
    Some discrTp <- case adt ^. M.adtkind of
        M.Enum discrTy -> tyToReprM discrTy
        _ -> mirFail $ "expected enum, but got adt " ++ show (adt ^. M.adtname)

    var <- case adt ^? M.adtvariants . ix i of
        Just var -> return var
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)

    SomeRustEnumRepr _ ctx <- enumVariantsM adt
    Some idx <- case Ctx.intIndex (fromIntegral i) (Ctx.size ctx) of
        Just x -> return x
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)
    IsStructType ctx' <- case checkStructType $ ctx Ctx.! idx of
        Just x -> return x
        Nothing -> mirFail $ "variant " ++ show i ++ " of enum " ++
            show (adt ^. M.adtname) ++ " is not a struct?"

    Some fctx' <- variantFieldsM' var
    let ftys = map (^. M.fty) (var ^. M.vfields)
    es' <- inferElidedVariantFields ftys es
    asn <- case buildStructAssign' fctx' $ map (fmap (\(MirExp _ e) -> Some e)) es' of
        Left err ->
            mirFail $ "error building variant " ++ show (var^.M.vname) ++ ": " ++ err ++ " -- " ++ show es'
        Right x -> return x
    Refl <- testEqualityOrFail (fieldCtxType fctx') ctx' $
        "got wrong fields for " ++ show (adt ^. M.adtname, i) ++ "?"

    discrs <- use $ cs . discrMap . ix (adt ^. M.adtname)
    discr <- case discrs ^? ix i of
        Just x -> enumDiscrLit discrTp x
        Nothing -> mirFail $ "can't find discr for variant " ++ show (adt ^. M.adtname, i)

    pure $ MirExp (RustEnumRepr discrTp ctx) $
        R.App $ mkRustEnum discrTp ctx (R.App discr) $
        R.App $ E.InjectVariant ctx idx $
        R.App $ E.MkStruct ctx' asn

-- It is possible for an enum to be initialized in MIR without providing
-- explicit assignments for all of its fields. As an example, imagine the value
-- @Ok(())@ of type @Result<(), i32>@. MIR is liable to construct this like so:
--
-- @
-- let mut _0 : Result<(), i32>;
-- discr(_0) = 0
-- @
--
-- Note that there is no statement for explicitly initializing the first field
-- of @Ok@ to @()@. This is by design, as @()@ is a zero-sized type (ZST). While
-- ZSTs need not appear explicitly in MIR, we would like to have explicit
-- representations for them in Crucible. This function is responsible for
-- constructing these explicit representations.
--
-- The approach that this function takes is pretty simple: if we encounter a
-- variant with the same number of types as field values, then return the values
-- unchanged. If there are fewer values than types, then we assume that any ZSTs
-- have elided the fields of the corresponding types, so we insert these values
-- into the list ourselves. We use 'initialValue' to construct a reasonable
-- value of each ZST.
--
-- Note that we are doing this step somewhat late in the pipeline. An
-- alternative approach would be to infer these missing values in
-- "Mir.Pass.AllocateEnum", when the enum variant initialization is first
-- handled. This would require some additional refactoring, so we have not yet
-- pursued this option.
inferElidedVariantFields :: [M.Ty] -> [Maybe (MirExp s)]
                         -> MirGenerator h s ret [Maybe (MirExp s)]
inferElidedVariantFields ftys fes
  | length ftys == length fes
  = pure fes
  | otherwise
  = go ftys fes
  where
    go [] [] = pure []
    go [] (_:_) = mirFail $ unlines [ "inferElidedVariantFields: too many expressions"
                                    , "types:       " ++ show ftys
                                    , "expressions: " ++ show fes
                                    ]
    go (ty:tys) exps = do
      col <- use $ cs . collection
      if isZeroSized col ty
         then do val <- initialValue ty
                 exps' <- go tys exps
                 pure $ val : exps'
         else
           case exps of
             e:es -> do
               es' <- go tys es
               pure $ e : es'
             [] -> mirFail "inferElidedVariantFields: not enough expressions"

buildEnum :: HasCallStack => M.Adt -> Int -> [MirExp s] ->
    MirGenerator h s ret (MirExp s)
buildEnum adt i es =
    buildEnum' adt i (map Just es)

enumDiscrLit :: C.TypeRepr tp -> Integer
             -> MirGenerator h s ret (E.App ext f tp)
enumDiscrLit tp discr =
  case tp of
    C.BVRepr w -> pure $ E.BVLit w $ BV.mkBV w discr
    _ -> mirFail $ "Unknown enum discriminant type: " ++ show tp

fieldDataRef ::
    FieldKind tp tp' ->
    R.Expr MIR s MirReferenceType ->
    MirGenerator h s ret (R.Expr MIR s MirReferenceType)
fieldDataRef (FkInit tpr) ref = return ref
fieldDataRef (FkMaybe tpr) ref = subjustRef tpr ref

structFieldRef ::
    M.Adt -> Int ->
    R.Expr MIR s MirReferenceType ->
    MirGenerator h s ret (MirPlace s)
structFieldRef adt i ref = do
    StructInfo ctx idx fld <- structInfo adt i
    ref <- subfieldRef ctx ref idx
    ref <- fieldDataRef fld ref
    -- TODO: for custom DSTs, we'll need to propagate struct metadata to fields
    return $ MirPlace (fieldDataType fld) ref NoMeta

enumFieldRef ::
    M.Adt -> Int -> Int ->
    R.Expr MIR s MirReferenceType ->
    MirGenerator h s ret (MirPlace s)
enumFieldRef adt i j ref = do
    EnumInfo discrTp ctx idx ctx' idx' fld <- enumInfo adt i j
    ref <- subvariantRef discrTp ctx ref idx
    ref <- subfieldRef ctx' ref idx'
    ref <- fieldDataRef fld ref
    -- TODO: for custom DSTs, we'll need to propagate enum metadata to fields
    return $ MirPlace (fieldDataType fld) ref NoMeta


enumDiscriminant :: M.Adt -> MirExp s ->
    MirGenerator h s ret (MirExp s)
enumDiscriminant adt (MirExp enumTpr v) = do
    SomeRustEnumRepr discrTpr variantsCtx <- enumVariantsM adt
    Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
    return $ MirExp discrTpr $ R.App $ rustEnumDiscriminant discrTpr v

tupleFieldRef ::
    [M.Ty] -> Int ->
    C.TypeRepr tp -> R.Expr MIR s MirReferenceType ->
    MirGenerator h s ret (MirPlace s)
tupleFieldRef tys i tpr ref = do
    col <- use $ cs . collection
    Some ctx <- return $ tyListToCtxMaybe col tys $ \ctx -> Some ctx
    let tpr' = C.StructRepr ctx
    Refl <- testEqualityOrFail tpr tpr' $ "bad representation " ++ show tpr ++
        " for tuple type " ++ show tys ++ ": expected " ++ show tpr'
    Some idx <- case Ctx.intIndex (fromIntegral i) (Ctx.size ctx) of
        Just x -> return x
        Nothing -> mirFail $ "field index " ++ show i ++
            " is out of range for tuple " ++ show tys
    let elemTpr = ctx Ctx.! idx
    case elemTpr of
        C.MaybeRepr valTpr -> do
            ref <- subfieldRef ctx ref idx
            ref <- subjustRef valTpr ref
            return $ MirPlace valTpr ref NoMeta
        _ -> mirFail $ "expected tuple field to have MaybeType, but got " ++ show elemTpr



testEqualityOrFail :: TestEquality f => f a -> f b -> String -> MirGenerator h s ret (a :~: b)
testEqualityOrFail x y msg = case testEquality x y of
    Just pf -> return pf
    Nothing -> mirFail msg

expectStructOrFail ::
  C.CtxRepr expectedStructCtx ->
  C.TypeRepr actualStructTp ->
  MirGenerator h s ret (C.StructType expectedStructCtx :~: actualStructTp)
expectStructOrFail expectedStructCtx actualStructTpr =
  testEqualityOrFail expectedStructTpr actualStructTpr $
    "expected struct to have type" ++ show expectedStructTpr ++
    ", but got " ++ show actualStructTpr
  where
    expectedStructTpr = C.StructRepr expectedStructCtx

expectEnumOrFail ::
  C.TypeRepr expectedDiscrTp ->
  C.CtxRepr expectedVariantsCtx ->
  C.TypeRepr actualEnumTp ->
  MirGenerator h s ret (RustEnumType expectedDiscrTp expectedVariantsCtx :~: actualEnumTp)
expectEnumOrFail expectedDiscrTpr expectedVariantsCtx actualEnumTpr =
  testEqualityOrFail expectedEnumTpr actualEnumTpr $
    "expected enum to have type" ++ show expectedEnumTpr ++
    ", but got " ++ show actualEnumTpr
  where
    expectedEnumTpr = RustEnumRepr expectedDiscrTpr expectedVariantsCtx



-- Vtable handling

-- TODO: make mir-json emit trait vtable layouts for all dyns observed in the
-- crate, then use that info to greatly simplify this function
traitVtableType :: (HasCallStack) =>
    M.Collection -> M.TraitName -> M.Trait -> Some C.TypeRepr
traitVtableType col tname trait = vtableTy
  where
    convertShimSig sig = eraseSigReceiver sig

    methodSigs = map (\(M.TraitMethod _name sig) -> sig) (trait ^. M.traitItems)
    shimSigs = map convertShimSig methodSigs

    vtableTy = tyListToCtx col (map M.TyFnPtr shimSigs) $ \ctx ->
        Some $ C.StructRepr ctx

eraseSigReceiver :: M.FnSig -> M.FnSig
eraseSigReceiver sig = sig & M.fsarg_tys %~ \xs -> case xs of
    [] -> error $ unwords ["dynamic trait method has no receiver", show sig]
    (_ : tys) -> M.TyErased : tys

---- "Allocation"
--
--
-- MIR initializes compound structures by initializing their
-- components. It does not include a general allocation. Here we add
-- general code to initialize the structures for local variables where
-- we can. In general, we only need to produce a value of the correct
-- type with a structure that is compatible for further
-- initialization.
--
-- With this code, it is possible for crux-mir to miss
-- uninitialized values.  So we should revisit this.
--
initialValue :: HasCallStack => M.Ty -> MirGenerator h s ret (Maybe (MirExp s))
initialValue (CTyInt512) =
    let w = knownNat :: NatRepr 512 in
    return $ Just $ MirExp (C.BVRepr w) (S.app (eBVLit w 0))
initialValue (CTyVector t) = do
    Some tr <- tyToReprM t
    return $ Just (MirExp (C.VectorRepr tr) (S.app $ E.VectorLit tr V.empty))
initialValue (CTyArray t) = tyToReprM t >>= \(Some tpr) -> case tpr of
    C.BVRepr w -> do
        let idxs = Ctx.Empty Ctx.:> BaseUsizeRepr
        v <- arrayZeroed idxs w
        return $ Just $ MirExp (C.SymbolicArrayRepr idxs (C.BaseBVRepr w)) v
    _ -> error $ "can't initialize array of " ++ show t ++ " (expected BVRepr)"
initialValue ty@(CTyBv _sz) = tyToReprM ty >>= \(Some tpr) -> case tpr of
    C.BVRepr w -> return $ Just $ MirExp (C.BVRepr w) $ S.app $ eBVLit w 0
    _ -> mirFail $ "Bv type " ++ show ty ++ " does not have BVRepr"
-- `Any` values have no reasonable default.  Any default we provide might get
-- muxed with actual non-default values, which will fail (unless the concrete
-- type happens to match exactly).
initialValue CTyAny = return Nothing
initialValue CTyMethodSpec = return Nothing
initialValue CTyMethodSpecBuilder = return Nothing

initialValue M.TyBool       = return $ Just $ MirExp C.BoolRepr (S.false)
initialValue (M.TyTuple []) = return $ Just $ MirExp C.UnitRepr (R.App E.EmptyApp)
initialValue (M.TyTuple tys) = do
    mexps <- mapM initialValue tys
    col <- use $ cs . collection
    return $ Just $ buildTupleMaybe col tys mexps
initialValue (M.TyInt M.USize) = return $ Just $ MirExp IsizeRepr (R.App $ isizeLit 0)
initialValue (M.TyInt sz)      = baseSizeToNatCont sz $ \w ->
    return $ Just $ MirExp (C.BVRepr w) (S.app (eBVLit w 0))
initialValue (M.TyUint M.USize) = return $ Just $ MirExp UsizeRepr (R.App $ usizeLit 0)
initialValue (M.TyUint sz)      = baseSizeToNatCont sz $ \w ->
    return $ Just $ MirExp (C.BVRepr w) (S.app (eBVLit w 0))
initialValue (M.TyArray t size) = do
    Some tpr <- tyToReprM t
    mv <- mirVector_uninit tpr $ S.app $ eBVLit knownNat (fromIntegral size)
    return $ Just $ MirExp (MirVectorRepr tpr) mv
-- TODO: disabled to workaround for a bug with muxing null and non-null refs
-- The problem is with
--      if (*) {
--          let x = &...;
--      }
-- `x` gets default-initialized at the start of the function, which (with these
-- cases uncommented) sets it to null (`MirReference_Integer 0`).  Then, if the
-- branch is taken, it's set to a valid `MirReference` value instead.  At the
-- end of the `if`, we try to mux together `MirReference_Integer` with a normal
-- `MirReference`, which currently fails.
--
--  * The short-term fix is to disable initialization of refs, so they never
--    get set to `null` in the first place.
--  * The medium-term fix is to support muxing the two MirReference variants,
--    using something like VariantType.
--  * The long-term fix is to remove default-initialization entirely, either by
--    writing an AdtAg pass for structs and tuples like we have for enums, or
--    by converting all locals to untyped allocations (allow writing each field
--    value independently, then materialize a fully-initialized struct the
--    first time it's read at struct type).
--
-- NB: When re-enabling this, also re-enable the TyRef case of `canInitialize`
{-
initialValue (M.TyRef (M.TySlice t) M.Immut) = do
    tyToReprCont t $ \ tr -> do
      let vec = R.App $ E.VectorLit tr V.empty
      vec' <- MirExp (MirVectorRepr tr) <$> mirVector_fromVector tr vec
      let i = MirExp UsizeRepr (R.App $ usizeLit 0)
      return $ Just $ buildTuple [vec', i, i]
initialValue (M.TyRef (M.TySlice t) M.Mut) = do
    tyToReprCont t $ \ tr -> do
      ref <- newMirRef (MirVectorRepr tr)
      let i = MirExp UsizeRepr (R.App $ usizeLit 0)
      return $ Just $ buildTuple [(MirExp (MirReferenceRepr (MirVectorRepr tr)) ref), i, i]
      -- fail ("don't know how to initialize slices for " ++ show t)
initialValue (M.TyRef M.TyStr M.Immut) = do
    let tr = C.BVRepr $ knownNat @8
    let vec = R.App $ E.VectorLit tr V.empty
    vec' <- MirExp (MirVectorRepr tr) <$> mirVector_fromVector tr vec
    let i = MirExp UsizeRepr (R.App $ usizeLit 0)
    return $ Just $ buildTuple [vec', i, i]
initialValue (M.TyRef M.TyStr M.Mut) = do
    let tr = C.BVRepr $ knownNat @8
    ref <- newMirRef (MirVectorRepr tr)
    let i = MirExp UsizeRepr (R.App $ usizeLit 0)
    return $ Just $ buildTuple [(MirExp (MirReferenceRepr (MirVectorRepr tr)) ref), i, i]
initialValue (M.TyRef (M.TyDynamic _) _) = do
    let x = R.App $ E.PackAny knownRepr $ R.App $ E.EmptyApp
    return $ Just $ MirExp knownRepr $ R.App $ E.MkStruct knownRepr $
        Ctx.Empty Ctx.:> x Ctx.:> x
initialValue (M.TyRawPtr (M.TyDynamic _) _) = do
    let x = R.App $ E.PackAny knownRepr $ R.App $ E.EmptyApp
    return $ Just $ MirExp knownRepr $ R.App $ E.MkStruct knownRepr $
        Ctx.Empty Ctx.:> x Ctx.:> x
initialValue (M.TyRef t M.Immut) = initialValue t
initialValue (M.TyRef t M.Mut)
  | Some tpr <- tyToRepr t = do
    r <- integerToMirRef tpr $ R.App $ usizeLit 0
    return $ Just $ MirExp (MirReferenceRepr tpr) r
-}
initialValue M.TyChar = do
    let w = (knownNat :: NatRepr 32)
    return $ Just $ MirExp (C.BVRepr w) (S.app (eBVLit w 0))
initialValue (M.TyClosure tys) = do
    mexps <- mapM initialValue tys
    col <- use $ cs . collection
    return $ Just $ buildTupleMaybe col tys mexps
initialValue (M.TyAdt nm _ _) = do
    adt <- findAdt nm
    col <- use $ cs . collection
    case adt ^. M.adtkind of
        _ | Just ty <- reprTransparentFieldTy col adt -> initialValue ty
        M.Struct -> do
            let var = M.onlyVariant adt
            fldExps <- mapM initField (var^.M.vfields)
            Just <$> buildStruct' adt fldExps
        M.Enum _ -> do
            case ifind (\_ vars -> vars ^. M.vinhabited) (adt ^. M.adtvariants) of
                -- Uninhabited enums can't be initialized.
                Nothing -> return Nothing
                -- Inhabited enums get initialized to their first inhabited variant.
                Just (discr, var) -> do
                    fldExps <- mapM initField (var^.M.vfields)
                    Just <$> buildEnum' adt discr fldExps
        M.Union -> return Nothing



initialValue (M.TyFnPtr _) = return $ Nothing
initialValue (M.TyFnDef _) = return $ Just $ MirExp C.UnitRepr $ R.App E.EmptyApp
initialValue M.TyNever     = return $ Just $ MirExp C.UnitRepr $ R.App E.EmptyApp
initialValue (M.TyDynamic _) = return $ Nothing
initialValue _ = return Nothing

initField :: M.Field -> MirGenerator h s ret (Maybe (MirExp s))
initField (M.Field _name ty) = initialValue ty

eBVLit ::
  (1 <= w) =>
  NatRepr w ->
  Integer ->
  E.App ext f (C.BVType w)
eBVLit w i = E.BVLit w (BV.mkBV w i)
