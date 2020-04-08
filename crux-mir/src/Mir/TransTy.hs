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
import qualified Data.Maybe as Maybe
import qualified Data.String as String
import           Data.String (fromString)
import qualified Data.Vector as V
import qualified Data.Text as Text

import GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Peano
import Data.Parameterized.Some


-- crucible
import qualified Lang.Crucible.Types as C

import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.Syntax as S

import qualified Mir.DefId as M
import qualified Mir.Mir as M
import qualified Mir.MirTy as M

import           Mir.PP (fmt)
import           Mir.Generator 
    ( MirExp(..), MirPlace(..), PtrMetadata(..), MirGenerator, mirFail
    , subanyRef, subfieldRef, subvariantRef, subjustRef
    , mirVector_fromVector
    , cs, discrMap )
import           Mir.Intrinsics
    ( MIR, pattern MirSliceRepr, pattern MirReferenceRepr, MirReferenceType
    , pattern MirVectorRepr
    , SizeBits, pattern UsizeRepr, pattern IsizeRepr
    , isizeLit
    , RustEnumType, pattern RustEnumRepr, mkRustEnum, rustEnumVariant, rustEnumDiscriminant
    , DynRefType)
import           Mir.GenericOps (tySubst)


-----------------------------------------------------------------------
-- ** Type translation: MIR types to Crucible types

-- Type translation and type-level list utilities.
-- References have the exact same semantics as their referent type.
-- Arrays and slices are both crucible vectors; no difference between them.
-- Tuples are crucible structs.

-- Non-custom ADTs are encoded as Any.  The underlying type is either a Struct
-- or a Variant of Structs, depending on whether the Rust type is a struct or
-- enum.
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
pattern CTyInt512 <- M.TyAdt _ $(M.normDefIdPat "int512::Int512") (M.Substs [])
  where CTyInt512 = M.TyAdt (M.textId "type::adt") (M.textId "int512::Int512") (M.Substs [])
pattern CTyBox t <- M.TyAdt _ $(M.normDefIdPat "alloc::boxed::Box") (M.Substs [t])
  where CTyBox t = M.TyAdt (M.textId "type::adt") (M.textId "alloc::boxed::Box") (M.Substs [t])
pattern CTyVector t <- M.TyAdt _ $(M.normDefIdPat "crucible::vector::Vector") (M.Substs [t])
  where CTyVector t = M.TyAdt (M.textId "type::adt") (M.textId "crucible::vector::Vector") (M.Substs [t])
pattern CTyArray t <- M.TyAdt _ $(M.normDefIdPat "crucible::array::Array") (M.Substs [t])
  where CTyArray t = M.TyAdt (M.textId "type::adt") (M.textId "crucible::array::Array") (M.Substs [t])

pattern CTyBvSize128 <- M.TyAdt _ $(M.normDefIdPat "crucible::bitvector::_128") (M.Substs [])
  where CTyBvSize128 = M.TyAdt (M.textId "type::adt") (M.textId "crucible::bitvector::_128") (M.Substs [])
pattern CTyBvSize256 <- M.TyAdt _ $(M.normDefIdPat "crucible::bitvector::_256") (M.Substs [])
  where CTyBvSize256 = M.TyAdt (M.textId "type::adt") (M.textId "crucible::bitvector::_256") (M.Substs [])
pattern CTyBvSize512 <- M.TyAdt _ $(M.normDefIdPat "crucible::bitvector::_512") (M.Substs [])
  where CTyBvSize512 = M.TyAdt (M.textId "type::adt") (M.textId "crucible::bitvector::_512") (M.Substs [])
pattern CTyBv t <- M.TyAdt _ $(M.normDefIdPat "crucible::bitvector::Bv") (M.Substs [t])
  where CTyBv t = M.TyAdt (M.textId "type::adt") (M.textId "crucible::bitvector::Bv") (M.Substs [t])
pattern CTyBv128 = CTyBv CTyBvSize128
pattern CTyBv256 = CTyBv CTyBvSize256
pattern CTyBv512 = CTyBv CTyBvSize512

pattern CTyAny <- M.TyAdt _ $(M.normDefIdPat "core::crucible::any::Any") (M.Substs [])
  where CTyAny = M.TyAdt (M.textId "type::adt") (M.textId "core::crucible::any::Any") (M.Substs [])


-- These don't have custom representation, but are referenced in various
-- places.
pattern CTyOption t <- M.TyAdt _ $(M.normDefIdPat "core::option::Option") (M.Substs [t])
  where CTyOption t = M.TyAdt (M.textId "type::adt") (M.textId "core::option::Option") (M.Substs [t])

optionDefId :: M.DefId
optionDefId = M.textId "core::option::Option"
optionDiscrNone :: Int
optionDiscrNone = 0
optionDiscrSome :: Int
optionDiscrSome = 1


tyToRepr :: TransTyConstraint => M.Ty -> Some C.TypeRepr
tyToRepr t0 = case t0 of
  CTyInt512 -> Some $ C.BVRepr (knownNat :: NatRepr 512)
  CTyBv128 -> Some $ C.BVRepr (knownNat :: NatRepr 128)
  CTyBv256 -> Some $ C.BVRepr (knownNat :: NatRepr 256)
  CTyBv512 -> Some $ C.BVRepr (knownNat :: NatRepr 512)
  CTyBox t -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)
  CTyVector t -> tyToReprCont t $ \repr -> Some (C.VectorRepr repr)
  CTyArray t
    | Some tpr <- tyToRepr t
    , C.AsBaseType btr <- C.asBaseType tpr ->
      Some (C.SymbolicArrayRepr (Ctx.Empty Ctx.:> C.BaseBVRepr (knownNat @SizeBits)) btr)
    | otherwise -> error $ "unsupported: crucible arrays of non-base type"
  CTyAny -> Some C.AnyRepr

  M.TyBool -> Some C.BoolRepr
  M.TyTuple [] -> Some C.UnitRepr
  
  -- non-empty tuples are mapped to structures of "maybe" types so
  -- that they can be allocated without being initialized
  M.TyTuple ts    -> tyListToCtxMaybe ts $ \repr -> Some (C.StructRepr repr)

  -- Closures are just tuples with a fancy name
  M.TyClosure ts  -> tyListToCtxMaybe ts $ \repr -> Some (C.StructRepr repr)

  M.TyArray t _sz -> tyToReprCont t $ \repr -> Some (MirVectorRepr repr)

  M.TyInt M.USize  -> Some IsizeRepr
  M.TyUint M.USize -> Some UsizeRepr
  M.TyInt base  -> baseSizeToNatCont base $ \n -> Some $ C.BVRepr n
  M.TyUint base -> baseSizeToNatCont base $ \n -> Some $ C.BVRepr n

  -- These definitions are *not* compositional
  M.TyRef (M.TySlice t) _ -> tyToReprCont t $ \repr -> Some (MirSliceRepr repr)
  M.TyRef M.TyStr _       -> Some (MirSliceRepr (C.BVRepr (knownNat @8)))

  -- Both `&dyn Tr` and `&mut dyn Tr` use the same representation: a pair of a
  -- data value (which is either `&Ty` or `&mut Ty`) and a vtable.  Both are
  -- type-erased (`AnyRepr`), the first because it has to be, and the second
  -- because we'd need to thread the `Collection` into this function (which we
  -- don't want to do) in order to construct the precise vtable type.
  M.TyRef (M.TyDynamic _ _) _ -> Some $ C.StructRepr $
    Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.AnyRepr

  -- TODO: DSTs not behind a reference - these should never appear in real code
  M.TySlice t -> tyToReprCont t $ \repr -> Some (MirSliceRepr repr)
  M.TyStr -> Some (MirSliceRepr (C.BVRepr (knownNat :: NatRepr 8)))

  M.TyRef t _       -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)
  -- Raw pointers are represented like references, including the fat pointer
  -- cases that are special-cased above.
  M.TyRawPtr t mutbl -> tyToRepr (M.TyRef t mutbl)

  M.TyChar -> Some $ C.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes

  -- An ADT is a `concreteAdtRepr` wrapped in `ANY`
  M.TyAdt _ _defid _tyargs -> Some C.AnyRepr
  M.TyDowncast _adt _i   -> Some C.AnyRepr

  M.TyFloat _ -> Some C.RealValRepr
  M.TyParam _i -> error $
    "BUG: all uses of TyParam should have been eliminated, found " ++ fmt t0

  -- non polymorphic function types go to FunctionHandleRepr
  M.TyFnPtr sig@(M.FnSig args ret [] [] _atys _abi _spread) ->
     tyListToCtx args $ \argsr  ->
     tyToReprCont ret $ \retr ->
        Some (C.FunctionHandleRepr argsr retr)
        
  M.TyFnPtr sig@(M.FnSig args ret params preds _atys _abi _spread) ->
      error $ "BUG: polymorphic fn ptrs should not appear in mir-json output any more"

  -- We don't support unsized rvalues.  Currently we error only for standalone
  -- standalone (i.e., not under `TyRef`/`TyRawPtr`) use of `TyDynamic` - we
  -- should do the same for TySlice and TyStr as well.
  M.TyDynamic _trait _preds -> error $ unwords ["standalone use of `dyn` is not supported:", show t0]

  M.TyProjection _def _tyargs -> error $
    "BUG: all uses of TyProjection should have been eliminated, found " ++ fmt t0
  M.TyFnDef _def _substs -> Some C.UnitRepr
  M.TyNever -> Some C.AnyRepr
  M.TyLifetime -> Some C.AnyRepr
  M.TyErased -> Some C.AnyRepr
  _ -> error $ unwords ["unknown type?", show t0]


dynRefCtx :: Ctx.Assignment C.TypeRepr (Ctx.EmptyCtx Ctx.::> C.AnyType Ctx.::> C.AnyType)
dynRefCtx = Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.AnyRepr

dynRefRepr :: C.TypeRepr DynRefType
dynRefRepr = C.StructRepr dynRefCtx



-- Checks whether a type can be default-initialized.  Any time this returns
-- `True`, `Trans.initialValue` must also return `Just`.  Non-initializable ADT
-- fields are wrapped in `Maybe` to support field-by-field initialization.
canInitialize :: M.Ty -> Bool
canInitialize ty = case ty of
    -- Primitives
    M.TyBool -> True
    M.TyChar -> True
    M.TyInt _ -> True
    M.TyUint _ -> True
    -- ADTs and related data structures
    M.TyTuple _ -> True
    M.TyAdt _ _ _ -> True
    M.TyClosure _ -> True
    -- Others
    M.TyArray _ _ -> True
    -- TODO: workaround for a ref init bug - see initialValue for details
    --M.TyRef ty' _ -> canInitialize ty'
    _ -> False


variantFields :: TransTyConstraint => M.Variant -> M.Substs -> Some C.CtxRepr
variantFields (M.Variant _vn _vd vfs _vct) args = 
    tyReprListToCtx
        (map (mapSome fieldType . tyToFieldRepr . M.fieldToTy . M.substField args) vfs)
        (\repr -> Some repr)

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

tyToFieldRepr :: M.Ty -> Some FieldRepr
tyToFieldRepr ty
  | canInitialize ty = viewSome (\tpr -> Some $ FieldRepr $ FkInit tpr) (tyToRepr ty)
  | otherwise = viewSome (\tpr -> Some $ FieldRepr $ FkMaybe tpr) (tyToRepr ty)

variantFields' :: TransTyConstraint => M.Variant -> M.Substs -> Some FieldCtxRepr
variantFields' (M.Variant _vn _vd vfs _vct) args =
    fieldReprListToCtx
        (map (tyToFieldRepr . M.fieldToTy . M.substField args) vfs)
        (\x -> Some x)

enumVariants :: TransTyConstraint => M.Adt -> M.Substs -> Some C.CtxRepr
enumVariants (M.Adt name kind vs _ _) args
  | kind /= M.Enum = error $ "expected " ++ show name ++ " to have kind Enum"
  | otherwise = reprsToCtx variantReprs $ \repr -> Some repr
  where
    variantReprs :: [Some C.TypeRepr]
    variantReprs = map (\v ->
        viewSome (\ctx -> Some $ C.StructRepr ctx) $
        variantFields v args) vs


-- As in the CPS translation, functions which manipulate types must be
-- in CPS form, since type tags are generally hidden underneath an
-- existential.

tyToReprCont :: forall a. TransTyConstraint => M.Ty -> (forall tp. HasCallStack => C.TypeRepr tp -> a) -> a
tyToReprCont t f = case tyToRepr t of
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

tyListToCtx :: forall a. TransTyConstraint => [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyListToCtx ts f = tyReprListToCtx (map tyToRepr ts) f

reprsToCtx :: forall a. [Some C.TypeRepr] -> (forall ctx. C.CtxRepr ctx -> a) -> a
reprsToCtx rs f = go rs Ctx.empty
 where go :: forall ctx. [Some C.TypeRepr] -> C.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)


-- same as tyListToCtx, but each type in the list is wrapped in a Maybe
tyListToCtxMaybe :: forall a. TransTyConstraint => [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyListToCtxMaybe ts f =  go (map tyToRepr ts) Ctx.empty
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

exp_to_assgn_Maybe :: HasCallStack => [M.Ty] -> [Maybe (MirExp s)]
  -> (forall ctx. C.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> a) -> a
exp_to_assgn_Maybe =
    go Ctx.empty Ctx.empty 
        where go :: C.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> [M.Ty] -> [Maybe (MirExp s)]
                -> (forall ctx'. C.CtxRepr ctx' -> Ctx.Assignment (R.Expr MIR s) ctx' -> a) -> a
              go ctx asgn [] [] k = k ctx asgn
              go ctx asgn (_:tys) (Just (MirExp tyr ex):vs) k =
                go (ctx Ctx.:> C.MaybeRepr tyr) (asgn Ctx.:> (R.App $ E.JustValue tyr ex)) tys vs k
              go ctx asgn (ty:tys) (Nothing:vs) k =
                tyToReprCont ty $ \tyr -> 
                   go (ctx Ctx.:> C.MaybeRepr tyr) (asgn Ctx.:> (R.App $ E.NothingValue tyr)) tys vs k
              go _ _ _ _ _ = error "BUG in mir-verifier: exp_to_assgn_Maybe"




packAny ::  MirExp s -> (MirExp s)
packAny (MirExp e_ty e) = MirExp C.AnyRepr (S.app $ E.PackAny e_ty e)

unpackAnyE :: HasCallStack => C.TypeRepr t -> MirExp s -> MirExp s
unpackAnyE tpr e = MirExp tpr $ unpackAnyC tpr e

unpackAnyC :: HasCallStack => C.TypeRepr tp -> MirExp s -> R.Expr MIR s tp
unpackAnyC tpr (MirExp C.AnyRepr e) =
    R.App $ E.FromJustValue tpr
        (R.App $ E.UnpackAny tpr e)
        (R.App $ E.StringLit $ fromString $ "bad unpack: Any as " ++ show tpr)
unpackAnyC _ (MirExp tpr' _) = error $ "bad anytype unpack of " ++ show tpr'


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

buildTupleMaybe :: [M.Ty] -> [Maybe (MirExp s)] -> MirExp s
buildTupleMaybe tys xs = exp_to_assgn_Maybe tys xs $ \ctx asgn ->
    MirExp (C.StructRepr ctx) (S.app $ E.MkStruct ctx asgn)

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


-- TODO: most of the `testEqualityOrFail` in here should be replaced with an
-- `error`ing version

readAnyE :: C.TypeRepr tp -> MirExp s -> MirGenerator h s ret (R.Expr MIR s tp)
readAnyE tpr (MirExp tpr' e) = do
    Refl <- testEqualityOrFail tpr' C.AnyRepr $
        "readAnyE: expected Any, but got " ++ show tpr'
    let valOpt = R.App $ E.UnpackAny tpr e
    val <- G.fromJustExpr valOpt $ R.App $ E.StringLit $ fromString $
        "readAnyE: bad unpack at type " ++ show tpr ++ ": " ++ show e
    return val

buildAnyE :: C.TypeRepr tp -> R.Expr MIR s tp -> MirGenerator h s ret (MirExp s)
buildAnyE tpr e = return $ MirExp C.AnyRepr $ R.App $ E.PackAny tpr e

adjustAnyE :: C.TypeRepr tp ->
    (R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)) ->
    MirExp s -> MirGenerator h s ret (MirExp s)
adjustAnyE tpr f me = do
    x <- readAnyE tpr me
    y <- f x
    buildAnyE tpr y


readEnumVariant :: C.CtxRepr ctx -> Ctx.Index ctx tp ->
    R.Expr MIR s (RustEnumType ctx) -> MirGenerator h s ret (R.Expr MIR s tp)
readEnumVariant ctx idx e = do
    let tpr = ctx Ctx.! idx
    let optVal = R.App $ E.ProjectVariant ctx idx $ R.App $ rustEnumVariant ctx e
    readJust' tpr optVal $
        "readEnumVariant: wrong variant; expected " ++ show idx

buildEnumVariant :: C.CtxRepr ctx -> Ctx.Index ctx tp ->
    R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s (RustEnumType ctx))
buildEnumVariant ctx idx e = do
    let discr = R.App $ isizeLit $ fromIntegral $ Ctx.indexVal idx
    let var = R.App $ E.InjectVariant ctx idx e
    return $ R.App $ mkRustEnum ctx discr var

adjustEnumVariant :: C.CtxRepr ctx -> Ctx.Index ctx tp ->
    (R.Expr MIR s tp -> MirGenerator h s ret (R.Expr MIR s tp)) ->
    R.Expr MIR s (RustEnumType ctx) -> MirGenerator h s ret (R.Expr MIR s (RustEnumType ctx))
adjustEnumVariant ctx idx f e = do
    x <- readEnumVariant ctx idx e
    y <- f x
    buildEnumVariant ctx idx y


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

structInfo :: M.Adt -> M.Substs -> Int -> MirGenerator h s ret StructInfo
structInfo adt args i = do
    when (adt ^. M.adtkind /= M.Struct) $ mirFail $
        "expected struct, but got adt " ++ show (adt ^. M.adtname)

    let var = M.onlyVariant adt
    fldTy <- case var ^? M.vfields . ix i of
        Just fld -> return $ M.fieldToTy $ M.substField args fld
        Nothing -> mirFail errFieldIndex

    Some ctx <- return $ variantFields var args
    Some idx <- case Ctx.intIndex (fromIntegral i) (Ctx.size ctx) of
        Just x -> return x
        Nothing -> mirFail errFieldIndex
    let tpr' = ctx Ctx.! idx
    Some tpr <- return $ tyToRepr fldTy

    kind <- checkFieldKind (not $ canInitialize fldTy) tpr tpr' $
        "field " ++ show i ++ " of struct " ++ show (adt ^. M.adtname)

    return $ StructInfo ctx idx kind
  where
    errFieldIndex = "field index " ++ show i ++ " is out of range for struct " ++
        show (adt ^. M.adtname)

getStructField :: M.Adt -> M.Substs -> Int -> MirExp s -> MirGenerator h s ret (MirExp s)
getStructField adt args i me = do
    StructInfo ctx idx fld <- structInfo adt args i
    e <- readAnyE (C.StructRepr ctx) me
    e <- readStructField ctx idx e
    e <- readFieldData' fld errFieldUninit e
    return $ MirExp (fieldDataType fld) e
  where
    errFieldUninit = "field " ++ show i ++ " of " ++ show (adt^.M.adtname) ++
        " read while uninitialized"

setStructField :: M.Adt -> M.Substs -> Int ->
    MirExp s -> MirExp s -> MirGenerator h s ret (MirExp s)
setStructField adt args i me (MirExp tpr e') = do
    StructInfo ctx idx fld <- structInfo adt args i
    Refl <- testEqualityOrFail tpr (fieldDataType fld) (errFieldType fld)
    e' <- buildFieldData fld e'
    let f' = adjustAnyE (C.StructRepr ctx) $
            \e -> writeStructField ctx idx e e'
    f' me
  where
    errFieldType :: FieldKind tp tp' -> String
    errFieldType fld = "expected field value for " ++ show (adt^.M.adtname, i) ++
        " to have type " ++ show (fieldDataType fld) ++ ", but got " ++ show tpr

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

mapStructField :: M.Adt -> M.Substs -> Int ->
    (MirExp s -> MirGenerator h s ret (MirExp s)) ->
    MirExp s -> MirGenerator h s ret (MirExp s)
mapStructField adt args i f me = do
    StructInfo ctx idx fld <- structInfo adt args i
    let f' = adjustAnyE (C.StructRepr ctx) $
            adjustStructField ctx idx $
            adjustFieldData fld $
            checkSameType ("mapStructField " ++ show i ++ " of " ++ show (adt ^. M.adtname)) $
            f
    f' me


data EnumInfo = forall ctx ctx' tp tp'. EnumInfo
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

enumInfo :: M.Adt -> M.Substs -> Int -> Int -> MirGenerator h s ret EnumInfo
enumInfo adt args i j = do
    when (adt ^. M.adtkind /= M.Enum) $ mirFail $
        "expected enum, but got adt " ++ show (adt ^. M.adtname)

    var <- case adt ^? M.adtvariants . ix i of
        Just var -> return var
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)
    fldTy <- case var ^? M.vfields . ix j of
        Just fld -> return $ M.fieldToTy $ M.substField args fld
        Nothing -> mirFail $ "field index " ++ show j ++ " is out of range for enum " ++
            show (adt ^. M.adtname) ++ " variant " ++ show i

    Some ctx <- return $ enumVariants adt args
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
    Some tpr <- return $ tyToRepr fldTy

    kind <- checkFieldKind (not $ canInitialize fldTy) tpr tpr' $
        "field " ++ show j ++ " of enum " ++ show (adt ^. M.adtname) ++ " variant " ++ show i

    return $ EnumInfo ctx idx ctx' idx' kind

getEnumField :: M.Adt -> M.Substs -> Int -> Int -> MirExp s -> MirGenerator h s ret (MirExp s)
getEnumField adt args i j me = do
    EnumInfo ctx idx ctx' idx' fld <- enumInfo adt args i j
    e <- readAnyE (RustEnumRepr ctx) me
    e <- readEnumVariant ctx idx e
    e <- readStructField ctx' idx' e
    e <- readFieldData' fld errFieldUninit e
    return $ MirExp (R.exprType e) e
  where
    errFieldUninit = "field " ++ show j ++ " of " ++ show (adt^.M.adtname) ++
        " variant " ++ show i ++ " read while uninitialized"


setEnumField :: M.Adt -> M.Substs -> Int -> Int ->
    MirExp s -> MirExp s -> MirGenerator h s ret (MirExp s)
setEnumField adt args i j me (MirExp tpr e') = do
    EnumInfo ctx idx ctx' idx' fld <- enumInfo adt args i j
    Refl <- testEqualityOrFail tpr (fieldDataType fld) (errFieldType fld)
    e' <- buildFieldData fld e'
    let f' = adjustAnyE (RustEnumRepr ctx) $
            adjustEnumVariant ctx idx $
            \e -> writeStructField ctx' idx' e e'
    f' me
  where
    errFieldType :: FieldKind tp tp' -> String
    errFieldType fld = "expected field value for " ++ show (adt^.M.adtname, i, j) ++
        " to have type " ++ show (fieldDataType fld) ++ ", but got " ++ show tpr



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
                Left $ "got Nothing for mandatory field " ++ show (length rest)
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

buildStruct' :: HasCallStack => M.Adt -> M.Substs -> [Maybe (MirExp s)] ->
    MirGenerator h s ret (MirExp s)
buildStruct' adt args es = do
    when (adt ^. M.adtkind /= M.Struct) $ mirFail $
        "expected struct, but got adt " ++ show (adt ^. M.adtname)
    let var = M.onlyVariant adt
    Some fctx <- return $ variantFields' var args
    asn <- case buildStructAssign' fctx $ map (fmap (\(MirExp _ e) -> Some e)) es of
        Left err -> mirFail $ "error building struct " ++ show (var^.M.vname) ++ ": " ++ err
        Right x -> return x
    let ctx = fieldCtxType fctx
    buildAnyE (C.StructRepr ctx) $ R.App $ E.MkStruct ctx asn

buildStruct :: HasCallStack => M.Adt -> M.Substs -> [MirExp s] ->
    MirGenerator h s ret (MirExp s)
buildStruct adt args es =
    buildStruct' adt args (map Just es)


buildEnum' :: HasCallStack => M.Adt -> M.Substs -> Int -> [Maybe (MirExp s)] ->
    MirGenerator h s ret (MirExp s)
buildEnum' adt args i es = do
    when (adt ^. M.adtkind /= M.Enum) $ mirFail $
        "expected enum, but got adt " ++ show (adt ^. M.adtname)

    var <- case adt ^? M.adtvariants . ix i of
        Just var -> return var
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)

    Some ctx <- return $ enumVariants adt args
    Some idx <- case Ctx.intIndex (fromIntegral i) (Ctx.size ctx) of
        Just x -> return x
        Nothing -> mirFail $ "variant index " ++ show i ++ " is out of range for enum " ++
            show (adt ^. M.adtname)
    IsStructType ctx' <- case checkStructType $ ctx Ctx.! idx of
        Just x -> return x
        Nothing -> mirFail $ "variant " ++ show i ++ " of enum " ++
            show (adt ^. M.adtname) ++ " is not a struct?"

    Some fctx' <- return $ variantFields' var args
    asn <- case buildStructAssign' fctx' $ map (fmap (\(MirExp _ e) -> Some e)) es of
        Left err -> mirFail $ "error building variant " ++ show (var^.M.vname) ++ ": " ++ err
        Right x -> return x
    Refl <- testEqualityOrFail (fieldCtxType fctx') ctx' $
        "got wrong fields for " ++ show (adt ^. M.adtname, i) ++ "?"

    discrs <- use $ cs . discrMap . ix (adt ^. M.adtname)
    discr <- case discrs ^? ix i of
        Just x -> return x
        Nothing -> mirFail $ "can't find discr for variant " ++ show (adt ^. M.adtname, i)

    buildAnyE (RustEnumRepr ctx) $
        R.App $ mkRustEnum ctx (R.App $ isizeLit discr) $
        R.App $ E.InjectVariant ctx idx $
        R.App $ E.MkStruct ctx' asn

buildEnum :: HasCallStack => M.Adt -> M.Substs -> Int -> [MirExp s] ->
    MirGenerator h s ret (MirExp s)
buildEnum adt args i es =
    buildEnum' adt args i (map Just es)



fieldDataRef ::
    FieldKind tp tp' ->
    R.Expr MIR s (MirReferenceType tp') ->
    MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
fieldDataRef (FkInit tpr) ref = return ref
fieldDataRef (FkMaybe tpr) ref = subjustRef tpr ref

structFieldRef ::
    M.Adt -> M.Substs -> Int ->
    C.TypeRepr tp -> R.Expr MIR s (MirReferenceType tp) ->
    MirGenerator h s ret (MirPlace s)
structFieldRef adt args i tpr ref = do
    StructInfo ctx idx fld <- structInfo adt args i
    Refl <- testEqualityOrFail tpr C.AnyRepr $
        "structFieldRef: bad referent type: expected Any, but got " ++ show tpr
    ref <- subanyRef (C.StructRepr ctx) ref
    ref <- subfieldRef ctx ref idx
    ref <- fieldDataRef fld ref
    -- TODO: for custom DSTs, we'll need to propagate struct metadata to fields
    return $ MirPlace (fieldDataType fld) ref NoMeta

enumFieldRef ::
    M.Adt -> M.Substs -> Int -> Int ->
    C.TypeRepr tp -> R.Expr MIR s (MirReferenceType tp) ->
    MirGenerator h s ret (MirPlace s)
enumFieldRef adt args i j tpr ref = do
    EnumInfo ctx idx ctx' idx' fld <- enumInfo adt args i j
    Refl <- testEqualityOrFail tpr C.AnyRepr $
        "enumFieldRef: bad referent type: expected Any, but got " ++ show tpr
    ref <- subanyRef (RustEnumRepr ctx) ref
    ref <- subvariantRef ctx ref idx
    ref <- subfieldRef ctx' ref idx'
    ref <- fieldDataRef fld ref
    -- TODO: for custom DSTs, we'll need to propagate enum metadata to fields
    return $ MirPlace (fieldDataType fld) ref NoMeta


enumDiscriminant :: M.Adt -> M.Substs -> MirExp s ->
    MirGenerator h s ret (MirExp s)
enumDiscriminant adt args e = do
    Some ctx <- pure $ enumVariants adt args
    let v = unpackAnyC (RustEnumRepr ctx) e
    return $ MirExp IsizeRepr $ R.App $ rustEnumDiscriminant v

tupleFieldRef ::
    [M.Ty] -> Int ->
    C.TypeRepr tp -> R.Expr MIR s (MirReferenceType tp) ->
    MirGenerator h s ret (MirPlace s)
tupleFieldRef tys i tpr ref = do
    Some ctx <- return $ tyListToCtxMaybe tys $ \ctx -> Some ctx
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



-- Vtable handling

isAutoTraitPredicate :: M.Predicate -> Bool
isAutoTraitPredicate (M.AutoTraitPredicate {}) = True
isAutoTraitPredicate _ = False

-- TODO: make mir-json emit trait vtable layouts for all dyns observed in the
-- crate, then use that info to greatly simplify this function
traitVtableType :: (HasCallStack) =>
    M.TraitName -> M.Trait -> Some C.TypeRepr
traitVtableType tname trait = vtableTy
  where
    convertShimSig sig = clearSigGenerics $ eraseSigReceiver sig

    methodSigs = Maybe.mapMaybe (\ti -> case ti of
        M.TraitMethod name sig -> Just sig
        _ -> Nothing) (trait ^. M.traitItems)
    shimSigs = map convertShimSig methodSigs

    vtableTy = tyListToCtx (map M.TyFnPtr shimSigs) $ \ctx ->
        Some $ C.StructRepr ctx

eraseSigReceiver :: M.FnSig -> M.FnSig
eraseSigReceiver sig = sig & M.fsarg_tys %~ \xs -> case xs of
    [] -> error $ unwords ["dynamic trait method has no receiver", show sig]
    (_ : tys) -> M.TyErased : tys

-- Erase generics, predicates, and associated types
clearSigGenerics :: M.FnSig -> M.FnSig
clearSigGenerics sig = sig
    & M.fsgenerics .~ []
    & M.fspredicates .~ []
    & M.fsassoc_tys .~ []
