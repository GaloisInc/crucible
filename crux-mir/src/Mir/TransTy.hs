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

module Mir.TransTy where

import Control.Lens
import qualified Data.Maybe as Maybe
import qualified Data.String as String
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
import qualified Lang.Crucible.Substitution()

import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.Syntax as S

import qualified Mir.DefId as M
import qualified Mir.Mir as M
import qualified Mir.MirTy as M

import           Mir.PP (fmt)
import           Mir.Generator (MirExp(..), MirGenerator, mkPredVar, mirFail)
import           Mir.Intrinsics
    ( MIR, pattern MirSliceRepr, pattern MirReferenceRepr
    , RustEnumType, pattern RustEnumRepr, mkRustEnum, rustEnumVariant
    , TaggedUnion, DynRefType)
import           Mir.GenericOps (tySubst)


--------------------------------------------------------------------------------------------
-- Reasoning about predicates that we know something about and that should be turned into
-- additional vtable/dictionary arguments 

-- This is a bit of a hack for higher-order functions
-- We always handle these via custom functions so there is
-- no need to pass dictionary arguments for them
-- REVISIT this!
noDictionary :: [M.TraitName]
noDictionary = []

-- | create a Var corresponding to a trait predicate
dictVar :: M.Predicate -> Maybe M.Var
dictVar (M.TraitPredicate did substs)
  | not (elem did noDictionary)    = Just $ mkPredVar (M.TyAdt did substs)
  | otherwise = Nothing
dictVar (M.TraitProjection _ _)    = Nothing
dictVar M.UnknownPredicate         = Nothing

-- | define the type of a dictionary Var
dictTy  :: M.Predicate -> Maybe M.Ty
dictTy (M.TraitPredicate did substs)
  | not (elem did noDictionary)    = Just $ (M.TyAdt did substs)
  | otherwise                      = Nothing
dictTy (M.TraitProjection _ _)     = Nothing
dictTy M.UnknownPredicate          = Nothing


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
-- Closures are encoded as Any, but are internally encoded as [Handle,
-- arguments], where arguments is itself a tuple.
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
baseSizeToNatCont M.USize _k = error "BUG: Nat is undetermined for usize"


tyToRepr :: TransTyConstraint => M.Ty -> Some C.TypeRepr
tyToRepr t0 = case t0 of
  M.TyAdt "::int512[0]::Int512[0]" (M.Substs []) ->
    Some $ C.BVRepr (knownNat :: NatRepr 512)

  M.TyBool -> Some C.BoolRepr
  M.TyTuple [] -> Some C.UnitRepr
  
  -- non-empty tuples are mapped to structures of "maybe" types so
  -- that they can be allocated without being initialized
  M.TyTuple ts    -> tyListToCtxMaybe ts $ \repr -> Some (C.StructRepr repr)

  -- Closures are just tuples with a fancy name
  M.TyClosure ts  -> tyListToCtxMaybe ts $ \repr -> Some (C.StructRepr repr)

  M.TyArray t _sz -> tyToReprCont t $ \repr -> Some (C.VectorRepr repr)

  -- FIXME, this should be configurable
  M.TyInt M.USize  -> Some C.IntegerRepr
  M.TyUint M.USize -> Some C.NatRepr
  M.TyInt base  -> baseSizeToNatCont base $ \n -> Some $ C.BVRepr n
  M.TyUint base -> baseSizeToNatCont base $ \n -> Some $ C.BVRepr n

  -- These definitions are *not* compositional
  -- What is the translation of "M.TySlice t" by itself?? Maybe just a Vector??
  M.TyRef (M.TySlice t) M.Immut -> tyToReprCont t $ \repr -> Some (C.VectorRepr repr)
  M.TyRef (M.TySlice t) M.Mut   -> tyToReprCont t $ \repr -> Some (MirSliceRepr repr)

  -- Both `&dyn Tr` and `&mut dyn Tr` use the same representation: a pair of a
  -- data value (which is either `&Ty` or `&mut Ty`) and a vtable.  Both are
  -- type-erased (`AnyRepr`), the first because it has to be, and the second
  -- because we'd need to thread the `Collection` into this function (which we
  -- don't want to do) in order to construct the precise vtable type.
  M.TyRef (M.TyDynamic _) _ -> Some $ C.StructRepr $
    Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.AnyRepr

  M.TyRawPtr (M.TyDynamic _) _ -> Some $ C.StructRepr $
    Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.AnyRepr

  -- NOTE: we cannot mutate this vector. Hmmmm....
  M.TySlice t -> tyToReprCont t $ \repr -> Some (C.VectorRepr repr)

  M.TyRef t M.Immut -> tyToRepr t -- immutable references are erased!
  M.TyRef t M.Mut   -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)

  M.TyRawPtr t M.Immut -> tyToRepr t -- immutable pointers are erased
  M.TyRawPtr t M.Mut -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)

  M.TyChar -> Some $ C.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes

  M.TyCustom custom_t -> customtyToRepr custom_t

  -- Strings are vectors of chars
  -- This is not the actual representation (which is packed into u8s)
  M.TyStr -> Some (C.VectorRepr (C.BVRepr (knownNat :: NatRepr 32)))

  -- An ADT is a `concreteAdtRepr` wrapped in `ANY`
  M.TyAdt _defid _tyargs -> Some C.AnyRepr
  M.TyDowncast _adt _i   -> Some C.AnyRepr

  M.TyFloat _ -> Some C.RealValRepr
  M.TyParam i -> case somePeano i of
    Just (Some nr) -> Some (C.VarRepr nr) 
    Nothing        -> error "type params must be nonnegative"

  -- non polymorphic function types go to FunctionHandleRepr
  M.TyFnPtr sig@(M.FnSig args ret [] preds _atys _abi) ->
     tyListToCtx (args ++ Maybe.mapMaybe dictTy preds) $ \argsr  ->
     tyToReprCont ret $ \retr ->
        Some (C.FunctionHandleRepr argsr retr)
        
  -- polymorphic function types go to PolyFnRepr
  -- invariant: never have 0 for PolyFnRepr
  M.TyFnPtr sig@(M.FnSig args ret params preds _atys _abi) ->
     case peanoLength params of
       Some k ->
         tyListToCtx (args ++ Maybe.mapMaybe dictTy preds) $ \argsr ->
         tyToReprCont ret $ \retr ->
            Some (C.PolyFnRepr k argsr retr)

  -- We don't support unsized rvalues.  Currently we error only for standalone
  -- standalone (i.e., not under `TyRef`/`TyRawPtr`) use of `TyDynamic` - we
  -- should do the same for TySlice and TyStr as well.
  M.TyDynamic _preds -> error $ unwords ["standalone use of `dyn` is not supported:", show t0]

  M.TyProjection _def _tyargs -> error $ "BUG: all uses of TyProjection should have been eliminated, found "
    ++ fmt t0
  M.TyFnDef _def substs ->
    -- TODO: lookup the type of the function and translate that type
    Some C.AnyRepr
  M.TyLifetime -> Some C.AnyRepr
  M.TyErased -> Some C.AnyRepr
  _ -> error $ unwords ["unknown type?", show t0]


dynRefCtx :: Ctx.Assignment C.TypeRepr (Ctx.EmptyCtx Ctx.::> C.AnyType Ctx.::> C.AnyType)
dynRefCtx = Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.AnyRepr

dynRefRepr :: C.TypeRepr DynRefType
dynRefRepr = C.StructRepr dynRefCtx


-- Note: any args on the fields are replaced by args on the variant
variantFields :: TransTyConstraint => M.Variant -> M.Substs -> Some C.CtxRepr
variantFields (M.Variant _vn _vd vfs _vct) args = 
    tyListToCtx (map M.fieldToTy (map (M.substField args) vfs)) $ \repr -> Some repr

structFields :: TransTyConstraint => M.Adt -> M.Substs -> Some C.CtxRepr
structFields (M.Adt name kind vs) args
  | kind /= M.Struct = error $ "expected " ++ show name ++ " to have kind Struct"
  | [v] <- vs = variantFields v args
  | otherwise = error $ "expected struct " ++ show name ++ " to have exactly one variant"

enumVariants :: TransTyConstraint => M.Adt -> M.Substs -> Some C.CtxRepr
enumVariants (M.Adt name kind vs) args
  | kind /= M.Enum = error $ "expected " ++ show name ++ " to have kind Enum"
  | otherwise = reprsToCtx variantReprs $ \repr -> Some repr
  where
    variantReprs :: [Some C.TypeRepr]
    variantReprs = map (\v ->
        viewSome (\ctx -> Some $ C.StructRepr ctx) $
        variantFields v args) vs

unionFieldTy :: TransTyConstraint => M.Adt -> M.Substs -> Int -> Some C.TypeRepr
unionFieldTy (M.Adt name kind vs) args idx
  | kind /= M.Union = error $ "expected " ++ show name ++ " to have kind Union"
  | idx >= length vs = error $
    "field index " ++ show idx ++ " out of range for union " ++ show name
  | [v] <- vs = tyToRepr $ M.fieldToTy $ M.substField args $ (v ^. M.vfields) !! idx
  | otherwise = error $ "expected union " ++ show name ++ " to have exactly one variant"



-- As in the CPS translation, functions which manipulate types must be
-- in CPS form, since type tags are generally hidden underneath an
-- existential.

tyToReprCont :: forall a. TransTyConstraint => M.Ty -> (forall tp. HasCallStack => C.TypeRepr tp -> a) -> a
tyToReprCont t f = case tyToRepr t of
                 Some x -> f x

tyListToCtx :: forall a. TransTyConstraint => [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyListToCtx ts f =  go (map tyToRepr ts) Ctx.empty
 where go :: forall ctx. [Some C.TypeRepr] -> C.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)

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



customtyToRepr :: TransTyConstraint => M.CustomTy -> Some C.TypeRepr
customtyToRepr (M.BoxTy t)  = tyToRepr t -- Box<T> is the same as T
customtyToRepr (M.IterTy t) = tyToRepr $ M.TyTuple [M.TySlice t, M.TyUint M.USize]
-- Implement C-style enums as single integers
customtyToRepr (M.CEnum _adt _i) = Some C.IntegerRepr
customtyToRepr ty = error ("FIXME: unimplemented custom type: " ++ fmt ty)


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

unpackAny :: HasCallStack => Some C.TypeRepr -> MirExp s -> MirGenerator h s ret (MirExp s)
unpackAny (Some tr) e@(MirExp C.AnyRepr _) = return $ unpackAnyE tr e
unpackAny _ (MirExp tr _) = mirFail $ "bad anytype, found " ++ fmt tr


unpackAnyE :: HasCallStack => C.TypeRepr t -> MirExp s -> MirExp s
unpackAnyE tpr e = MirExp tpr $ unpackAnyC tpr e

unpackAnyC :: HasCallStack => C.TypeRepr tp -> MirExp s -> R.Expr MIR s tp
unpackAnyC tpr (MirExp C.AnyRepr e) =
    R.App $ E.FromJustValue tpr
        (R.App $ E.UnpackAny tpr e)
        (R.App $ E.TextLit $ "bad unpack: Any as " <> Text.pack (show tpr))
unpackAnyC _ (MirExp tpr' _) = error $ "bad anytype unpack of " ++ show tpr'


-- array in haskell -> crucible array
buildArrayLit :: forall h s tp ret.  C.TypeRepr tp -> [MirExp s] -> MirGenerator h s ret (MirExp s)
buildArrayLit trep exps = do
    vec <- go exps V.empty
    return $ MirExp (C.VectorRepr trep) $  S.app $ E.VectorLit trep vec
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


buildTaggedUnion :: Integer -> [MirExp s] -> MirExp s
buildTaggedUnion i es =
    let v = buildTuple es in
        buildTuple [MirExp knownRepr (S.app $ E.NatLit (fromInteger i)), packAny v ]


mkAssignment :: HasCallStack => C.CtxRepr ctx -> [MirExp s] ->
    Either String (Ctx.Assignment (R.Expr MIR s) ctx)
mkAssignment ctx es = go ctx (reverse es)
  where
    go :: forall ctx s. C.CtxRepr ctx -> [MirExp s] ->
        Either String (Ctx.Assignment (R.Expr MIR s) ctx)
    go ctx [] = case Ctx.viewAssign ctx of
        Ctx.AssignEmpty -> return Ctx.empty
        _ -> fail "not enough expressions"
    go ctx (MirExp tpr e : rest) = case Ctx.viewAssign ctx of
        Ctx.AssignExtend ctx' tpr' -> case testEquality tpr tpr' of
            Nothing -> fail $ "type mismatch: expected " ++ show tpr' ++ " but got " ++
                show tpr ++ " in field " ++ show (length rest)
            Just Refl -> go ctx' rest >>= \flds -> return $ Ctx.extend flds e
        _ -> fail "too many expressions"

-- Build a StructType expr for the variant data
buildVariantData :: HasCallStack => M.Adt -> M.Variant -> M.Substs -> [MirExp s] ->
    MirGenerator h s ret (MirExp s)
buildVariantData adt var args es
  | Some ctx <- variantFields var args
  = case mkAssignment ctx es of
        Left err -> mirFail $ "bad buildVariantData: " ++ err
        Right flds -> return $ MirExp (C.StructRepr ctx) $ R.App $ E.MkStruct ctx flds


-- Convert a `MirExp` for the data of a variant into a MirExp of the
-- `VariantType` itself.
buildVariant :: HasCallStack => M.Adt -> M.Substs -> Int -> MirExp s ->
    MirGenerator h s ret (MirExp s)
buildVariant adt args i (MirExp tpr e)
  | Some ctx <- enumVariants adt args
  , Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx)
  = do
    let tpr' = ctx Ctx.! idx
    Refl <- testEqualityOrFail tpr tpr' $
        "bad buildVariant: found: " ++ show tpr ++ ", expected " ++ show tpr' ++
        " for variant " ++ show i ++ " of " ++ show (adt ^. M.adtname) ++ " " ++ show args
    let discr = R.App $ E.IntLit $ fromIntegral i
    return $ MirExp (RustEnumRepr ctx)
        (R.App $ mkRustEnum ctx discr $ R.App $ E.InjectVariant ctx idx e)
  | otherwise = mirFail $
    "buildVariant: index " ++ show i ++ " out of range for " ++ show (adt ^. M.adtname)


getAllFieldsMaybe :: MirExp s -> MirGenerator h s ret ([MirExp s])
getAllFieldsMaybe e =
    case e of
      MirExp C.UnitRepr _ -> do
        return []
      MirExp (C.StructRepr ctx) _ -> do
        let s = Ctx.sizeInt (Ctx.size ctx)
        mapM (accessAggregateMaybe e) [0..(s-1)]
      _ -> mirFail $ "getallfieldsMaybe of non-struct" ++ show e


accessAggregate :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregate (MirExp (C.StructRepr ctx) ag) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      return $ MirExp tpr (S.getStruct idx ag)
accessAggregate (MirExp ty a) b = mirFail $ "invalid access of " ++ show ty ++ " at location " ++ (show b)

accessAggregateMaybe :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregateMaybe (MirExp (C.StructRepr ctx) ag) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      case tpr of
        C.MaybeRepr tpr' -> let mv = R.App $ E.FromJustValue tpr' (S.getStruct idx ag) (R.App $ E.TextLit "Unitialized aggregate value")
                             in return $ MirExp tpr' mv
        _ -> mirFail "accessAggregateMaybe: non-maybe struct"
      
accessAggregateMaybe (MirExp ty a) b = mirFail $ "invalid access of " ++ show ty ++ " at location " ++ (show b)


accessVariant :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessVariant (MirExp (RustEnumRepr ctx) v) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      let proj = R.App $ E.ProjectVariant ctx idx $ R.App $ rustEnumVariant ctx v
      e <- G.fromJustExpr proj $ R.App $ E.TextLit $
        "invalid access of wrong variant " <> Text.pack (show i)
      return $ MirExp tpr e
accessVariant (MirExp ty a) b = mirFail $ "invalid access of " ++ show ty ++ " at location " ++ (show b)




modifyAggregateIdx :: MirExp s -> -- aggregate to modify
                      MirExp s -> -- thing to insert
                      Int -> -- index
                      MirGenerator h s ret (MirExp s)
modifyAggregateIdx (MirExp (C.StructRepr agctx) ag) (MirExp instr ins) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size agctx) = do
      let tpr = agctx Ctx.! idx
      case (testEquality tpr instr) of
          Just Refl -> return $ MirExp (C.StructRepr agctx) (S.setStruct agctx ag idx ins)
          _ -> mirFail $ "bad modify, found: " ++ show instr ++ " expected " ++ show tpr
  | otherwise = mirFail ("modifyAggregateIdx: Index " ++ show i ++ " out of range for struct")
modifyAggregateIdx (MirExp ty _) _ _ =
  do mirFail ("modifyAggregateIdx: Expected Crucible structure type, but got:" ++ show ty)

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
  | otherwise = mirFail ("modifyAggregateIdx: Index " ++ show i ++ " out of range for struct")
modifyAggregateIdxMaybe (MirExp ty _) _ _ =
  do mirFail ("modifyAggregateIdx: Expected Crucible structure type, but got:" ++ show ty)


-- Adjust the contents of an ANY value.  Requires knowing the current concrete
-- type.  The function must return a `MirExp` of the same type as input - that
-- is, this function does not allow changing the underlying type of the `ANY`.
adjustAny ::
    C.TypeRepr tp ->
    (MirExp s -> MirGenerator h s ret (MirExp s)) ->
    MirExp s -> MirGenerator h s ret (MirExp s)
adjustAny tpr f (MirExp C.AnyRepr a) = do
    let oldValOpt = R.App $ E.UnpackAny tpr a
    oldVal <- G.fromJustExpr oldValOpt $ R.App $ E.TextLit $
        "invalid ANY unpack at type " <> Text.pack (show tpr)
    MirExp tpr' newVal <- f (MirExp tpr oldVal)
    Refl <- testEqualityOrFail tpr tpr' $
        "bad any adjust, found: " ++ show tpr' ++ ", expected " ++ show tpr
    return $ MirExp C.AnyRepr (R.App $ E.PackAny tpr newVal)

-- Adjust the contents of a struct field.
adjustStructField ::
    Int ->
    (MirExp s -> MirGenerator h s ret (MirExp s)) ->
    MirExp s -> MirGenerator h s ret (MirExp s)
adjustStructField i f (MirExp (C.StructRepr ctx) st)
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
    let tpr = ctx Ctx.! idx
    let oldVal = S.getStruct idx st
    MirExp tpr' newVal <- f (MirExp tpr oldVal)
    Refl <- testEqualityOrFail tpr tpr' $
        "bad struct field adjust, found: " ++ show tpr' ++ ", expected " ++ show tpr
    return $ MirExp (C.StructRepr ctx) (S.setStruct ctx st idx newVal)
  | otherwise = mirFail ("adjustStructField: Index " ++ show i ++ " out of range for variant")
adjustStructField _ _ (MirExp ty _) =
  do mirFail ("adjustStructField: Expected Crucible variant type, but got:" ++ show ty)

adjustVariant :: 
    Int ->
    (MirExp s -> MirGenerator h s ret (MirExp s)) ->
    MirExp s -> MirGenerator h s ret (MirExp s)
adjustVariant i f (MirExp (RustEnumRepr ctx) v)
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      let oldValOpt = R.App $ E.ProjectVariant ctx idx $ R.App $ rustEnumVariant ctx v
      oldVal <- G.fromJustExpr oldValOpt $ R.App $ E.TextLit $
        "invalid adjust of wrong variant " <> Text.pack (show i)
      MirExp tpr' newVal <- f (MirExp tpr oldVal)
      Refl <- testEqualityOrFail tpr tpr' $
        "bad variant adjust, found: " ++ show tpr' ++ ", expected " ++ show tpr
      let discr = R.App $ E.IntLit $ fromIntegral i
      return $ MirExp (RustEnumRepr ctx)
        (R.App $ mkRustEnum ctx discr $ R.App $ E.InjectVariant ctx idx newVal)
  | otherwise = mirFail ("adjustVariant: Index " ++ show i ++ " out of range for variant")
adjustVariant _ _ (MirExp ty _) =
  do mirFail ("adjustVariant: Expected Crucible variant type, but got:" ++ show ty)

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
    M.TraitName -> M.Trait -> M.Substs -> [M.Predicate] -> Some C.TypeRepr
traitVtableType tname _ _ ps
  | any (not . isAutoTraitPredicate) ps =
    -- We don't yet support things like `dyn Iterator<Item = u8>`, which
    -- manifests as `TraitProjection` predicates constraining the type of
    -- `Iterator::Item<Self>`.
    error $ unwords ["unsupported predicate(s)",
        show $ filter (not . isAutoTraitPredicate) ps,
        "for trait", show tname]
traitVtableType tname trait substs _
  | not $ all (== tname) $ trait ^. M.traitSupers =
    -- We don't yet support traits with supertraits.  This would require
    -- collecting up all the trait items from the entire tree into one big
    -- vtable.
    error $ unwords ["trait", show tname, "has nonempty supertraits (unsupported):",
        show $ trait ^. M.traitSupers]
  | not $ all (== M.TraitPredicate tname dummySubsts) $ trait ^. M.traitPredicates =
    -- A predicate `Self: OtherTrait` works the same as a supertrait.  Other
    -- predicates might be okay.
    error $ unwords ["trait", show tname, "has nonempty predicates (unsupported):",
        show $ trait ^. M.traitPredicates, show tname, show dummySubsts]
  where
    -- NB: no -1 on the length.  The `substs` arguments is the substs for the
    -- trait, not including Self - but Self *is* included in `dummySubsts`.
    dummySubsts = M.Substs [M.TyParam (fromIntegral i) | i <- [0 .. M.lengthSubsts substs]]
traitVtableType tname trait substs _ = vtableTy
  where
    -- The substitutions that turn the method signature (generic, from the
    -- trait declaration) into the signature of the vtable shim.  These are the
    -- `substs` from the TraitPredicate, plus one more type to use for `Self`.
    shimSubsts = M.insertAtSubsts (M.Substs [dummySelf]) 0 substs

    -- We specially replace the receiver argument with TyErased, and that's the
    -- only place `Self` (`TyParam 0`) should appear, assuming the method is
    -- properly object-safe.  Thus, the first entry in the `shimSubsts` should
    -- never be evaluated.
    dummySelf :: M.Ty
    dummySelf = errNotObjectSafe ["tried to use Self outside receiver position"]

    convertShimSig sig = tySubst shimSubsts $ clearSigGenerics $ eraseSigReceiver sig

    methodSigs = Maybe.mapMaybe (\ti -> case ti of
        M.TraitMethod name sig -> Just sig
        _ -> Nothing) (trait ^. M.traitItems)
    shimSigs = map convertShimSig methodSigs

    vtableTy = tyListToCtx (map M.TyFnPtr shimSigs) $ \ctx ->
        Some $ C.StructRepr ctx

    errNotObjectSafe :: [String] -> a
    errNotObjectSafe parts = error $ unwords $
        ["a method of trait", show tname, "is not object safe:"] ++ parts

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
