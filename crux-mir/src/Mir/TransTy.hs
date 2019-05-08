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

import qualified Data.Maybe as Maybe
import qualified Data.String as String
import qualified Data.Vector as V

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
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.Syntax as S




import qualified Mir.DefId as M
import qualified Mir.Mir as M
import qualified Mir.MirTy as M

import           Mir.PP (fmt)
import           Mir.Generator (MirExp(..), MirGenerator, mkPredVar)
import           Mir.Intrinsics (MIR, pattern MirSliceRepr, pattern MirReferenceRepr, TaggedUnion)


--------------------------------------------------------------------------------------------
-- Reasoning about predicates that we know something about and that should be turned into
-- additional vtable/dictionary arguments 

-- This is a bit of a hack for higher-order functions
-- We always handle these via custom functions so there is
-- no need to pass dictionary arguments for them
-- REVISIT this!
noDictionary :: [M.TraitName]
noDictionary = [M.textId "::ops[0]::function[0]::Fn[0]",
                M.textId "::ops[0]::function[0]::FnMut[0]",
                M.textId "::ops[0]::function[0]::FnOnce[0]"]

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

-- Non-custom ADTs are encoded as a tagged union [Nat, Any]. The first
-- component records which injection is currently being stored; the
-- second component is the injection. Structs and enums are encoded
-- the same -- the only difference is that structs have only one
-- summand. 
--
-- Closures are encoded as Any, but are internally encoded as [Handle,
-- arguments], where arguments is itself a tuple.
--
-- Custom type translation is on the bottom of this file.

type TransTyConstraint = (HasCallStack)   -- (HasCallStack, ?col::M.Collection)


-- | convert a baseSize to a nat repr
-- The BaseSize must *not* be USize.
baseSizeToNatCont :: HasCallStack => M.BaseSize -> (forall w. (1 <= w) => C.NatRepr w -> a) -> a
baseSizeToNatCont M.B8   k = k (knownNat :: NatRepr 8)
baseSizeToNatCont M.B16  k = k (knownNat :: NatRepr 16)
baseSizeToNatCont M.B32  k = k (knownNat :: NatRepr 32)
baseSizeToNatCont M.B64  k = k (knownNat :: NatRepr 64)
baseSizeToNatCont M.B128 k = k (knownNat :: NatRepr 128)
baseSizeToNatCont M.USize _k = error "BUG: Nat is undetermined for usize"


tyToRepr :: TransTyConstraint => M.Ty -> Some C.TypeRepr
tyToRepr t0 = case t0 of
  M.TyBool -> Some C.BoolRepr
  M.TyTuple [] -> Some C.UnitRepr
  
  -- non-empty tuples are mapped to structures of "maybe" types so
  -- that they can be allocated without being initialized
  M.TyTuple ts    -> tyListToCtxMaybe ts $ \repr -> Some (C.StructRepr repr)
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

  -- NOTE: we cannot mutate this vector. Hmmmm....
  M.TySlice t -> tyToReprCont t $ \repr -> Some (C.VectorRepr repr)

  M.TyRef t M.Immut -> tyToRepr t -- immutable references are erased!
  M.TyRef t M.Mut   -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)

  M.TyRawPtr t M.Immut -> tyToRepr t -- immutable pointers are erased
  M.TyRawPtr t M.Mut -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)
  
  M.TyChar -> Some $ C.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes
  
  M.TyCustom custom_t -> customtyToRepr custom_t
  
  -- FIXME: should this be a tuple? 
  M.TyClosure _def_id _substs -> Some C.AnyRepr
  
  -- Strings are vectors of chars
  -- This is not the actual representation (which is packed into u8s)
  M.TyStr -> Some (C.VectorRepr (C.BVRepr (knownNat :: NatRepr 32)))
  
  M.TyAdt _defid _tyargs -> Some taggedUnionRepr
  M.TyDowncast _adt _i   -> Some taggedUnionRepr
  M.TyFloat _ -> Some C.RealValRepr
  M.TyParam i -> case somePeano i of
    Just (Some nr) -> Some (C.VarRepr nr) 
    Nothing        -> error "type params must be nonnegative"

  -- non polymorphic function types go to FunctionHandleRepr
  M.TyFnPtr sig@(M.FnSig args ret [] preds _atys) ->
     tyListToCtx (args ++ Maybe.mapMaybe dictTy preds) $ \argsr  ->
     tyToReprCont ret $ \retr ->
        Some (C.FunctionHandleRepr argsr retr)
        
  -- polymorphic function types go to PolyFnRepr
  -- invariant: never have 0 for PolyFnRepr
  M.TyFnPtr sig@(M.FnSig args ret params preds _atys) ->
     case peanoLength params of
       Some k ->
         tyListToCtx (args ++ Maybe.mapMaybe dictTy preds) $ \argsr ->
         tyToReprCont ret $ \retr ->
            Some (C.PolyFnRepr k argsr retr)

  -- TODO: the only dynamic types that we support are closures
  M.TyDynamic _def -> Some C.AnyRepr
  
  M.TyProjection def _tyargs
   | def == (M.textId "::ops[0]::function[0]::FnOnce[0]::Output[0]")
     -> Some taggedUnionRepr
  M.TyProjection _def _tyargs -> error $ "BUG: all uses of TyProjection should have been eliminated, found "
    ++ fmt t0
  M.TyFnDef _def substs ->
    -- TODO: lookup the type of the function and translate that type
    Some C.AnyRepr
  M.TyLifetime -> Some C.AnyRepr
  _ -> error $ unwords ["unknown type?", show t0]


taggedUnionCtx :: Ctx.Assignment C.TypeRepr ((Ctx.EmptyCtx Ctx.::> C.NatType) Ctx.::> C.AnyType)
taggedUnionCtx = Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr

-- | All ADTs are mapped to tagged unions
taggedUnionRepr :: C.TypeRepr TaggedUnion
taggedUnionRepr = C.StructRepr $ taggedUnionCtx


-- Note: any args on the fields are replaced by args on the variant
variantToRepr :: TransTyConstraint => M.Variant -> M.Substs -> Some C.CtxRepr
variantToRepr (M.Variant _vn _vd vfs _vct) args = 
    tyListToCtx (map M.fieldToTy (map (M.substField args) vfs)) $ \repr -> Some repr



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
unpackAny _ (MirExp tr _) = fail $ "bad anytype, found " ++ fmt tr


unpackAnyE :: HasCallStack => C.TypeRepr t -> MirExp s -> MirExp s
unpackAnyE tr (MirExp C.AnyRepr e) =
   MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) (String.fromString ("Bad Any unpack: " ++ show tr)))
unpackAnyE _ _ = error $ "bad anytype unpack"


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
                  Nothing -> fail "bad type in build array"

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


getAllFieldsMaybe :: MirExp s -> MirGenerator h s ret ([MirExp s])
getAllFieldsMaybe e =
    case e of
      MirExp C.UnitRepr _ -> do
        return []
      MirExp (C.StructRepr ctx) _ -> do
        let s = Ctx.sizeInt (Ctx.size ctx)
        mapM (accessAggregateMaybe e) [0..(s-1)]
      _ -> fail $ "getallfieldsMaybe of non-struct" ++ show e


accessAggregate :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregate (MirExp (C.StructRepr ctx) ag) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      return $ MirExp tpr (S.getStruct idx ag)
accessAggregate (MirExp ty a) b = fail $ "invalid access of " ++ show ty ++ " at location " ++ (show b)

accessAggregateMaybe :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregateMaybe (MirExp (C.StructRepr ctx) ag) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      case tpr of
        C.MaybeRepr tpr' -> let mv = R.App $ E.FromJustValue tpr' (S.getStruct idx ag) (R.App $ E.TextLit "Unitialized aggregate value")
                             in return $ MirExp tpr' mv
        _ -> fail "accessAggregateMaybe: non-maybe struct"
      
accessAggregateMaybe (MirExp ty a) b = fail $ "invalid access of " ++ show ty ++ " at location " ++ (show b)



modifyAggregateIdx :: MirExp s -> -- aggregate to modify
                      MirExp s -> -- thing to insert
                      Int -> -- index
                      MirGenerator h s ret (MirExp s)
modifyAggregateIdx (MirExp (C.StructRepr agctx) ag) (MirExp instr ins) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size agctx) = do
      let tpr = agctx Ctx.! idx
      case (testEquality tpr instr) of
          Just Refl -> return $ MirExp (C.StructRepr agctx) (S.setStruct agctx ag idx ins)
          _ -> fail $ "bad modify, found: " ++ show instr ++ " expected " ++ show tpr
  | otherwise = fail ("modifyAggregateIdx: Index " ++ show i ++ " out of range for struct")
modifyAggregateIdx (MirExp ty _) _ _ =
  do fail ("modfiyAggregateIdx: Expected Crucible structure type, but got:" ++ show ty)


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
                _ -> fail "bad modify"
         _ -> fail "modifyAggregateIdxMaybe: expecting maybe type for struct component"
  | otherwise = fail ("modifyAggregateIdx: Index " ++ show i ++ " out of range for struct")
modifyAggregateIdxMaybe (MirExp ty _) _ _ =
  do fail ("modfiyAggregateIdx: Expected Crucible structure type, but got:" ++ show ty)
