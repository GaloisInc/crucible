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

{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}

module Mir.Trans where

import Control.Monad
import Control.Monad.ST
import Control.Lens hiding (op,(|>))
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Data.String (fromString)
import Numeric
import Numeric.Natural

import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.FunctionHandle as FH
import qualified What4.ProgramLoc as PL
import qualified What4.FunctionName as FN
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.SSAConversion as SSA
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Syntax as S
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.Substitution as C


import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableFC as Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.Peano
import Data.Parameterized.BoolRepr
import Data.Parameterized.WithRepr

import Mir.Mir
import Mir.MirTy
import qualified Mir.Mir as M
import qualified Mir.DefId as M
import qualified Mir.MirTy as M

import Mir.Intrinsics
import Mir.Generator
import Mir.GenericOps

import Mir.Pass.ExpandSuperTraits
import Mir.Pass.AssociatedTypes

import Mir.PP(ppreds,fmt)
import Text.PrettyPrint.ANSI.Leijen(Pretty(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import GHC.Stack

import Unsafe.Coerce
import Debug.Trace

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
-- summand. (Note that this means that symbolic ADTs don't work yet,
-- since we are working with Anys.)
--
-- Closures are encoded as Any, but are internally encoded as [Handle,
-- arguments], where arguments is itself a tuple.
--
-- Custom type translation is on the bottom of this file.

-- | convert a baseSize to a nat repr
-- The BaseSize must *not* be USize.
baseSizeToNatCont :: HasCallStack => M.BaseSize -> (forall w. (1 <= w) => C.NatRepr w -> a) -> a
baseSizeToNatCont M.B8   k = k (knownNat :: NatRepr 8)
baseSizeToNatCont M.B16  k = k (knownNat :: NatRepr 16)
baseSizeToNatCont M.B32  k = k (knownNat :: NatRepr 32)
baseSizeToNatCont M.B64  k = k (knownNat :: NatRepr 64)
baseSizeToNatCont M.B128 k = k (knownNat :: NatRepr 128)
baseSizeToNatCont M.USize _k = error "BUG: Nat is undetermined for usize"


tyToRepr :: HasCallStack => M.Ty -> Some C.TypeRepr
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

  M.TySlice t -> tyToReprCont t $ \repr -> Some (C.VectorRepr repr)

  M.TyRef t M.Immut -> tyToRepr t -- immutable references are erased!
  M.TyRef t M.Mut   -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)

  M.TyRawPtr t M.Immut -> tyToRepr t -- immutable pointers are erased
  M.TyRawPtr t M.Mut -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)
  
  M.TyChar -> Some $ C.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes
  M.TyCustom custom_t -> customtyToRepr custom_t
  -- FIXME: should this be a tuple? 
  M.TyClosure _def_id _substs -> Some C.AnyRepr
  M.TyStr -> Some C.StringRepr
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
        
  M.TyDynamic _def -> Some C.AnyRepr
--  M.TyProjection _def _tyargs -> Some taggedUnionRepr
  M.TyProjection _def _tyargs -> error $ "BUG: all uses of TyProjection should have been eliminated, found "
    ++ show (pretty t0) 
  M.TyFnDef _def substs -> Some C.AnyRepr
  _ -> error $ unwords ["unknown type?", show t0]


taggedUnionCtx :: Ctx.Assignment C.TypeRepr ((Ctx.EmptyCtx Ctx.::> C.NatType) Ctx.::> C.AnyType)
taggedUnionCtx = Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr

-- | All ADTs are mapped to tagged unions
taggedUnionRepr :: C.TypeRepr TaggedUnion
taggedUnionRepr = C.StructRepr $ taggedUnionCtx


-- Note: any args on the fields are replaced by args on the variant
variantToRepr :: HasCallStack => M.Variant -> Substs -> Some C.CtxRepr
variantToRepr (M.Variant _vn _vd vfs _vct) args = 
    tyListToCtx (map M.fieldToTy (map (M.substField args) vfs)) $ \repr -> Some repr



-- As in the CPS translation, functions which manipulate types must be
-- in CPS form, since type tags are generally hidden underneath an
-- existential.

tyToReprCont :: forall a. HasCallStack => M.Ty -> (forall tp. HasCallStack => C.TypeRepr tp -> a) -> a
tyToReprCont t f = case tyToRepr t of
                 Some x -> f x

tyListToCtx :: forall a. HasCallStack => [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
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
tyListToCtxMaybe :: forall a. HasCallStack => [M.Ty] -> (forall ctx. C.CtxRepr ctx -> a) -> a
tyListToCtxMaybe ts f =  go (map tyToRepr ts) Ctx.empty
 where go :: forall ctx. [Some C.TypeRepr] -> C.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> C.MaybeRepr tp)


-- | Translate a Mir type substitution to a Crucible type substitution
substToSubstCont :: HasCallStack => Substs -> (forall subst. C.CtxRepr subst -> a) -> a
substToSubstCont (Substs []) f        = f Ctx.empty
substToSubstCont (Substs (ty:rest)) f =
  tyToReprCont ty $ \tyr ->
    substToSubstCont (Substs rest) $ \rr ->
       f (rr `Ctx.extend` tyr)

-----------------------------------------------------------------------







   

-----------
-- ** MIR intrinsics Generator interaction

newMirRef ::
  C.TypeRepr tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
newMirRef tp = G.extensionStmt (MirNewRef tp)

dropMirRef ::
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret ()
dropMirRef refExp = void $ G.extensionStmt (MirDropRef refExp)

readMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret (R.Expr MIR s tp)
readMirRef tp refExp = G.extensionStmt (MirReadRef tp refExp)

writeMirRef ::
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s tp ->
  MirGenerator h s ret ()
writeMirRef ref x = void $ G.extensionStmt (MirWriteRef ref x)

subfieldRef ::
  C.CtxRepr ctx ->
  R.Expr MIR s (MirReferenceType TaggedUnion) ->
  Ctx.Index ctx tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subfieldRef ctx ref idx = G.extensionStmt (MirSubfieldRef ctx ref idx)

subindexRef ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType (C.VectorType tp)) ->
  R.Expr MIR s C.NatType ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subindexRef tp ref idx = G.extensionStmt (MirSubindexRef tp ref idx)

-----------
-- ** Expression generation

packBase
    :: HasCallStack => C.TypeRepr tp
    -> C.CtxRepr ctx
    -> Ctx.Assignment (R.Atom s) ctx
    -> (forall ctx'. Some (R.Atom s) -> C.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a)
    -> a
packBase ctp ctx0 asgn k =
  case Ctx.viewAssign ctx0 of
    Ctx.AssignEmpty -> error "packType: ran out of actual arguments!"
    Ctx.AssignExtend ctx' ctp' ->
      case testEquality ctp ctp' of
        Nothing -> error $ unwords ["crucible type mismatch: given",show ctp,"but ctxrepr had", show ctp', "even though ctx was", show ctx0]
        Just Refl ->
          let asgn' = Ctx.init asgn
              idx   = Ctx.nextIndex (Ctx.size asgn')
           in k (Some (asgn Ctx.! idx))
                ctx'
                asgn'

unfold_ctx_assgn
    :: HasCallStack =>
       M.Ty
    -> C.CtxRepr ctx
    -> Ctx.Assignment (R.Atom s) ctx
    -> (forall ctx'. Some (R.Atom s) -> C.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a)
    -> a
unfold_ctx_assgn tp ctx asgn k =
    tyToReprCont tp $ \repr ->
        packBase repr ctx asgn k

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



parsePosition :: Text.Text -> PL.Position
parsePosition posText =
  case Text.split (==':') posText of
    [fname,line,col,_line2,_col2]
      | (l,[]):_ <- readDec (Text.unpack line)
      , (c,[]):_ <- readDec (Text.unpack col)
      -> PL.SourcePos fname l c
    [fname,line,col]
      | (l,[]):_ <- readDec (Text.unpack line)
      , (c,[]):_ <- readDec (Text.unpack col)
      -> PL.SourcePos fname l c
    _ -> PL.OtherPos posText


setPosition :: Text.Text -> MirGenerator h s ret ()
setPosition = G.setPosition . parsePosition

--------------------------------------------------------------------------------------
-- ** Expressions


-- Expressions: variables and constants
--

transConstVal :: HasCallStack => Some C.TypeRepr -> M.ConstVal -> MirGenerator h s ret (MirExp s)
transConstVal (Some (C.BVRepr w)) (M.ConstInt i) =
    return $ MirExp (C.BVRepr w) (S.app $ E.BVLit w (fromInteger (M.fromIntegerLit i)))
transConstVal (Some (C.BoolRepr)) (M.ConstBool b) = return $ MirExp (C.BoolRepr) (S.litExpr b)
transConstVal (Some (C.NatRepr)) (M.ConstInt i) =
    do let n = fromInteger (M.fromIntegerLit i)
       return $ MirExp C.NatRepr (S.app $ E.NatLit n)
transConstVal (Some (C.IntegerRepr)) (ConstInt i) =
      return $ MirExp C.IntegerRepr (S.app $ E.IntLit (fromIntegerLit i))
transConstVal (Some (C.StringRepr)) (M.ConstStr str) =
    do let t = Text.pack str
       return $ MirExp C.StringRepr (S.litExpr t)
transConstVal (Some (C.BVRepr w)) (M.ConstChar c) =
    do let i = toInteger (Char.ord c)
       return $ MirExp (C.BVRepr w) (S.app $ E.BVLit w i)
transConstVal (Some (C.AnyRepr)) (M.ConstFunction did _substs) =
    -- TODO: use this substs
    buildClosureHandle did (Substs []) []

transConstVal (Some (C.RealValRepr)) (M.ConstFloat (M.FloatLit _ str)) =
    case reads str of
      (d , _):_ -> let rat = toRational (d :: Double) in
                   return (MirExp C.RealValRepr (S.app $ E.RationalLit rat))
      []        -> fail $ "cannot parse float constant: " ++ show str
transConstVal tp cv = fail $ "fail or unimp constant: " ++ (show tp) ++ " " ++ (show cv)


lookupVar :: HasCallStack => M.Var -> MirGenerator h s ret (MirExp s)
lookupVar (M.Var vname _ vty _ pos) = do
    vm <- use varMap
    case (Map.lookup vname vm, tyToRepr vty) of
      (Just (Some varinfo), Some vtr)
        | Just C.Refl <- C.testEquality vtr (varInfoRepr varinfo) ->
            case varinfo of
              VarRegister reg ->
                do r <- G.readReg reg
                   return $ MirExp vtr r
              VarReference reg ->
                do r <- readMirRef vtr =<< G.readReg reg
                   return $ MirExp vtr r
              VarAtom a ->
                do return $ MirExp vtr (R.AtomExpr a)

        | otherwise -> fail ("bad type in lookupVar: " <> show vname <> " at " <> Text.unpack pos <>
                             "\n\t expected " <> show vtr <> " found " <> show (varInfoRepr varinfo))
      _ -> error ("register not found: " <> show vname <> " at " <> Text.unpack pos)

-- NOTE: The return var in the MIR output is always "_0"
lookupRetVar :: HasCallStack => C.TypeRepr ret -> MirGenerator h s ret (R.Expr MIR s ret)
lookupRetVar tr = do
    vm <- use varMap
    case (Map.lookup "_0" vm) of
      Just (Some varinfo) ->
        case  C.testEquality tr (varInfoRepr varinfo) of 
          Just C.Refl ->
            case varinfo of
              VarRegister reg ->
                do G.readReg reg
              VarReference reg ->
                do readMirRef tr =<< G.readReg reg
              VarAtom a ->
                do return (R.AtomExpr a)
          Nothing -> fail $ "return register has wrong type. Expected: "
                       ++ show tr ++ "\n Found " ++ show (varInfoRepr varinfo)

      _ -> fail $ "reg not found in retvar " ++ show (Map.keys vm)


-- ** Expressions: Operations and Aggregates

-- TODO: what is the difference between a Move and a Copy?
evalOperand :: HasCallStack => M.Operand -> MirGenerator h s ret (MirExp s)
evalOperand (M.Copy lv) = evalLvalue lv
evalOperand (M.Move lv) = evalLvalue lv
evalOperand (M.OpConstant (M.Constant conty conlit)) =
    case conlit of
       M.Value constval   -> transConstVal (tyToRepr conty) constval
       M.Item defId _args -> fail $ "cannot translate item " ++ show defId
       M.LPromoted prom   -> fail $ "cannot translate promoted " ++ show prom


-- Given two bitvectors, extend the length of the shorter one so that they
-- have the same length
-- Use the sign of the first bitvector to determine how to sign extend
extendToMax :: (1 <= n, 1 <= m) =>
               NatRepr n -> G.Expr MIR s (C.BVType n) ->
               NatRepr m -> G.Expr MIR s (C.BVType m) -> Maybe M.ArithType ->
   (forall n. (1 <= n) => NatRepr n -> G.Expr MIR s (C.BVType n) -> G.Expr MIR s (C.BVType n) -> a) -> a
extendToMax n e1 m e2 (Just arith) k =
   let extend :: (1 <= w, 1 <= r, w+1 <= r) => (NatRepr r)
         -> (NatRepr w)
         -> (f (C.BVType w))
         -> E.App MIR f (C.BVType r)
       extend = case arith of
                  M.Signed   -> E.BVSext
                  M.Unsigned -> E.BVZext
   in case testEquality n m of
      Just Refl -> k n e1 e2
      Nothing   -> case testLeq (incNat n) m of
                      Just LeqProof ->
                         k m (S.app $ extend m n e1) e2
                      Nothing -> case testLeq (incNat m) n of
                          Just LeqProof ->
                              k n e1 (S.app $ extend n m e2)
                          Nothing -> error "impossible case"
extendToMax n e1 m e2 Nothing k = 
   case testEquality n m of
      Just Refl -> k n e1 e2
      Nothing   -> error "don't know the sign"


-- Rust implements left and right shift operations via the trait

transBinOp :: M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
transBinOp bop op1 op2 = do
    me1 <- evalOperand  op1
    me2 <- evalOperand  op2
    evalBinOp bop (M.arithType op1) me1 me2

evalBinOp :: M.BinOp -> Maybe M.ArithType -> MirExp s -> MirExp s -> MirGenerator h s ret (MirExp s)
evalBinOp bop mat me1 me2 = 
    case (me1, me2) of
      (MirExp ty1@(C.BVRepr na) e1a, MirExp ty2@C.NatRepr e2a) ->
         case (bop, mat) of
            (M.Shl, _) -> do
                let e2bv = S.app (E.IntegerToBV na (S.app (E.NatToInteger e2a)))
                return $ MirExp (C.BVRepr na) (S.app $ E.BVShl na e1a e2bv)
            (M.Shr, Just M.Unsigned) -> do
                let e2bv = S.app (E.IntegerToBV na (S.app (E.NatToInteger e2a)))
                return $ MirExp (C.BVRepr na) (S.app $ E.BVLshr na e1a e2bv)
            (M.Shr, Just M.Signed) -> do
                let e2bv = S.app (E.IntegerToBV na (S.app (E.NatToInteger e2a)))
                return $ MirExp (C.BVRepr na) (S.app $ E.BVAshr na e1a e2bv)

            _ -> fail $ "bad binop: " ++ show bop ++ " for " ++ show ty1 ++ " and " ++ show ty2
      (MirExp ty1@(C.BVRepr na) e1a, MirExp ty2@(C.BVRepr ma) e2a) ->
          -- if the BVs are not the same width extend the shorter one
          extendToMax na e1a ma e2a (mat) $ \ n e1 e2 -> 
            case (bop, mat) of
              (M.Add, _) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVAdd n e1 e2)
              (M.Sub, _) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVSub n e1 e2)
              (M.Mul, _) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVMul n e1 e2)
              (M.Div, Just M.Unsigned) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVUdiv n e1 e2)
              (M.Div, Just M.Signed) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVSdiv n e1 e2)
              (M.Rem, Just M.Unsigned) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVUrem n e1 e2)
              (M.Rem, Just M.Signed) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVSrem n e1 e2)
              (M.BitXor, _) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVXor n e1 e2)
              (M.BitAnd, _) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVAnd n e1 e2)
              (M.BitOr, _) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVOr n e1 e2)
              (M.Shl, _) ->
                 let res = MirExp (C.BVRepr n) (S.app $ E.BVShl n e1 e2)
                 -- TODO check unsigned vs signed???
                 in extendUnsignedBV res na
              (M.Shr, Just M.Unsigned) ->
                 let res = MirExp (C.BVRepr n) (S.app $ E.BVLshr n e1 e2)
                 in extendUnsignedBV res na
              (M.Shr, Nothing) ->
                 let res = MirExp (C.BVRepr n) (S.app $ E.BVLshr n e1 e2)
                 in extendUnsignedBV res na
              (M.Shr, Just M.Signed) ->
                 let res = MirExp (C.BVRepr n) (S.app $ E.BVAshr n e1 e2) 
                 in extendSignedBV res na
              (M.Lt, Just M.Unsigned) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVUlt n e1 e2)
              (M.Lt, Just M.Signed) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVSlt n e1 e2)
              (M.Le, Just M.Unsigned) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVUle n e1 e2)
              (M.Le, Just M.Signed) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVSle n e1 e2)

              (M.Gt, Just M.Unsigned) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVUle n e2 e1)
              (M.Gt, Just M.Signed) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVSle n e2 e1)
              (M.Ge, Just M.Unsigned) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVUlt n e2 e1)
              (M.Ge, Just M.Signed) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVSlt n e2 e1)

              (M.Ne, _) -> return $ MirExp (C.BoolRepr) (S.app $ E.Not $ S.app $ E.BVEq n e1 e2)
              (M.Beq, _) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVEq n e1 e2)
              _ -> fail $ "bad binop: " ++ show bop ++ " for " ++ show ty1 ++ " and " ++ show ty2
      (MirExp C.BoolRepr e1, MirExp C.BoolRepr e2) ->
          case bop of
            M.BitAnd -> return $ MirExp C.BoolRepr (S.app $ E.And e1 e2)
            M.BitXor -> return $ MirExp C.BoolRepr (S.app $ E.BoolXor e1 e2)
            M.BitOr -> return $ MirExp C.BoolRepr (S.app $ E.Or e1 e2)
            M.Beq -> return $ MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.BoolXor e1 e2)
            _ -> fail "bad binop"
      (MirExp C.NatRepr e1, MirExp C.NatRepr e2) ->
          case bop of
            M.Beq -> return $ MirExp C.BoolRepr (S.app $ E.NatEq e1 e2)
            M.Lt -> return $ MirExp C.BoolRepr (S.app $ E.NatLt e1 e2)
            M.Le -> return $ MirExp C.BoolRepr (S.app $ E.NatLe e1 e2)
            M.Gt -> return $ MirExp C.BoolRepr (S.app $ E.NatLe e2 e1)
            M.Ge -> return $ MirExp C.BoolRepr (S.app $ E.NatLt e2 e1)

            M.Add -> return $ MirExp C.NatRepr (S.app $ E.NatAdd e1 e2)
            M.Sub -> return $ MirExp C.NatRepr (S.app $ E.NatSub e1 e2)
            M.Mul -> return $ MirExp C.NatRepr (S.app $ E.NatMul e1 e2)
            M.Ne -> return $ MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.NatEq e1 e2)
            _ -> fail "bad natural number binop"
      (MirExp C.RealValRepr e1, MirExp C.RealValRepr e2) ->
          case bop of
            M.Beq -> return $ MirExp C.BoolRepr (S.app $ E.RealEq e1 e2)
            M.Lt -> return $ MirExp C.BoolRepr (S.app $ E.RealLt e1 e2)
            M.Le -> return $ MirExp C.BoolRepr (S.app $ E.RealLe e1 e2)
            M.Gt -> return $ MirExp C.BoolRepr (S.app $ E.RealLe e2 e1)
            M.Ge -> return $ MirExp C.BoolRepr (S.app $ E.RealLt e2 e1)

            M.Add -> return $ MirExp C.RealValRepr (S.app $ E.RealAdd e1 e2)
            M.Sub -> return $ MirExp C.RealValRepr (S.app $ E.RealSub e1 e2)
            M.Mul -> return $ MirExp C.RealValRepr (S.app $ E.RealMul e1 e2)
            M.Ne -> return $ MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.RealEq e1 e2)
            _ -> fail "bad natural number binop"

      (_, _) -> fail $ "bad or unimplemented type: " ++ (show bop) ++ ", " ++ (show me1) ++ ", " ++ (show me2)



transCheckedBinOp ::  M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s) -- returns tuple of (result, bool)
transCheckedBinOp  a b c = do
    res <- transBinOp a b c
    return $ buildTupleMaybe [error "not needed", TyBool] [Just res, Just $ MirExp (C.BoolRepr) (S.litExpr False)]
         -- This always succeeds, since we're checking correctness. We can also check for overflow if desired.


-- Nullary ops in rust are used for resource allocation, so are not interpreted
transNullaryOp ::  M.NullOp -> M.Ty -> MirGenerator h s ret (MirExp s)
transNullaryOp _ _ = fail "nullop"

transUnaryOp :: M.UnOp -> M.Operand -> MirGenerator h s ret (MirExp s)
transUnaryOp uop op = do
    mop <- evalOperand op
    case (uop, mop) of
      (M.Not, MirExp C.BoolRepr e) -> return $ MirExp C.BoolRepr $ S.app $ E.Not e
      (M.Neg, MirExp (C.BVRepr n) e) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVSub n (S.app $ E.BVLit n 0) e)
      _ -> fail "bad op or type for unary"


-- a -> u -> [a;u]
buildRepeat :: M.Operand -> M.ConstUsize -> MirGenerator h s ret (MirExp s)
buildRepeat op size = do
    (MirExp tp e) <- evalOperand op
    let n = fromInteger size
    return $ MirExp (C.VectorRepr tp) (S.app $ E.VectorReplicate tp (S.app $ E.NatLit n) e)

buildRepeat_ :: M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
buildRepeat_ op size = do
    let (M.OpConstant (M.Constant _ (M.Value (M.ConstInt i)))) = size
    buildRepeat op (M.fromIntegerLit i)


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

buildTupleMaybe :: [Ty] -> [Maybe (MirExp s)] -> MirExp s
buildTupleMaybe tys xs = exp_to_assgn_Maybe tys xs $ \ctx asgn ->
    MirExp (C.StructRepr ctx) (S.app $ E.MkStruct ctx asgn)


buildTaggedUnion :: Integer -> [MirExp s] -> MirExp s
buildTaggedUnion i es =
    let v = buildTuple es in
        buildTuple [MirExp knownRepr (S.app $ E.NatLit (fromInteger i)), packAny v ]

buildTaggedUnion' :: Integer -> MirExp s -> MirExp s -- second argument is already a struct
buildTaggedUnion' i v =
    buildTuple [MirExp knownRepr (S.app $ E.NatLit (fromInteger i)), packAny v ]

getAllFields :: MirExp s -> MirGenerator h s ret ([MirExp s])
getAllFields e =
    case e of
      MirExp C.UnitRepr _ -> do
        return []
      MirExp (C.StructRepr ctx) _ -> do
        let s = Ctx.sizeInt (Ctx.size ctx)
        mapM (accessAggregate e) [0..(s-1)]
      _ -> fail $ "getallfields of non-struct" ++ show e


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
          _ -> fail "bad modify"
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


-- casts

-- | Make sure that the expression has exactly the bitwidth requested. If the BV is too short, extend. If too long, truncate.
extendUnsignedBV :: (1 <= w) => MirExp s -> NatRepr w -> MirGenerator h s ret (MirExp s)
extendUnsignedBV (MirExp tp e) w = 
    case tp of
      (C.BVRepr n) | Just Refl <- testEquality w n ->
                return $ MirExp tp e
      (C.BVRepr n) | Just LeqProof <- testLeq (incNat w) n ->
                return $ MirExp (C.BVRepr w) (S.app $ E.BVTrunc w n e)
      (C.BVRepr n) | Just LeqProof <- testLeq (incNat n) w ->
                return $ MirExp (C.BVRepr w) (S.app $ E.BVZext w n e)
      _ -> fail ("unimplemented unsigned bvext: " ++ show tp ++ "  " ++ show w)

extendSignedBV :: (1 <= w) => MirExp s -> NatRepr w -> MirGenerator h s ret (MirExp s)
extendSignedBV (MirExp tp e) w = 
    case tp of
      (C.BVRepr n) | Just Refl <- testEquality w n ->
                return $ MirExp tp e
      (C.BVRepr n) | Just LeqProof <- testLeq (incNat w) n ->
                return $ MirExp (C.BVRepr w) (S.app $ E.BVTrunc w n e)
      (C.BVRepr n) | Just LeqProof <- testLeq (incNat n) w ->
                return $ MirExp (C.BVRepr w) (S.app $ E.BVSext w n e)
      _ -> fail $ "unimplemented signed bvext" ++ show tp ++ " " ++ show w


evalCast' :: M.CastKind -> M.Ty -> MirExp s -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast' ck ty1 e ty2  =
    case (ck, ty1, ty2) of
      (M.Misc,a,b) | a == b -> return e

      (M.Misc, M.TyUint _, M.TyUint M.USize) -> fail "Cannot cast to unsized type"
      (M.Misc, M.TyInt _,  M.TyInt  M.USize) -> fail "Cannot cast to unsized type"
      (M.Misc, M.TyUint _, M.TyUint s) -> baseSizeToNatCont s $ extendUnsignedBV e 
      (M.Misc, M.TyInt _,  M.TyInt s)  -> baseSizeToNatCont s $ extendSignedBV e 
      (M.Misc, M.TyCustom (M.BoxTy tb1), M.TyCustom (M.BoxTy tb2)) -> evalCast' ck tb1 e tb2

      (M.Unsize, M.TyRef (M.TyArray tp _sz) M.Immut, M.TyRef (M.TySlice tp') M.Immut)
        | tp == tp' -> return e -- arrays and immutable slices have the same denotation
        | otherwise -> fail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray tp _sz) M.Mut, M.TyRef (M.TySlice tp') M.Immut)
        | tp == tp' -> fail "FIXME! implement mut->immut unsize cast!"
        | otherwise -> fail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray tp sz) M.Mut, M.TyRef (M.TySlice tp') M.Mut)
        | tp == tp', MirExp (MirReferenceRepr (C.VectorRepr elem_tp)) ref <- e
        -> do let start = S.litExpr 0
              let end   = S.litExpr (fromIntegral sz)
              let tup   = S.mkStruct
                              (Ctx.Empty Ctx.:> MirReferenceRepr (C.VectorRepr elem_tp) Ctx.:> C.NatRepr Ctx.:> C.NatRepr)
                              (Ctx.Empty Ctx.:> ref Ctx.:> start Ctx.:> end)
              return $ MirExp (MirSliceRepr elem_tp) tup
        | otherwise -> fail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray _ _) M.Immut, M.TyRef (M.TySlice _) M.Mut) ->
         fail "Cannot cast an immutable array to a mutable slice"

      -- Trait object creation.
      (M.Unsize, M.TyRef baseType _, M.TyRef (M.TyDynamic traitName) _) ->
        mkTraitObject traitName baseType e

      -- C-style adts, casting an enum value to a TyInt
      (M.Misc, M.TyCustom (CEnum _n _i), M.TyInt USize) -> return e
      (M.Misc, M.TyCustom (CEnum _n _i), M.TyInt sz) | (MirExp C.IntegerRepr e0) <- e ->
         baseSizeToNatCont sz $ \nat ->
           -- TODO: what happened to E.IntegerToSBV? Will we lose the sign here?
           return $ MirExp (C.BVRepr nat) (R.App $ E.IntegerToBV nat e0)

      -- C-style adts, casting a TyInt to an enum value
      (M.Misc, M.TyInt USize, M.TyCustom (CEnum _n _i)) -> return e
      (M.Misc, M.TyInt _sz,   M.TyCustom (CEnum _n _i)) | (MirExp (C.BVRepr nat) e0) <- e ->
           return $ MirExp knownRepr (R.App $ E.SbvToInteger nat e0)


      _ -> fail $ "unimplemented cast: " ++ (show ck) ++ " " ++ (show ty1) ++ " as " ++ (show ty2)
 
evalCast :: M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast ck op ty = do
    e <- evalOperand op
    evalCast' ck (M.typeOf op) e ty

-- Some dynamic traits have special implementation as objects

mkCustomTraitObject :: HasCallStack => M.DefId -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s)
mkCustomTraitObject traitName (TyClosure fname args) e@(MirExp baseTyr baseValue)
   | M.did_name traitName == ("Fn", 0) = do
      -- traceM $ "customTraitObj for " ++ show fname ++ " with args " ++ show args
      -- a trait object for a closure is just the closure value
      -- call is a custom operation
      let vtableCtx = undefined
      let assn      = undefined
      let ctxr      = Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.StructRepr vtableCtx
      let _obj      = R.App $ E.PackAny (C.StructRepr ctxr)
                       (R.App $ E.MkStruct ctxr (Ctx.empty Ctx.:> (R.App $ E.PackAny baseTyr baseValue) Ctx.:> assn))
      return e
mkCustomTraitObject traitName baseType _ =
  fail $ Text.unpack $ Text.unwords ["Error while creating a trait object: type ",
                                     Text.pack (show baseType)," does not implement trait ", M.idText traitName]
    

-- | Create a new trait object for the given trait for the given value
-- Fails if the type of the value does not implement the trait.
-- A trait object is pair of the value (first coerced to Any) with
-- a copy of the vtable for that type. To make this work we need to *wrap* the standard vtable
-- for this type so that it accepted "Any" instead
-- This pair is then packed to type AnyType.
mkTraitObject :: HasCallStack => M.DefId -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s)
mkTraitObject traitName baseType e@(MirExp implRepr baseValue) = do
    -- look up the information about the trait
    (Some timpls) <- traitImplsLookup traitName

    -- look up the specific vtable for that type
    case Map.lookup [baseType] (timpls^.vtables) of
      Nothing -> mkCustomTraitObject traitName baseType e
      Just vtbl -> do
        let baseTy    = (timpls^.vtableTyRepr)
        --traceM $ "pre-subst vtable type is  " ++ show baseTy
        let substR    = Ctx.singleton C.AnyRepr 
        let vtableCtx = implementCtxRepr substR baseTy
        --traceM $ "post-subst vtable type is " ++ show vtableCtx
        let ctxr      = Ctx.empty Ctx.:> C.AnyRepr Ctx.:> C.StructRepr vtableCtx
        let assn      = S.mkStruct vtableCtx (vtblToStruct substR vtbl)
        let cbv       = R.App $ E.PackAny implRepr baseValue
        let obj       = R.App $ E.PackAny (C.StructRepr ctxr)
                           (S.mkStruct ctxr (Ctx.empty Ctx.:> cbv Ctx.:> assn))
        return $ MirExp C.AnyRepr obj

      
traitImplsLookup :: HasCallStack => M.DefId -> MirGenerator h s ret (Some (TraitImpls s))
traitImplsLookup traitName = do
  (TraitMap mp) <- use traitMap
  case Map.lookup traitName mp of
    Nothing -> fail $ Text.unpack $ Text.unwords ["Trait does not exist ", M.idText traitName]
    Just timpls -> return timpls
    

-- Expressions: evaluation of Rvalues and Lvalues

evalRefLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalRefLvalue lv =
      case lv of
        M.Local (M.Var nm _ _ _ pos) ->
          do vm <- use varMap
             case Map.lookup nm vm of
               Just (Some (VarReference reg)) ->
                 do r <- G.readReg reg
                    return $ MirExp (R.typeOfReg reg) r
               _ -> fail ("Mutable reference-taken variable not backed by reference! " <> show nm <> " at " <> Text.unpack pos)
        M.LProjection proj -> evalRefProj proj

        _ -> fail ("FIXME! evalRval, Ref for non-local lvars" ++ show lv)

getVariant :: HasCallStack => M.Ty -> MirGenerator h s ret (M.Variant, Substs)
getVariant (M.TyAdt nm args) = do
    am <- use collection
    case Map.lookup nm (am^.adts) of
       Nothing -> fail ("Unknown ADT: " ++ show nm)
       Just (M.Adt _ [struct_variant]) -> return (struct_variant, args)
       _      -> fail ("Expected ADT with exactly one variant: " ++ show nm)
getVariant (M.TyDowncast (M.TyAdt nm args) ii) = do
    let i = fromInteger ii
    am <- use collection
    case Map.lookup nm (am^.adts) of
       Nothing -> fail ("Unknown ADT: " ++ show nm)
       Just (M.Adt _ vars) | i < length vars -> return $ (vars !! i, args)
       _      -> fail ("Expected ADT with more than " ++ show i ++ " variants: " ++ show nm)
getVariant ty = fail $ "Variant type expected, received " ++ show (pretty ty) ++ " instead"

evalRefProj :: HasCallStack => M.LvalueProjection -> MirGenerator h s ret (MirExp s)
evalRefProj (M.LvalueProjection base projElem) =
  do MirExp tp ref <- evalRefLvalue base 
     -- traceM $ "evalRefProj:" ++ show (pretty base) ++ " of type " ++ show tp 
     case tp of
       MirReferenceRepr elty ->
         case projElem of
          M.Deref -> return (MirExp tp ref)

          M.PField idx _mirTy
            | C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr) <- elty
            -> do
             (struct_variant, args) <- getVariant (M.typeOf base)
             Some ctx <- return $ variantToRepr struct_variant args
             case Ctx.intIndex idx (Ctx.size ctx) of
                     Nothing -> fail ("Invalid index: " ++ show idx)
                     Just (Some idx') -> 
                        do r' <- subfieldRef ctx ref idx'
                           return (MirExp (MirReferenceRepr (ctx Ctx.! idx')) r')

          M.ConstantIndex offset _min_len fromend
            | C.VectorRepr tp' <- elty
            , fromend == False ->
                do let natIdx = S.litExpr (fromIntegral offset)
                   r' <- subindexRef tp' ref natIdx
                   return (MirExp (MirReferenceRepr tp') r')

            | C.VectorRepr _tp' <- elty
            , fromend == True ->
                fail ("FIXME: implement constant fromend indexing in reference projection")

          M.Index var
            | C.VectorRepr tp' <- elty
            -> do MirExp idxTy idx <- lookupVar var
                  case idxTy of
                    C.NatRepr ->
                      do r' <- subindexRef tp' ref idx
                         return (MirExp (MirReferenceRepr tp') r')
                    C.BVRepr w ->
                      do idxNat <- G.forceEvaluation (S.app (E.BvToNat w idx))
                         r' <- subindexRef tp' ref idxNat
                         return (MirExp (MirReferenceRepr tp') r')

                    _ -> fail ("Expected index value to be an integer value in reference projection " ++
                                show base ++ " " ++ show projElem ++ " " ++ show idxTy)
          _ -> fail ("Unexpected interior reference " ++ show base ++ " " ++ show projElem)
       _ -> fail ("Expected reference value in lvalue projection: " ++ show tp ++ " " ++ show base)


evalRval :: HasCallStack => M.Rvalue -> MirGenerator h s ret (MirExp s)
evalRval (M.Use op) = evalOperand op
evalRval (M.Repeat op size) = buildRepeat op size
evalRval (M.Ref bk lv _) =
  case bk of
    M.Shared  -> evalLvalue lv
    M.Mutable -> evalRefLvalue lv
    M.Unique  -> fail "FIXME! Unique reference not implemented"

evalRval (M.Len lv) =
  case lv of
    M.LProjection (M.LvalueProjection lv' M.Deref)
      | M.TyRef (M.TySlice _) M.Mut <- M.typeOf lv'
      -> do MirExp t e <- evalLvalue lv'
            case t of
              MirSliceRepr _tp' ->
                do let end = S.getStruct (Ctx.natIndex @2) e
                   return $ MirExp C.NatRepr end
              _ -> fail "Expected mutable slice value"
    _ ->
      do MirExp t e <- evalLvalue lv
         case t of
           C.VectorRepr _ -> return $ MirExp C.NatRepr $ S.vectorSize e -- might need to convert nat to bv later
           _ -> fail "len expects vector input"

evalRval (M.Cast ck op ty) = evalCast ck op ty
evalRval (M.BinaryOp binop op1 op2) = transBinOp binop op1 op2
evalRval (M.CheckedBinaryOp binop op1 op2) = transCheckedBinOp  binop op1 op2
evalRval (M.NullaryOp nop nty) = transNullaryOp  nop nty
evalRval (M.UnaryOp uop op) = transUnaryOp  uop op
evalRval (M.Discriminant lv) = do
    e <- evalLvalue lv
    let ty = typeOf lv 
    case ty of
      TyCustom (CEnum _adt _i) -> return e
      _ -> do (MirExp C.NatRepr idx) <- accessAggregate e 0
              return $ (MirExp knownRepr $ R.App (E.NatToInteger idx))

evalRval (M.RCustom custom) = transCustomAgg custom
evalRval (M.Aggregate ak ops) = case ak of
                                   M.AKTuple ->  do
                                       exps <- mapM evalOperand ops
                                       return $ buildTuple exps
                                   M.AKArray ty -> do
                                       exps <- mapM evalOperand ops
                                       tyToReprCont ty $ \repr ->
                                           buildArrayLit repr exps
                                   M.AKClosure defid argsm -> do
                                       args <- mapM evalOperand ops
                                       buildClosureHandle defid argsm args
evalRval rv@(M.RAdtAg (M.AdtAg adt agv ops ty)) = do
    case ty of
      -- cstyle
      TyCustom (CEnum _ vs) -> do
         let j = vs !! fromInteger agv
         return $ (MirExp knownRepr (R.App (E.IntLit j)))
      _ -> do
       es <- mapM evalOperand ops
       return $ buildTaggedUnion agv es




-- A closure is (packed into an any) of the form [handle, arguments]
-- (arguments being those variables packed into the closure, not the function arguments)
-- NOTE: what if the closure has a polymorphic types?? How can we tell?
buildClosureHandle :: M.DefId      -- ^ name of the function
                    -> Substs      -- ^ types of the closed over variables 
                    -> [MirExp s]  -- ^ values of the closed over variables
                    -> MirGenerator h s ret (MirExp s)
buildClosureHandle funid (Substs tys) args
  = tyListToCtx tys $ \ subst -> do
      hmap <- use handleMap
      case (Map.lookup funid hmap) of
        Just (MirHandle _ _sig fhandle)
          | Just C.Dict <- C.checkClosedCtx (FH.handleArgTypes fhandle)
          , Just C.Dict <- C.checkClosed (FH.handleReturnType fhandle)
            -> do
              let closure_arg = buildTuple args
                  inst_ty = FH.handleType fhandle
                  handle_cl = R.App $ E.HandleLit fhandle
                  handl = MirExp inst_ty handle_cl
              let closure_unpack = buildTuple [handl, (packAny closure_arg)]
              return $ packAny closure_unpack
        _ ->
          do fail ("buildClosureHandle: unknown function: "
              ++ show funid ++ " or non-closed type ")

buildClosureType :: M.DefId -> Substs -> MirGenerator h s ret (Some C.TypeRepr, Some C.TypeRepr) -- get type of closure, in order to unpack the any
buildClosureType defid (Substs args') = do
    hmap <- use handleMap
    case (Map.lookup defid hmap) of
      Just (MirHandle _ _sig fhandle) -> do
          let args = tail (tail args')
          -- traceM $ "buildClosureType for " ++ show defid ++ " with ty args " ++ show (pretty args)
          -- build type StructRepr [HandleRepr, StructRepr [args types]]
          tyListToCtx args $ \argsctx -> do
              let argstruct = C.StructRepr argsctx
                  handlerepr = FH.handleType fhandle
              reprsToCtx [Some handlerepr, Some C.AnyRepr] $ \t ->
                  return $ (Some (C.StructRepr t), Some argstruct)
      _ ->
       do fail ("buildClosureType: unknown function: " ++ show defid)


unpackAny :: HasCallStack => Some C.TypeRepr -> MirExp s -> MirGenerator h s ret (MirExp s)
unpackAny (Some tr) e@(MirExp C.AnyRepr _) = return $ unpackAnyE tr e
unpackAny _ (MirExp tr _) = fail $ "bad anytype, found " ++ show (pretty tr) 


unpackAnyE :: HasCallStack => C.TypeRepr t -> MirExp s -> MirExp s
unpackAnyE tr (MirExp C.AnyRepr e) =
   MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) (fromString ("Bad Any unpack: " ++ show tr)))
unpackAnyE _ _ = error $ "bad anytype unpack"


packAny ::  MirExp s -> (MirExp s)
packAny (MirExp e_ty e) = MirExp C.AnyRepr (S.app $ E.PackAny e_ty e)

filterMaybes :: [Maybe a] -> [a]
filterMaybes [] = []
filterMaybes ((Just a):as) = a : (filterMaybes as)
filterMaybes ((Nothing):as) = filterMaybes as

evalLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalLvalue (M.Tagged l _) = evalLvalue l
evalLvalue (M.Local var) = lookupVar var
evalLvalue (M.LProjection (M.LvalueProjection lv (M.PField field _ty))) = do
    db <- use debugLevel
    case M.typeOf lv of

      -- TODO: unify first two cases
      mty@(M.TyAdt did _) -> do
         (struct_variant, args) <- getVariant mty
         etu <- evalLvalue lv
         e   <- accessAggregate etu 1
         Some ctx <- return $ variantToRepr struct_variant args
         struct <- unpackAny (Some (C.StructRepr ctx)) e
         accessAggregate struct field

      mty@(M.TyDowncast _ _) -> do
         (struct_variant, args) <- getVariant mty
         etu <- evalLvalue lv
         e   <- accessAggregate etu 1
         Some ctx <- return $ variantToRepr struct_variant args
         struct <- unpackAny (Some (C.StructRepr ctx)) e
         accessAggregate struct field


      M.TyClosure defid args -> do
        -- if lv is a closure, then accessing the ith component means accessing the ith arg in the struct
        e <- evalLvalue lv
        (clty, rty) <- buildClosureType defid args
        unpack_closure <- unpackAny clty e
        clargs <- accessAggregate unpack_closure 1
        clargs' <- unpackAny rty clargs
        accessAggregate clargs' field


      _ -> do -- otherwise, lv is a tuple
        ag <- evalLvalue lv
        accessAggregateMaybe ag field
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Index i))) = do
    (MirExp arr_tp arr) <- evalLvalue lv
    (MirExp ind_tp ind) <- lookupVar i
    case (arr_tp, ind_tp) of
      (C.VectorRepr elt_tp, C.NatRepr) -> do
          G.assertExpr (ind S..< (S.app (E.VectorSize arr)))
                       (S.litExpr "Index out of range")
          return $ MirExp elt_tp $ S.app $ E.VectorGetEntry elt_tp arr ind
      (MirSliceRepr elt_tp, C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr)) ->
           let mir_ty = M.typeOf i in
           case mir_ty of
             M.TyAdt did (Substs [TyUint USize]) 
               | did == M.textId "::ops[0]::range[0]::RangeFrom[0]" -> do
                  -- get the start of the range
                  let astart = (S.getStruct Ctx.i2of2 ind)
                  let indty  = C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr)
                  let start = S.getStruct Ctx.baseIndex
                                (S.app $ E.FromJustValue indty (S.app $ E.UnpackAny indty astart) (fromString ("Bad Any unpack Nat")))
                  -- create a new slice by modifying the indices of the current one
                  let newSlice = updateSliceLB elt_tp arr start
                  return (MirExp arr_tp newSlice)
               | did == M.textId "::ops[0]::range[0]::Range[0]" -> do
                  -- get the start of the range
                  let astart = (S.getStruct Ctx.i2of2 ind)
                  let indty  = C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr Ctx.:> C.NatRepr)
                  let start = S.getStruct Ctx.i1of2
                                (S.app $ E.FromJustValue indty (S.app $ E.UnpackAny indty astart) (fromString ("Bad Any unpack Nat")))
                  -- create a new slice by modifying the indices of the current one
                  let newSlice = updateSliceLB elt_tp arr start
                  return (MirExp arr_tp newSlice)
   

             _ -> 
               fail $ "Unknown slice projection type:" ++ show mir_ty
      _ -> fail $ "Bad index, arr_typ is:" ++ show arr_tp ++ "\nind_type is: " ++ show ind_tp

evalLvalue (M.LProjection (M.LvalueProjection lv M.Deref)) =
   case M.typeOf lv of
     M.TyRef _ M.Immut ->
         do evalLvalue lv
     M.TyRef _ M.Mut ->
         do MirExp ref_ty ref <- evalLvalue lv
            case ref_ty of
              MirReferenceRepr tp ->
                 do r <- readMirRef tp ref
                    return $ MirExp tp r
              MirSliceRepr tp ->
                 do let vr = S.getStruct Ctx.i1of3 ref
                    v <- readMirRef (C.VectorRepr tp) vr
                    -- TODO: trim this vector relative to the slice....
                    return $ MirExp (C.VectorRepr tp) v
--                    error $ unwords ["Found slice for " , show $ pretty tp]
              _ -> error $ unwords ["Expected reference value in mutable dereference", show $ pretty lv]
     tp ->
       fail $ unwords ["Expected reference type in dereference", show tp, show lv]

-- downcast: extracting the injection from an ADT. This is done in rust after switching on the discriminant.
-- We don't really do anything here --- all the action is when we project from the downcasted adt
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Downcast _i))) = do
    evalLvalue lv
evalLvalue lv = fail $ "unknown lvalue access: " ++ (show lv)




--------------------------------------------------------------------------------------
-- ** Statements
--

-- v := rvalue
--
assignVarRvalue :: M.Var -> M.Rvalue -> MirGenerator h s ret ()
assignVarRvalue var rv = assignVarExp var =<< evalRval rv

-- v := mirexp
assignVarExp :: HasCallStack => M.Var -> MirExp s -> MirGenerator h s ret ()

-- Implement implict coercion from mutable reference to immutable reference.  The major
-- invariant guarantee given by the borrow checker is that, so long as the immutable
-- reference is live, the value will not change.  This justifies immediately deferencing
-- the pointer to get out the value within.
assignVarExp v@(M.Var _vnamd _ (M.TyRef _lhs_ty M.Immut) _ _pos)
               (MirExp (MirReferenceRepr e_ty) e) =
         do r <- readMirRef e_ty e
            assignVarExp v (MirExp e_ty r)

-- For mutable slice to immutable slice, we make a copy of the vector so that
-- we have the correct range. Note: if we update immutable slices to also
-- store bounds, then we can update this coercion.
assignVarExp v@(M.Var _vnamd _ (M.TyRef (M.TySlice _lhs_ty) M.Immut) _ _pos)
               (MirExp (MirSliceRepr e_ty) e) =
 
         do let rvec  = S.getStruct Ctx.i1of3 e
            let start = S.getStruct Ctx.i2of3 e
            let stop  = S.getStruct Ctx.i3of3 e
            r <- readMirRef (C.VectorRepr e_ty) rvec
            r2 <- vectorCopy e_ty start stop r
            assignVarExp v (MirExp (C.VectorRepr e_ty) r2)


assignVarExp (M.Var vname _ vty _ pos) (MirExp e_ty e) = do
    vm <- use varMap
    case (Map.lookup vname vm) of
      Just (Some varinfo)
        | Just C.Refl <- testEquality e_ty (varInfoRepr varinfo) ->
            case varinfo of
              VarRegister reg ->
                do G.assignReg reg e
              VarReference reg ->
                do r <- G.readReg reg
                   writeMirRef r e
              VarAtom _ ->
                do fail ("Cannot assign to atom: " <> show vname <> " of type " <> show (pretty vty) <> " at " <> Text.unpack pos)
        | otherwise ->
            fail $ "type error in assignment: got " ++ (show (pretty e_ty)) ++ " but expected "
                     ++ (show (varInfoRepr varinfo)) ++ " in assignment of " ++ (show vname) ++ " which has type "
                     ++ (show vty) ++ " at " ++ (Text.unpack pos)
      Nothing -> fail ("register not found: " ++ show vname ++ " at " ++ Text.unpack pos)

-- lv := mirexp
assignLvExp :: HasCallStack => M.Lvalue -> MirExp s -> MirGenerator h s ret ()
assignLvExp lv re = do
    case lv of
        M.Tagged lv _ -> assignLvExp  lv re
        M.Local var   -> assignVarExp var re
        M.Static -> fail "static"
        M.LProjection (M.LvalueProjection lv (M.PField field _ty)) -> do

            am <- use collection
            case M.typeOf lv of
              M.TyAdt nm args ->
                case Map.lookup nm (am^.adts) of
                  Nothing -> fail ("Unknown ADT: " ++ show nm)
                  Just (M.Adt _ [struct_variant]) ->
                    do etu <- evalLvalue lv
                       e   <- accessAggregate etu 1 -- get the ANY data payload
                       Some ctx <- return $ variantToRepr struct_variant args
                       struct <- unpackAny (Some (C.StructRepr ctx)) e
                       struct' <- modifyAggregateIdx struct re field
                       etu' <- modifyAggregateIdx etu (packAny struct') 1
                       assignLvExp lv etu'
                  Just _ -> fail ("Expected ADT with exactly one variant: " ++ show nm)

              M.TyDowncast (M.TyAdt nm args) i -> 
                case Map.lookup nm (am^.adts) of
                  Nothing -> fail ("Unknown ADT: " ++ show nm)
                  Just (M.Adt _ vars) -> do
                     let struct_variant = vars List.!! (fromInteger i)
                     Some ctx <- return $ variantToRepr struct_variant args

                     etu <- evalLvalue lv
                     e   <- accessAggregate etu 1

                     struct <- unpackAny (Some (C.StructRepr ctx)) e
                     struct' <- modifyAggregateIdx struct re field

                     etu' <- modifyAggregateIdx etu (packAny struct') 1
                     assignLvExp lv etu'

              M.TyClosure defid args -> do
                (Some top_ty, Some clos_ty) <- buildClosureType defid args
                clos      <- evalLvalue lv
                etu       <- unpackAny (Some top_ty) clos
                clos_str  <- accessAggregate etu 1
                cstr      <- unpackAny (Some clos_ty) clos_str
                new_ag    <- modifyAggregateIdx cstr re field
                let clos_str' = packAny new_ag
                etu'      <- modifyAggregateIdx etu clos_str' 1
                let clos' = packAny etu'
                assignLvExp lv clos'

              _ -> do
                ag <- evalLvalue lv
                new_ag <- modifyAggregateIdxMaybe ag re field
                assignLvExp lv new_ag
        M.LProjection (M.LvalueProjection lv (M.Downcast i)) -> do
          assignLvExp lv re

        M.LProjection (M.LvalueProjection (M.LProjection (M.LvalueProjection lv' M.Deref)) (M.Index v))
          | M.TyRef (M.TySlice _) M.Mut <- M.typeOf lv' ->
            do MirExp slice_tp slice <- evalLvalue lv'

               MirExp ind_tp ind     <- lookupVar v
               MirExp r_tp r         <- return re
               case (slice_tp, ind_tp) of
                 (MirSliceRepr el_tp, C.NatRepr)
                   | Just Refl <- testEquality r_tp el_tp
                   -> do let _ctx   = Ctx.Empty Ctx.:> MirReferenceRepr (C.VectorRepr el_tp) Ctx.:> C.NatRepr Ctx.:> C.NatRepr
                         let ref   = S.getStruct (Ctx.natIndex @0) slice
                         let start = S.getStruct (Ctx.natIndex @1) slice
                         let len   = S.getStruct (Ctx.natIndex @2) slice
                         G.assertExpr (ind S..< len) (S.litExpr "Index out of range")
                         let ind'  = start S..+ ind
                         arr <- readMirRef (C.VectorRepr el_tp) ref
                         let arr' = S.app $ E.VectorSetEntry el_tp arr ind' r
                         writeMirRef ref arr'

                 _ -> fail $ "bad type in slice assignment"

        M.LProjection (M.LvalueProjection lv (M.Index v)) -> do
            (MirExp arr_tp arr) <- evalLvalue lv
            (MirExp ind_tp ind) <- lookupVar v
            case re of
              MirExp r_tp r ->
                case (arr_tp, ind_tp) of
                  (C.VectorRepr x, C.NatRepr) ->
                      case (testEquality x r_tp) of
                        Just Refl -> do
                          G.assertExpr (ind S..< (S.app (E.VectorSize arr)))
                                       (S.litExpr "Index out of range")
                          let arr' = MirExp arr_tp (S.app $ E.VectorSetEntry r_tp arr ind r)
                          assignLvExp lv arr'
                        Nothing -> fail "bad type in assign"
                  _ -> fail $ "bad type in assign"
        M.LProjection (M.LvalueProjection lv M.Deref) ->
            do MirExp ref_tp ref <- evalLvalue lv
               case (ref_tp, re) of
                 (MirReferenceRepr tp, MirExp tp' e)
                   | Just C.Refl <- testEquality tp tp' -> writeMirRef ref e
                 _ -> fail $ unwords ["Type mismatch when assigning through a reference", show lv, ":=", show re]            
        _ -> fail $ "rest assign unimp: " ++ (show lv) ++ ", " ++ (show re)

-- "Allocate" space for the variable by constructing an initial value for it (if possible)
-- This code will 
storageLive :: M.Var -> MirGenerator h s ret ()
storageLive (M.Var nm _ ty _ _) = 
  do vm <- use varMap
     db <- use debugLevel
     case Map.lookup nm vm of
       Just (Some varinfo@(VarRegister reg)) -> do
         mv <- initialValue ty
         case mv of
           Nothing -> do
             when (db > 6) $
                traceM $ "storageLive: cannot initialize storage for " ++ show nm ++ " of type " ++ show (pretty ty)
             return ()
           Just (MirExp rty e) ->
              case testEquality rty (varInfoRepr varinfo) of
                 Just Refl -> do
                   G.assignReg reg e
                 Nothing -> fail $ "Types don't match in storageLive. Created value of type: " ++ show rty ++ " for var of type: " ++ show (varInfoRepr varinfo)
             
       Just (Some varinfo@(VarReference reg)) -> do
         r  <- newMirRef (varInfoRepr varinfo)
         mv <- initialValue ty
         case mv of
           Nothing -> do
              when (db > 6) $
                traceM $ "storageLive: cannot initialize storage for " ++ show nm ++ " of type " ++ show (pretty ty)
              return ()
           Just (MirExp rty e) -> 
              case testEquality rty (varInfoRepr varinfo) of
                 Just Refl -> do
                   writeMirRef r e
                   G.assignReg reg r
                 Nothing -> error "types don't match in storageLive. This is probably a bug"
       _ -> return ()


storageDead :: M.Var -> MirGenerator h s ret ()
storageDead (M.Var nm _ _ _ _) =
  do vm <- use varMap
     case Map.lookup nm vm of
       Just (Some _varinfo@(VarReference reg)) ->
         do dropMirRef =<< G.readReg reg
       _ -> return ()


transStatement :: HasCallStack => M.Statement -> MirGenerator h s ret ()
transStatement (M.Assign lv rv pos) = do
  setPosition pos
  re <- evalRval rv
  assignLvExp lv re
transStatement (M.StorageLive lv) =
  do storageLive lv
transStatement (M.StorageDead lv) =
  do storageDead lv
transStatement (M.SetDiscriminant lv i) = do
  ev@(MirExp ty e) <- evalLvalue lv
  case ty of
    C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr) -> do
       e' <- modifyAggregateIdx ev (MirExp C.NatRepr (S.litExpr (fromInteger (toInteger i)))) 0
       assignLvExp lv e'
    C.AnyRepr ->
       fail "set discriminant: found any"
    C.IntegerRepr ->
       fail "set discriminant: this case should have been translated away by Pass/AllocEnum"
{-      case (M.typeOf lv) of
       M.TyCustom (M.CEnum adt vs) -> do
          -- TODO: this is dead code, remove
          -- this is a C-style enum
          let ty = TyInt USize
          let j = vs !! i  -- TODO: better error message if this fails (would be a bug in the translator)
          traceM $ "j is " ++ show j
          let idx = (Value (ConstInt (Isize (toInteger j))))
          transStatement (M.Assign lv (Use (OpConstant (Constant ty idx))) "internal: set-discr")
       _ -> fail "set discriminant: should find CEnum here" -}
    _ -> fail $ "set discriminant: cannot handle type " ++ show ty
transStatement M.Nop = return ()

ifteAny :: R.Expr MIR s C.BoolType
        -> (forall a. MirGenerator h s ret a) -- ^ true branch
        -> (forall a. MirGenerator h s ret a) -- ^ false branch
        -> MirGenerator h s ret a
ifteAny e x y = do
  x_id <- G.defineBlockLabel x
  y_id <- G.defineBlockLabel y
  G.branch e x_id y_id

transSwitch :: MirExp s -> -- thing switching over
    [Integer] -> -- switch comparisons
        [M.BasicBlockInfo] -> -- jumps
                MirGenerator h s ret a
transSwitch _ [] [targ] = jumpToBlock targ
transSwitch (MirExp (C.BoolRepr) e) [v] [t1,t2] =
    if v == 1 then
              doBoolBranch e t1 t2
    else
              doBoolBranch e t2 t1
transSwitch (MirExp (C.IntegerRepr) e) vs ts =
    doIntBranch e vs ts

transSwitch (MirExp f _e) _ _  = error $ "bad switch: " ++ show f

doBoolBranch :: R.Expr MIR s C.BoolType -> M.BasicBlockInfo -> M.BasicBlockInfo -> MirGenerator h s ret a
doBoolBranch e t f = do
    lm <- use labelMap
    case (Map.lookup t lm, Map.lookup f lm) of
      (Just tb, Just fb) -> G.branch e tb fb
      _ -> error "bad lookup on boolbranch"

-- nat branch: branch by iterating through list
doIntBranch :: R.Expr MIR s C.IntegerType -> [Integer] -> [M.BasicBlockInfo] -> MirGenerator h s ret a
doIntBranch _ _ [i] = do
    lm <- use labelMap
    case (Map.lookup i lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"
doIntBranch e (v:vs) (i:is) = do
    let test = S.app $ E.IntEq e $ S.app $ E.IntLit v
    ifteAny test (jumpToBlock i) (doIntBranch e vs is)
doIntBranch _ _ _ =
    fail "doIntBranch: improper switch!"

jumpToBlock :: M.BasicBlockInfo -> MirGenerator h s ret a
jumpToBlock bbi = do
    lm <- use labelMap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"

{-
jumpToBlock' :: M.BasicBlockInfo -> MirGenerator h s ret a
jumpToBlock' bbi = do
    lm <- use labelMap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"
-}

doReturn :: HasCallStack => C.TypeRepr ret -> MirGenerator h s ret a
doReturn tr = do
    e <- lookupRetVar tr
    G.returnFromFunction e

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- | Find the function expression for this name (instantiated with the given type arguments) 
-- It could be a regular function, a static trait invocation, or a dictionary argument
-- 
-- Will return an expression of type (FnHandleType args ret) or (PolyFnType k args ret)
-- Also returns any predicates that must be satisfied at this call
-- 
-- Some of these predicates will turn into additional (term) arguments, but only the call
-- site knows which
lookupFunction :: forall h s ret. HasCallStack => MethName -> Substs
   -> MirGenerator h s ret (Maybe (MirExp s, [Predicate]))
lookupFunction nm (Substs funsubst)
  | Some k <- peanoLength funsubst = do
  db   <- use debugLevel
  when (db > 3) $
    traceM $ "**lookupFunction: trying to resolve " ++ fmt nm ++ fmt (Substs funsubst)

  hmap <- use handleMap
  _tm   <- use traitMap
  stm  <- use staticTraitMap
  vm   <- use varMap
  am   <- use collection

  isStatic <- resolveStaticTrait' nm (Substs funsubst)

  -- Given a (polymorphic) function handle, turn it into an expression by
  -- instantiating the type arguments
  let mkFunExp :: Substs -> [Param] -> FH.FnHandle a r -> MirExp s
{-      mkFunExp (Substs [])     fhandle =
        case (C.checkClosedCtx (FH.handleArgTypes fhandle),
              C.checkClosed (FH.handleReturnType fhandle)) of
          (Just C.Dict, Just C.Dict) -> 
            MirExp (FH.handleType fhandle) (R.App $ E.HandleLit fhandle)
          (_,_) ->
            error $ "Handle not closed"  -}
      mkFunExp (Substs hsubst) params fhandle
        | Some fk <- peanoLength params = tyListToCtx (reverse hsubst) $ \tyargs ->
       
        let fargctx  = FH.handleArgTypes fhandle
            fret     = FH.handleReturnType fhandle
            ifargctx = C.instantiate (C.mkSubst tyargs) fargctx
            ifret    = C.instantiate (C.mkSubst tyargs) fret
        in
        case testEquality fk (ctxSizeP tyargs) of
          Nothing   -> case ltP (ctxSizeP tyargs) fk of
             TrueRepr  ->
               let
                  fty      = C.PolyFnRepr fk fargctx fret
                  polyfcn  = R.App $ E.PolyHandleLit fk fhandle
                  polyspec = R.App $ E.PolySpecialize fty polyfcn tyargs
                  cty      = C.PolyFnRepr (fk `minusP` (ctxSizeP tyargs)) ifargctx ifret
               in
                  MirExp cty polyspec
             FalseRepr -> error "BUG: invalid number of type args"
          Just Refl ->
            let --fargctx  = FH.handleArgTypes fhandle
                --fret     = FH.handleReturnType fhandle
                --ifargctx = C.instantiate (C.mkSubst tyargs) fargctx
                --ifret    = C.instantiate (C.mkSubst tyargs) fret
                polyfcn  = R.App $ E.PolyHandleLit fk fhandle
                polyinst = R.App $ E.PolyInstantiate (C.PolyFnRepr fk fargctx fret) polyfcn tyargs
            in
              MirExp (C.FunctionHandleRepr ifargctx ifret) polyinst

  -- Given a (polymorphic) trait method, instantiate it with the method's type arguments
  let instantiateTraitMethod :: MirExp s -> Substs -> MirExp s
      instantiateTraitMethod exp@(MirExp (C.FunctionHandleRepr _ _) _) (Substs []) = exp
      instantiateTraitMethod (MirExp fty@(C.PolyFnRepr n fargctx fret) polyfcn) (Substs methsubst) = do
        tyListToCtx (reverse methsubst) $ \tyargs -> do
           let ifargctx = C.instantiate (C.mkSubst tyargs) fargctx
           let ifret    = C.instantiate (C.mkSubst tyargs) fret
           case testEquality (ctxSizeP tyargs) n of
                   Just Refl -> 
                     let polyinst = R.App $ E.PolyInstantiate fty polyfcn tyargs
                         cty      = C.FunctionHandleRepr ifargctx ifret
                     in (MirExp cty polyinst)
                   Nothing ->
                     case ltP (ctxSizeP tyargs) n of
                       TrueRepr -> 
                         let polyinst = R.App $ E.PolySpecialize fty polyfcn tyargs
                             cty      = C.PolyFnRepr (n `minusP` (ctxSizeP tyargs)) ifargctx ifret 
                         in (MirExp cty polyinst)
                         
                       FalseRepr -> 
                         error $ "TODO: " ++ show (ctxSizeP tyargs) ++ " > " ++ show n
      instantiateTraitMethod (MirExp ty _) ss =
         error $ "instantiateTraitMethod: found exp of type " ++ show ty
                         ++ "\n and substs " ++ fmt ss

  case () of 
       -- a normal function, resolve associated types to additional type arguments
    () | Just (MirHandle nm fs fh) <- Map.lookup nm hmap
       -> do
            let preds = fs^.fspredicates
            let gens = fs^.fsgenerics
            let hsubst = Substs $ funsubst

            when (db > 3) $ do
              traceM $ "***lookupFunction: In normal call of " ++ show (pretty nm)
              traceM $ "\tpreds are " ++ fmt preds
              traceM $ "\tgens are " ++ fmt gens
              traceM $ "\thsubst is " ++ fmt hsubst
            return $ Just $ (mkFunExp hsubst gens fh, tySubst hsubst preds)

       -- a custom function (we will find it elsewhere)
       | True <- memberCustomFunc nm (Substs funsubst)
       -> return Nothing

       -- a static invocation of a trait, the type argument (from funsubst) is a concrete type
       -- so we can just look up the method in the static method table

       | Just (MirHandle name sig handle, Substs methsubst) <- isStatic
       -> do

             let exp  = mkFunExp (Substs methsubst) (sig^.fsgenerics) handle
             let ssig = specialize sig methsubst

             when (db > 3) $ do
               traceM $ "***lookupFunction: In static trait call of " ++ fmt nm ++ fmt (Substs funsubst)
               traceM $ "\tfound handle    " ++ fmt name
               traceM $ "\tmirHandle ty is " ++ fmt sig
               traceM $ "\tfunsubst is     " ++ fmt funsubst
               traceM $ "\tmethsubst is    " ++ fmt methsubst
               traceM $ "\tspec ty is      " ++ fmt ssig

             return $ Just (exp, ssig^.fspredicates)
               

{-
       | Just (MirExp fty polyfcn, polysig, Substs methsubst) <- isStatic
         -> tyListToCtx (reverse methsubst) $ \tyargs -> do

           when (db > 3) $ do
             traceM $ "***lookupFunction: In static trait call of " ++ fmt nm ++ fmt (Substs funsubst)
             traceM $ "\tpolysig is   " ++ fmt polysig
             traceM $ "\tmethsubst is " ++ fmt methsubst
             traceM $ "\tfty is       " ++ fmt fty
       
           case fty of
              (C.FunctionHandleRepr fargctx fret) ->
                case testEquality (ctxSizeP tyargs) zeroP of
                   Just Refl -> do

                     return $ Just (MirExp (C.FunctionHandleRepr fargctx fret) polyfcn,
                              tySubst (Substs methsubst) (polysig^.fspredicates))
                   Nothing ->
                     error $ "BUG: too many type arguments for non-polymorphic function"
              (C.PolyFnRepr n fargctx fret) -> do
                case testEquality (ctxSizeP tyargs) n of
                   Just Refl -> do
                     let 
                         ifargctx = C.instantiate (C.mkSubst tyargs) fargctx
                         ifret    = C.instantiate (C.mkSubst tyargs) fret
                         polyinst = R.App $ E.PolyInstantiate fty polyfcn tyargs

                     return $ Just (MirExp (C.FunctionHandleRepr ifargctx ifret) polyinst,
                              tySubst (Substs methsubst) (polysig^.fspredicates))
                   Nothing ->
                     case ltP (ctxSizeP tyargs) n of
                       TrueRepr -> do
                         let
                             ifargctx = C.instantiate (C.mkSubst tyargs) fargctx
                             ifret    = C.instantiate (C.mkSubst tyargs) fret
                             polyinst = R.App $ E.PolySpecialize fty polyfcn tyargs

                         return $ Just (MirExp (C.PolyFnRepr (n `minusP` (ctxSizeP tyargs)) ifargctx ifret) polyinst,
                                  tySubst (Substs methsubst) (polysig^.fspredicates))
                         
                       FalseRepr -> 
                         error $ "TODO: " ++ show (ctxSizeP tyargs) ++ " > " ++ show n
              _ -> fail $ "Found non-function " ++ show nm ++ " for type "
                          ++ show (pretty funsubst) ++ " in the trait map: " ++ show fty

-}
       -- a dictionary projection for a trait call
       -- TODO: we don't use type args for resolution, we just access the first dictionary
       -- that we find. This is wrong.

       -- In the guard for this branch:
       -- 1. find the <potential_traits> that could potentially contain this method 
       -- 2. find the trait name <tn> and <fields> of a dictionary type for all potential_traits
       -- 3. find the index <idx> of the method in the dictionary
       -- 4. make sure that we have a dictionary variable in scope
       -- 5. pick the first one (wrong!)

       -- In the branch:
       -- 6.  look up the <trait> in the collection
       -- 7.  pull out its <preds>
       -- 10. create the <var> for the dictionary and the <exp> that projects the appropriate field <fld>
       -- 11. evaluate the var and return the result
       | Just potential_traits <- Map.lookup nm stm

       , ((tn, idx, fields):_) <- [ (tn, idx, fields)
          | (tn, Just (M.Adt _ [Variant _ _ fields _])) <-
                   map (\tn -> (tn,Map.lookup tn (am^.adts))) potential_traits 
          , idx <- Maybe.maybeToList (List.findIndex (\(Field fn _ _) -> nm == fn) fields)
          , Map.member (M.idText tn) vm ]
       -> do 
             let Just trait = Map.lookup tn (am^.traits)
             let (tsubst,msubst) = splitAt (length (trait^.traitParams)) funsubst
             let Just (TraitMethod _ sig) =
                    List.find (\tm -> tm^.itemName == nm) (trait^.traitItems)
             let preds = sig^.fspredicates
             let var = mkPredVar (TyAdt tn (Substs tsubst))
             let fld@(Field _ ty _) = fields !! idx
             let ty'  = tySubst (Substs tsubst) ty
             let exp = M.Use (M.Copy (M.LProjection (M.LvalueProjection (M.Local var) (M.PField idx ty'))))
             let rty = typeOf exp
             when (db > 5) $ do
               traceM $ "***lookupFunction: at dictionary projection for " ++ show (pretty nm)
               traceM $ "   traitParams are" ++ fmt (trait^.traitParams)
               traceM $ "   traitPreds are " ++ fmt (trait^.traitPredicates)
               traceM $ "   var is         " ++ show var
               traceM $ "   tsubst is      " ++ fmt tsubst
               traceM $ "   msubst is      " ++ fmt msubst
               traceM $ "   method sig is  " ++ fmt sig
               traceM $ "   field is       " ++ fmt fld
               traceM $ "   ty is          " ++ fmt ty
               traceM $ "   ty' is          " ++ fmt ty'
               traceM $ "   rty is         " ++ fmt rty
               traceM $ "   exp is         " ++ fmt exp
          
             fun <- evalRval exp
             let fun' = instantiateTraitMethod fun (Substs msubst)
             return $ (Just (fun', tySubst (Substs funsubst) preds))



       | otherwise -> do
            when (db > 1) $ do
               traceM $ "***lookupFunction: Cannot find function " ++ show nm ++ " with type args " ++ show (pretty funsubst)
               case Map.lookup nm stm of
                  Just traits -> do
                     traceM $ "Potential traits: " ++ show traits
                     traceM $ "Potential variants:  " ++ show (pretty (map (\tn -> Map.lookup tn (am^.adts)) traits))
                  Nothing ->
                     traceM $ "Cannot find " ++ fmt nm ++ " in static trait map"
            return Nothing

-- Coerce an Adt value with parameters in 'subst' to an adt value with parameters in 'asubsts'
-- The ADT is a tagged union, so to do the coercion, we need to switch through the potential
-- variants, and when we find that one, coerce the fields of that variant.

-- For simplicity, this function only works for Adts with variants that have <= 2 fields.
-- TODO: make it work with n fields
type Coercion = forall h s ret. HasCallStack => M.Ty -> (M.Ty, MirExp s) -> MirGenerator h s ret (MirExp s)

coerceAdt :: forall h s ret. HasCallStack => Bool ->
      M.DefId
   -> Substs
   -> Substs
   -> R.Expr MIR s TaggedUnion
   -> MirGenerator h s ret (R.Expr MIR s TaggedUnion)
coerceAdt dir adt substs asubsts e0 = do
  let f :: Coercion
      f = if dir then coerceArg else coerceRet

  am <- use collection
  let variants = case (am^.adts) Map.!? adt of
                    Just (M.Adt _ vs) -> vs
                    Nothing -> fail $ "Cannot find declaration for adt: " ++ show adt

  let idx :: R.Expr MIR s C.NatType
      idx = (S.getStruct Ctx.i1of2 e0)
  let dat :: R.Expr MIR s C.AnyType
      dat = (S.getStruct Ctx.i2of2 e0)

  let loop :: Natural -> [M.Variant] -> R.Expr MIR s C.AnyType
           -> MirGenerator h s ret (R.Expr MIR s C.AnyType)
      loop _n [] e = return e 
      loop n (variant@(M.Variant _name _ fields _) : variants) e = do 
         G.ifte (R.App (E.BaseIsEq knownRepr (R.App (E.NatLit n)) idx))
            (do let ec_type = if dir then variantToRepr variant asubsts
                                     else variantToRepr variant substs

                case ec_type of
                   -- i.e. None
                   Some Ctx.Empty -> return e
                   -- i.e. Some
                   Some cr@(Ctx.Empty Ctx.:> tr) -> do
                     let atyp = fieldToTy (substField asubsts (List.head fields))
                     let typ  = fieldToTy (substField substs  (List.head fields))
                     let sr = C.StructRepr cr
                     let unp = (S.app $ E.FromJustValue sr (S.app $ E.UnpackAny sr e)
                                       ("not the expected type"))
                     (MirExp tr' e') <- f typ (atyp, MirExp tr (S.getStruct Ctx.baseIndex unp))
                     let updated = S.mkStruct (Ctx.Empty Ctx.:> tr') (Ctx.empty `Ctx.extend` e')
                     let packed  = R.App (E.PackAny (C.StructRepr (Ctx.Empty Ctx.:> tr'))
                                         updated)
                     return $ packed
                   -- i.e. cons
                   Some cr@(Ctx.Empty Ctx.:> tr1 Ctx.:> tr2) -> do
                     let aty1:aty2:[] = map (fieldToTy . substField asubsts) fields
                     let typ1:typ2:[] = map (fieldToTy . substField substs) fields
                     let sr = C.StructRepr cr
                     let unpacked = (S.app $ E.FromJustValue sr (S.app $ E.UnpackAny sr e)
                                       ("not the expected type"))
                     (MirExp tr1' e1') <- f typ1 (aty1, MirExp tr1 (S.getStruct Ctx.i1of2 unpacked))
                     (MirExp tr2' e2') <- f typ2 (aty2, MirExp tr2 (S.getStruct Ctx.i2of2 unpacked))
                     let cr' = (Ctx.Empty Ctx.:> tr1' Ctx.:> tr2')
                     let updated = S.mkStruct cr' (Ctx.empty Ctx.:> e1' Ctx.:> e2' )
                     let packed  = R.App (E.PackAny (C.StructRepr cr') updated)
                     return $ packed

                   _ -> fail "unhandled coerceArg, variant with more than 1 field")
            (loop (n+1) variants e)
  res <- loop 0 variants dat
  return $ S.mkStruct (Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr)
                      (Ctx.empty Ctx.:> idx Ctx.:> res)



-- If we are calling a polymorphic function, we may need to coerce the type of the argument
-- so that it has the right type.
coerceArg :: forall h s ret. HasCallStack => M.Ty -> (M.Ty, MirExp s) -> MirGenerator h s ret (MirExp s)
coerceArg ty (aty, e@(MirExp tr e0)) | M.isPoly ty = do
  case (ty,aty,tr) of
     (M.TyRef ty1 M.Immut, M.TyRef aty1 M.Immut, _) -> coerceArg ty1 (aty1, e)
     (M.TyAdt adt substs,   -- polymorphic type of the parameter
      M.TyAdt _   asubsts,  -- actual Mir type of the argument, including actual substitution
      C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr)) -> do
        tagged <- coerceAdt True adt substs asubsts e0
        return (MirExp taggedUnionRepr tagged)

     -- Some types already have 'any' in the right place, so no need to coerce
     (M.TyParam _, M.TyClosure _ _, _) -> return e     
     (M.TySlice (M.TyParam _),   _, C.VectorRepr C.AnyRepr) -> return e
     (M.TyArray (M.TyParam _) _, _, C.VectorRepr C.AnyRepr) -> return e

     -- however, if the type is mutable, this is a bit suspicious. I'm not sure that
     -- we'll ever be able to call these polymorphic functions with mutable values
     (M.TyRef (M.TySlice (M.TyParam _)) M.Mut, _, MirSliceRepr C.AnyRepr) -> return e
     (M.TyRef (M.TyParam _) M.Mut,  _, MirReferenceRepr  C.AnyRepr) -> return e

     (M.TyParam _,_, _) -> return $ packAny e

     _ -> fail $ "poly type " ++ show ty ++ " unsupported in fcn call for " ++ show tr
               ++ " with aty " ++ show aty

     -- leave all others alone
               | otherwise = return e

-- Coerce the return type of a polymorphic function 
coerceRet :: forall h s ret. HasCallStack =>
            M.Ty             -- ^ declared return type of the fcn
         -> (M.Ty, MirExp s) -- ^ expected return type by the context, expression to coerce
         -> MirGenerator h s ret (MirExp s)
coerceRet ty (aty, e@(MirExp tr e0)) | M.isPoly ty = do
   case (ty,aty,tr) of
     (M.TyRef ty1 M.Immut, M.TyRef aty2 M.Immut,_) -> coerceRet ty1 (aty2,e)
     (M.TyParam _, M.TyClosure _ _, _) -> return e

     (M.TyArray (M.TyParam _) _, _, C.VectorRepr C.AnyRepr) -> return e
     (M.TySlice (M.TyParam _), _, C.VectorRepr C.AnyRepr) -> return e
     (M.TyRef (M.TySlice (M.TyParam _)) M.Mut, _, MirSliceRepr C.AnyRepr) -> return e
     (M.TyRef (M.TyParam _) M.Mut,  _, MirReferenceRepr  C.AnyRepr) -> return e

     (M.TyParam _,_,C.AnyRepr) -> unpackAny (tyToRepr aty) e
     (M.TyAdt adt substs,   -- polymorphic type of the parameter
      M.TyAdt _   asubsts,  -- actual Mir type of the argument, including actual substitution
      C.StructRepr (Ctx.Empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr)) -> do
        tagged <- coerceAdt False adt substs asubsts e0
        return (MirExp taggedUnionRepr tagged)
     _ -> fail $ "poly type " ++ show (pretty ty) ++
                 " unsupported in fcn return for " ++ show tr
-- leave all others alone
                   | otherwise = return e


-- regular function calls: closure calls & dynamic trait method calls handled later
doCall :: forall h s ret a. (HasCallStack) => M.DefId -> Substs -> [M.Operand] 
   -> Maybe (M.Lvalue, M.BasicBlockInfo) -> C.TypeRepr ret -> MirGenerator h s ret a
doCall funid funsubst cargs cdest retRepr = do
    _hmap <- use handleMap
    _tmap <- use traitMap
    am    <- use collection
    db    <- use debugLevel
    mhand <- lookupFunction funid funsubst
    case cdest of 
      (Just (dest_lv, jdest))


         -- custom call where we first evaluate the arguments to MirExps
         | Just (CustomOp op) <- lookupCustomFunc funid funsubst -> do
            when (db > 3) $
              traceM $ fmt (PP.fillSep [PP.text "At custom function call of",
                   pretty funid, PP.text "with arguments", pretty cargs, 
                   PP.text "and type parameters:", pretty funsubst])

            ops <- mapM evalOperand cargs
            let opTys = map M.typeOf cargs
            res <- op opTys (M.typeOf dest_lv) ops
            assignLvExp dest_lv res
            jumpToBlock jdest

         -- custom call where we pass the arguments in directly (as Mir operands)
         | Just (CustomMirOp op) <- lookupCustomFunc funid funsubst -> do
            when (db > 3) $
              traceM $ fmt (PP.fillSep [PP.text "At custom function call of",
                   pretty funid, PP.text "with arguments", pretty cargs, 
                   PP.text "and type parameters:", pretty funsubst])

            res <- op cargs
            assignLvExp dest_lv res
            jumpToBlock jdest

        -- normal function call (could be through a dictionary argument or a static trait)
        -- need to construct any dictionary arguments for predicates (if present)
        | Just (MirExp (C.FunctionHandleRepr ifargctx ifret) polyinst, preds) <- mhand -> do
            when (db > 3) $
               traceM $ fmt (PP.fillSep [PP.text "At normal function call of",
                   pretty funid, PP.text "with arguments", pretty cargs,
                   PP.text "predicates:", PP.list (map pretty preds),
                   PP.text "and type parameters:", pretty funsubst])

            -- Make a dictionary for the function call
            let mkDict :: (Var, Predicate) -> MirGenerator h s ret (MirExp s)
                mkDict (var, pred@(TraitPredicate tn (Substs ss))) = do
                  vm <- use varMap
                  case Map.lookup (var^.varname) vm of
                    Just _ -> lookupVar var
                    Nothing -> do
                      let (TyAdt did subst)              = var^.varty
                      let (Adt _ [Variant _ _ fields _]) = case (am^.adts) Map.!? did of
                                                             Just adt -> adt
                                                             Nothing  -> error $ "Cannot find " ++ fmt did ++ " in adts"
                      let go :: Field -> MirGenerator h s ret (MirExp s)
                          go (Field fn (TyFnPtr sig) _) = do
                            mhand <- lookupFunction fn subst
                            case mhand of
                              Just (e,[])    -> return e
                              Just (e,preds) -> do
                                 let sig' = tySubst (Substs ss) sig
                                 if (preds /= sig' ^. fspredicates) then do
                                    traceM $ "WARNING: For dictionary for " ++ fmt pred
                                    traceM $ "and member item " ++ fmt fn ++ " of type " ++ fmt sig
                                    traceM $ "Found preds " ++ fmt preds
                                    traceM $ "Need preds " ++ fmt (sig' ^.fspredicates)
                                    return e
                                 else
                                    return e -- error $ "found predicates when building a dictionary for " ++ show var
                              Nothing     -> error $ "when building a dictionary for " ++  fmt var
                                                  ++ " couldn't find an entry for " ++ fmt fn
                                                  ++ " of type " ++ fmt (var^.varty)
                      when (db > 3) $ traceM $ "Building dictionary for " ++ fmt pred
                                    ++ " of type " ++ fmt (var^.varty)
                      entries <- mapM go fields
                      when (db > 3) $ traceM $ "Done building dictionary for " ++ fmt var
                      return $ buildTaggedUnion 0 entries

            exps <- mapM evalOperand cargs

            dexps <- mapM mkDict (Maybe.mapMaybe (\x -> (,x) <$> (dictVar x)) preds)

            exp_to_assgn (exps ++ dexps) $ \ctx asgn -> do
                case (testEquality ctx ifargctx) of
                  Just Refl -> do
                    ret_e <- G.call polyinst asgn
                    assignLvExp dest_lv (MirExp ifret ret_e)
                    jumpToBlock jdest
                  _ -> fail $ "type error in call: args " ++ (show ctx) ++ "\n vs function params "
                                 ++ show ifargctx ++ "\n while calling " ++ show (pretty funid)
             
         | otherwise -> fail $ "Don't know how to call " ++ fmt funid ++ "\n mhand is " ++ show mhand

      Nothing
         -- special case for exit function that does not return
         | Just CustomOpExit <- lookupCustomFunc funid funsubst,
               [o] <- cargs -> do
               _exp <- evalOperand o
               G.reportError (S.app $ E.TextLit "Program terminated with exit:")

        -- other functions that don't return.
{-
        | Just (MirHandle _ sig fhandle) <- mhand,
          isNever ret -> do

            -- traceM $ show (vcat [text "At a tail call of ", pretty funid, text " with arguments ", pretty cargs,
            --       text "with type parameters: ", pretty funsubst])

            exps <- mapM evalOperand cargs
            tyListToCtx (Maybe.catMaybes funsubst) $ \tyargs -> do

              let fargctx = FH.handleArgTypes fhandle
              let fret    = FH.handleReturnType fhandle
              let ifargctx = C.instantiate tyargs fargctx

--            cexps <- zipWithM coerceArg args (zip (map M.typeOf cargs) exps)
              exp_to_assgn exps $ \ctx asgn -> do
                case (testEquality ctx ifargctx) of
                  (Just Refl) -> do
                       let polyfcn  = R.App $ E.PolyHandleLit fhandle
                       let polyinst = R.App $ E.PolyInstantiate (C.PolyFnRepr fargctx fret) polyfcn tyargs

                       _ <- G.call polyinst asgn
                       G.reportError (S.app $ E.TextLit "Program terminated with exit:")

                  _ -> fail $ "type error in call: args " ++ (show ctx)   ++ " vs function params " ++ show fargctx 
                                 ++ "\n expected ret " ++ show retRepr  ++ " vs function ret " ++ show fret
                                 ++ "\n while calling " ++ show funid

-}
         | otherwise -> fail $ "no dest in doCall of " ++ show (pretty funid)

-- Method/trait calls
      -- 1. translate `traitObject` -- should be a Ref to a tuple
      -- 2. the first element should be Ref Any. This is the base value. Unpack the Any behind the Ref and stick it back into a Ref.
      -- 3. the second element should be a Struct that matches the context repr in `tis^.vtableTyRepr`.
      -- 4. index into that struct with `midx` and retrieve a FunctionHandle value
      -- 5. Call the FunctionHandle passing the reference to the base value (step 2), and the rest of the arguments (translated)

methodCall :: HasCallStack =>
     TraitName -> MethName -> Substs -> M.Operand -> [M.Operand] -> Maybe (M.Lvalue, M.BasicBlockInfo) -> MirGenerator h s ret a
methodCall traitName methodName (Substs funsubst) traitObject args (Just (dest_lv,jdest)) = do
  (Some tis) <- traitImplsLookup traitName
  case Map.lookup methodName $ tis^.methodIndex of
    Nothing -> fail $ Text.unpack $ Text.unwords $ ["Error while translating a method call: no such method ",
                                                    M.idText methodName, " in trait ", M.idText traitName]
    Just (Some midx) -> do
      -- type of the vtable for this trait object, instantiated with "Any"
      let substR     = Ctx.singleton C.AnyRepr 
      let vtableRepr = implementCtxRepr substR (tis^.vtableTyRepr)
      -- polymorphic type of the method <<specialized to object>>
      let midx'      = implementIdx substR midx
      let fnRepr     = vtableRepr Ctx.! midx'

      -- the object itself and its type (which should be C.AnyRepr)
      (MirExp tp e) <- evalOperand traitObject
      exps          <- mapM evalOperand args
      case testEquality tp C.AnyRepr of 
        Just Refl -> do
          
          let objTy     = C.StructRepr (Ctx.Empty Ctx.:> C.AnyRepr Ctx.:> C.StructRepr vtableRepr)
          let e1        = R.App $ E.UnpackAny objTy e
          let e2        = R.App $ E.FromJustValue objTy e1 (R.App (E.TextLit (fromString "unpack to struct")))
          let _baseValue = R.App $ E.GetStruct e2 Ctx.i1of2 C.AnyRepr 
          let vtable    = R.App $ E.GetStruct e2 Ctx.i2of2 (C.StructRepr vtableRepr)
          let fn        = R.App $ E.GetStruct vtable midx' fnRepr
          case fnRepr of
             C.FunctionHandleRepr fargctx fret ->
                exp_to_assgn exps $ \ctx asgn -> do
                  case (testEquality ctx fargctx ) of
                     Just Refl -> do
                       ret_e <- G.call fn asgn
                       assignLvExp dest_lv (MirExp fret ret_e)
                       jumpToBlock jdest
                     Nothing -> fail $ "type error in TRAIT call: args " ++ (show ctx) ++ " vs function params "
                                 ++ show fargctx ++ " while calling " ++ show fn
             C.PolyFnRepr k fargctx fret ->
               tyListToCtx (reverse funsubst) $ \subst -> do
                 case testEquality (ctxSizeP subst) k of
                   Just Refl -> do
                     let fargctx' = C.instantiate (C.mkSubst subst) fargctx
                     let fret'    = C.instantiate (C.mkSubst subst) fret
                     exp_to_assgn exps $ \ctx asgn -> do
                        case (testEquality ctx fargctx') of
                          Just Refl -> do
                            ret_e <- G.call (R.App $ E.PolyInstantiate fnRepr fn subst) asgn
                            assignLvExp dest_lv (MirExp fret' ret_e)
                            jumpToBlock jdest
                          Nothing -> fail $ "type error in TRAIT call: args " ++ (show ctx) ++ " vs function params "
                                     ++ show fargctx'
                   Nothing -> error $ "TODO: " ++ show k ++ " /=  " ++ show (ctxSizeP subst)
             _ -> fail $ "type error in TRAIT call: " ++ show fnRepr 
                        
        Nothing -> fail $ unwords $ ["Type error when calling ", show methodName, " type is ", show tp]
methodCall _ _ _ _ _ _ = fail "No destination for method call"


transTerminator :: HasCallStack => M.Terminator -> C.TypeRepr ret -> MirGenerator h s ret a
transTerminator (M.Goto bbi) _ =
    jumpToBlock bbi
transTerminator (M.SwitchInt swop _swty svals stargs) _ | all Maybe.isJust svals = do
    s <- evalOperand swop
    transSwitch s (Maybe.catMaybes svals) stargs
transTerminator (M.Return) tr =
    doReturn tr
transTerminator (M.DropAndReplace dlv dop dtarg _) _ = do
    transStatement (M.Assign dlv (M.Use dop) "<dummy pos>")
    jumpToBlock dtarg

transTerminator (M.Call (M.OpConstant (M.Constant _ (M.Value (M.ConstFunction funid funsubsts)))) cargs cretdest _) tr = do
             
    case (funsubsts, cargs) of
      (Substs (M.TyDynamic traitName : _), tobj:_args) |
       False  <- memberCustomFunc funid funsubsts -> do
        -- this is a method call on a trait object, and is not a custom function
        db <- use debugLevel
        when (db > 2) $
           traceM $ show (PP.sep [PP.text "At TRAIT function call of ", pretty funid, PP.text " with arguments ", pretty cargs, 
                   PP.text "with type parameters: ", pretty funsubsts])

        methodCall traitName funid funsubsts tobj cargs cretdest

      _ -> do -- this is a normal function call
        doCall funid funsubsts cargs cretdest tr -- cleanup ignored
        
transTerminator (M.Assert _cond _expected _msg target _cleanup) _ =
    jumpToBlock target -- FIXME! asserts are ignored; is this the right thing to do? NO!
transTerminator (M.Resume) tr =
    doReturn tr -- resume happens when unwinding
transTerminator (M.Drop _dl dt _dunwind) _ =
    jumpToBlock dt -- FIXME! drop: just keep going
transTerminator M.Unreachable tr =
    G.reportError (S.litExpr "Unreachable")
transTerminator t _tr =
    fail $ "unknown terminator: " ++ (show t)


--- translation of toplevel glue ---

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
-- With this code, it is possible for mir-verifier to miss
-- uninitialized values.  So we should revisit this.
--
initialValue :: HasCallStack => M.Ty -> MirGenerator h s ret (Maybe (MirExp s))
initialValue M.TyBool       = return $ Just $ MirExp C.BoolRepr (S.false)
initialValue (M.TyTuple []) = return $ Just $ MirExp C.UnitRepr (R.App E.EmptyApp)
initialValue (M.TyTuple tys) = do
    mexps <- mapM initialValue tys
    return $ Just $ buildTupleMaybe tys mexps
initialValue (M.TyInt M.USize) = return $ Just $ MirExp C.IntegerRepr (S.litExpr 0)
initialValue (M.TyInt sz)      = baseSizeToNatCont sz $ \w ->
    return $ Just $ MirExp (C.BVRepr w) (S.app (E.BVLit w 0))
initialValue (M.TyUint M.USize) = return $ Just $ MirExp C.NatRepr (S.litExpr 0)
initialValue (M.TyUint sz)      = baseSizeToNatCont sz $ \w ->
    return $ Just $ MirExp (C.BVRepr w) (S.app (E.BVLit w 0))
initialValue (M.TyArray t size) = do
    mv <- initialValue t 
    case mv of
      Just (MirExp tp e) -> do
        let n = fromInteger (toInteger size)
        return $ Just $ MirExp (C.VectorRepr tp) (S.app $ E.VectorReplicate tp (S.app $ E.NatLit n) e)
      Nothing -> return Nothing
initialValue (M.TyRef (M.TySlice t) M.Immut) = do
    tyToReprCont t $ \ tr ->
      return $ Just (MirExp (C.VectorRepr tr) (S.app $ E.VectorLit tr V.empty))
initialValue (M.TyRef (M.TySlice t) M.Mut) = do
    tyToReprCont t $ \ tr -> do
      ref <- newMirRef (C.VectorRepr tr)      
      let i = (MirExp C.NatRepr (S.litExpr 0))
      return $ Just $ buildTuple [(MirExp (MirReferenceRepr (C.VectorRepr tr)) ref), i, i]
      -- fail ("don't know how to initialize slices for " ++ show t)
initialValue (M.TyRef t M.Immut) = initialValue t
initialValue (M.TyRef t M.Mut) = do
    mv <- initialValue t
    case mv of
      Just (MirExp tp e) -> do
        ref <- newMirRef tp
        writeMirRef ref e
        return $ Just (MirExp (MirReferenceRepr tp) ref)
      Nothing -> return Nothing
initialValue M.TyChar = do
    let w = (knownNat :: NatRepr 32)
    return $ Just $ MirExp (C.BVRepr w) (S.app (E.BVLit w 0))
initialValue M.TyStr =
   return $ Just $ (MirExp C.StringRepr (S.litExpr ""))
initialValue (M.TyClosure defid (Substs (_i8:hty:closed_tys))) = do
   -- TODO: figure out what the first i8 type argument is for   
   mclosed_args <- mapM initialValue closed_tys
   let closed_args = filterMaybes mclosed_args
   handle <- buildClosureHandle defid (Substs closed_tys) closed_args
   return $ Just $ handle

-- NOTE: this case is wrong in the case of enums --- we need to know
-- which branch of the ADT to initialize, so we arbitrarily pick the
-- first one. However, hopefully the allocateEnum pass will have
-- converted these adt initializations to aggregates already so this
-- won't matter.
initialValue (M.TyAdt nm args) = do
    am <- use collection
    case Map.lookup nm (am^.adts) of
       Nothing -> return $ Nothing
       Just (M.Adt _ []) -> fail ("don't know how to initialize void adt " ++ show nm)
       Just (M.Adt _ (Variant _vn _disc fds _kind:_)) -> do
          let initField (Field _name ty _subst) = initialValue (tySubst args ty)
          fds <- mapM initField fds
          let union = buildTaggedUnion 0 (Maybe.catMaybes fds)
          return $ Just $ union
initialValue (M.TyFnPtr _) =
   return $ Nothing
initialValue (M.TyDynamic _) =
   return $ Nothing
initialValue (M.TyProjection _ _) =
   return $ Nothing
initialValue (M.TyCustom (CEnum _n _i)) =
   return $ Just $ MirExp C.IntegerRepr (S.litExpr 0)
initialValue _ = return Nothing


tyToInitReg :: HasCallStack => Text.Text -> M.Ty -> MirGenerator h s ret (Some (R.Reg s))
tyToInitReg nm t = do
   mv  <- initialValue t
   db  <- use debugLevel
   case mv of 
      Just (MirExp _tp exp) -> Some <$> G.newReg exp
      Nothing -> do
        when (db > 5) $ do
           traceM $ "tyToInitReg: Cannot initialize register of type " ++ show (pretty t)
        tyToFreshReg nm t

tyToFreshReg :: HasCallStack => Text.Text -> M.Ty -> MirGenerator h s ret (Some (R.Reg s))
tyToFreshReg nm t = do
    tyToReprCont t $ \tp -> do
        r <-  G.newUnassignedReg tp
        return $ Some r


buildIdentMapRegs_ :: HasCallStack => Set Text.Text -> Set Text.Text -> [(Text.Text, M.Ty)] -> MirGenerator h s ret (VarMap s)
buildIdentMapRegs_ addressTakenVars needsInitVars pairs = foldM f Map.empty pairs
  where
  f map_ (varname, varty)
    | varname `Set.member` addressTakenVars =
        tyToReprCont varty $ \tp ->
           do reg <- G.newUnassignedReg (MirReferenceRepr tp)
              return $ Map.insert varname (Some (VarReference reg)) map_

    | varname `Set.member` needsInitVars = 
        do Some r <- tyToInitReg varname varty 
           return $ Map.insert varname (Some (VarRegister r)) map_

    | otherwise =
        do Some r <- tyToFreshReg varname varty
           return $ Map.insert varname (Some (VarRegister r)) map_

-- | Look at all of the assignments in the basic block and return
-- the set of variables that have their addresses computed
addrTakenVars :: M.BasicBlock -> Set Text.Text
addrTakenVars bb = mconcat (map f (M._bbstmts (M._bbdata bb)))
 where
 f (M.Assign _ (M.Ref M.Mutable lv _) _) = g lv
 f _ = mempty

 g (M.Local (M.Var nm _ _ _ _)) = Set.singleton nm
 g (M.LProjection (M.LvalueProjection lv _)) = g lv
 g (M.Tagged lv _) = g lv

 g _ = mempty


buildIdentMapRegs :: forall h s ret. HasCallStack => M.MirBody -> [M.Var] -> MirGenerator h s ret (VarMap s)
buildIdentMapRegs (M.MirBody localvars blocks) extravars =
   buildIdentMapRegs_ addressTakenVars needsInitVars (map (\(M.Var name _ ty _ _) -> (name,ty)) (localvars ++ extravars))
 where
   addressTakenVars = mconcat (map addrTakenVars blocks)
   -- "allocate" space for return variable
   needsInitVars = Set.fromList ["_0"]


buildLabelMap :: forall h s ret. M.MirBody -> MirGenerator h s ret (LabelMap s)
buildLabelMap (M.MirBody _ blocks) = Map.fromList <$> mapM buildLabel blocks

buildLabel :: forall h s ret. M.BasicBlock -> MirGenerator h s ret (M.BasicBlockInfo, R.Label s)
buildLabel (M.BasicBlock bi _) = do
    lab <- G.newLabel
    return (bi, lab)
-- | Build the initial state for translation
initFnState :: FnState s
            -> [(Text.Text, M.Ty)]                 -- ^ names and MIR types of args
            -> C.CtxRepr args                     -- ^ crucible types of args
            -> Ctx.Assignment (R.Atom s) args      -- ^ register assignment for args
            -> [Predicate]                         -- ^ predicates on type args
            -> FnState s
initFnState fnState vars argsrepr args preds = fnState { _varMap = (go (reverse vars) argsrepr args Map.empty), _preds = preds }
    where go :: [(Text.Text, M.Ty)] -> C.CtxRepr args -> Ctx.Assignment (R.Atom s) args -> VarMap s -> VarMap s
          go [] ctx _ m
            | Ctx.null ctx = m
            | otherwise = error "wrong number of args"
          go ((name,ti):ts) ctx asgn m =
            unfold_ctx_assgn ti ctx asgn $ \(Some atom) ctx' asgn' ->
                 go ts ctx' asgn' (Map.insert name (Some (VarAtom atom)) m)


-- do the statements and then the terminator
translateBlockBody :: HasCallStack => C.TypeRepr ret -> M.BasicBlockData -> MirGenerator h s ret a
translateBlockBody tr (M.BasicBlockData stmts terminator) = (mapM_ transStatement stmts)
   >> (transTerminator terminator tr)

--
registerBlock :: HasCallStack => C.TypeRepr ret -> M.BasicBlock -> MirGenerator h s ret ()
registerBlock tr (M.BasicBlock bbinfo bbdata)  = do
    lm <- use labelMap
    case (Map.lookup bbinfo lm) of
      Just lab -> do
        G.defineBlock lab (translateBlockBody tr bbdata)
      _ -> fail "bad label"


--------------------------------------------------------------------------------------------
-- Reasoning about predicates that we know something about and that perhaps we can turn into
-- additional vtable arguments for this function

-- This is a bit of a hack for higher-order functions
-- We always handle these via custom functions so there is
-- no need to pass dictionary arguments for them
-- REVISIT this!
noDictionary :: [TraitName]
noDictionary = [M.textId "::ops[0]::function[0]::Fn[0]",
                M.textId "::ops[0]::function[0]::FnMut[0]",
                M.textId "::ops[0]::function[0]::FnOnce[0]"]

-- | create a Var corresponding to a trait predicate
dictVar :: Predicate -> Maybe Var
dictVar (TraitPredicate did substs) | not (elem did noDictionary) = Just $ mkPredVar (TyAdt did substs)
                                    | otherwise = Nothing
dictVar (TraitProjection _ _ _)     = Nothing
dictVar UnknownPredicate            = Nothing

-- | define the type of a dictionary Var
dictTy  :: Predicate -> Maybe Ty
dictTy (TraitPredicate did substs) | not (elem did noDictionary) = Just $ (TyAdt did substs)
                                   | otherwise = Nothing
dictTy (TraitProjection _ _ _)     = Nothing
dictTy UnknownPredicate            = Nothing

-- | make a variable corresponding to a dictionary type
-- NOTE: this could make a trait for Fn/FnMut/FnOnce
mkPredVar :: Ty -> M.Var
mkPredVar ty@(TyAdt did _) = Var {
                _varname  = M.idText did
              , _varmut   = M.Immut
              , _varty    = ty
              , _varscope = "dictionary"
              , _varpos   = "dictionary argument"
              }
mkPredVar ty = error $ "BUG in mkPredVar: must provide Adt type"

-------------------------------------------------------------------------------------------



-- | Translate a MIR function, returning a jump expression to its entry block
-- argvars are registers
-- The first block in the list is the entrance block
genFn :: HasCallStack => M.Fn -> C.TypeRepr ret -> MirGenerator h s ret (R.Expr MIR s ret)
genFn (M.Fn fname argvars sig body@(MirBody localvars blocks)) rettype = do
  TraitMap _tm <- use traitMap
  let gens  = sig^.fsgenerics
  let preds = sig^.fspredicates
  let atys  = sig^.fsassoc_tys
  
  lm <- buildLabelMap body
  labelMap .= lm

  vm' <- buildIdentMapRegs body []
  varMap %= Map.union vm'


  db <- use debugLevel
  when (db > 3) $ do
     vmm <- use varMap
     let showVar var = fmt var ++ " : " ++ fmt (M.typeOf var)
     traceM $ "-----------------------------------------------------------------------------"
     traceM $ "Generating code for: " ++ show fname
     traceM $ "Generics are: " ++  fmt(map pretty gens)
     traceM $ "Predicates are: " ++ fmt  (map pretty preds)
     traceM $ "Function args are: " ++ List.intercalate "," (map showVar argvars)
     traceM $ "VarMap is: " ++ fmt (Map.keys vmm)
     traceM $ "Associated types are: " ++ fmt (map pretty atys)
     traceM $ "Body is:\n" ++ fmt body
     traceM $ "-----------------------------------------------------------------------------"
  let (M.MirBody _mvars blocks@(enter : _)) = body
  -- actually translate all of the blocks of the function
  mapM_ (registerBlock rettype) blocks
  let (M.BasicBlock bbi _) = enter
  lm <- use labelMap
  case (Map.lookup bbi lm) of
    Just lbl -> do
       G.jump lbl
    _ -> fail "bad thing happened"

transDefine :: forall h. HasCallStack =>
  Map M.DefId Adt ->
  (forall s. FnState s) ->
  M.Fn ->
  ST h (Text, Core.AnyCFG MIR)
transDefine adts fnState fn@(M.Fn fname fargs fsig _) =
  case (Map.lookup fname (fnState^.handleMap)) of
    Nothing -> fail "bad handle!!"
    Just (MirHandle _hname _hsig (handle :: FH.FnHandle args ret)) -> do
      let argPredVars = Maybe.mapMaybe dictVar (fsig^.fspredicates)
      let argtups  = map (\(M.Var n _ t _ _) -> (n,t)) (fargs ++ argPredVars)
      let argtypes = FH.handleArgTypes handle
      let rettype  = FH.handleReturnType handle
      let def :: G.FunctionDef MIR handle FnState args ret
          def inputs = (s,f) where
            s = initFnState fnState argtups argtypes inputs (fsig^.fspredicates)
            f = genFn fn rettype
      (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos handle def
      case SSA.toSSA g of
        Core.SomeCFG g_ssa -> return (M.idText fname, Core.AnyCFG g_ssa)


-- | Decide whether the given method definition is a specific implementation method for
-- a declared trait. If so, return all such declared traits along with the type substitution
-- SCW NOTE: we are returning a list because the same method may implement several different
-- traits depending due to subtraits
-- ?: Do subtraits need to have the same params???
getTraitImplementation ::
      Collection                  -- ^ the collection
   -> MethName                    -- ^ specific function in the collection
   -> [(TraitRef,TraitImplItem)]  -- ^ traits that this function could implement
getTraitImplementation col name = do
    let timpls      = col^.impls

    -- If the implementation includes associated types, add them
    -- to the substitution (as we have generalized them from all of the
    -- methods in a prior pass)
    let addAssocTypes :: [TraitImplItem] -> TraitRef -> TraitRef
        addAssocTypes tiis (TraitRef tn (Substs subs)) =
          TraitRef tn (Substs (subs ++ assocs))
            where
              assocs = Maybe.mapMaybe getTy tiis
              getTy (TraitImplType _ _ _ _ ty) = Just ty
              getTy _ = Nothing

    -- find all traitImplItems with the same name 
    let implItems = [ (addAssocTypes (ti^.tiItems) (ti^.tiTraitRef),tii) |
                      ti <- timpls,
                      tii <- ti^.tiItems,
                      tii^.tiiName == name ]

    -- make references for subtraits too
    -- find all traits that extend this one
    let getSubImpl (TraitRef tn subst, tii) 
          = [ (TraitRef (t^.traitName) subst, tii) 
            | t <- Map.elems (col^.traits)
            , tn `elem` t^.traitSupers ] 


    let isImpl (TraitRef tn _,_) (TraitRef sn _, _) = tn == sn

    let go curr =
         let subs = concatMap getSubImpl curr
         in if all (\sn -> any (isImpl sn) curr) subs
            then curr
            else go (List.nub (curr ++ subs))
                            
    go implItems




-- | Allocate method handles for each of the functions in the Collection
-- Fn preds must include *all* predicates necessary for translating
-- the fbody at this point (i.e. "recursive" predicates for impls)
-- and these preds must already have their associated types abstracted???
mkHandleMap :: forall s. HasCallStack => Collection -> FH.HandleAllocator s -> ST s HandleMap
mkHandleMap col halloc = mapM mkHandle (col^.functions) where

    mkHandle :: M.Fn -> ST s MirHandle
    mkHandle (M.Fn fname fargs ty _fbody)  =
       let
           -- add dictionary args to type
           targs = map typeOf (fargs ++ Maybe.mapMaybe dictVar (ty^.fspredicates))

           handleName = FN.functionNameFromText (M.idText fname)
       in

          tyListToCtx targs $ \argctx ->
          tyToReprCont (ty^.fsreturn_ty) $ \retrepr -> do
             h <- FH.mkHandle' halloc handleName argctx retrepr
             return $ MirHandle fname ty h 


--------------------------------------------------------------------------------------

-- Create the dictionary adt type for a trait
-- The dictionary is a record (i.e. an ADT with a single variant) with
-- a field for each method in the trait.
-- Ignore non-method components of the trait
defineTraitAdts :: Map TraitName M.Trait -> Map TraitName M.Adt
defineTraitAdts traits = fmap traitToAdt traits where
   traitToAdt :: M.Trait -> M.Adt
   traitToAdt tr = do

     let itemToField :: M.TraitItem -> Maybe M.Field
         itemToField (M.TraitMethod did fnsig) = do
           let fnsig' = specialize fnsig ntys 
           return $ M.Field did (TyFnPtr fnsig') (Substs [])
         itemToField _ = Nothing

         n    = length (tr^.traitParams)
         ntys = take n (TyParam <$> [0 .. ])

     let fields = Maybe.mapMaybe itemToField (tr^.traitItems)
     M.Adt (tr^.traitName) [M.Variant (tr^.traitName) (Relative 0) fields M.FnKind]

--------------------------------------------------------------------------------------
--
-- Most of the implementation of this pass is in GenericOps

passRemoveUnknownPreds :: Collection -> Collection
passRemoveUnknownPreds col = modifyPreds ff col 
  where
     ff did = Map.member did trs
     trs = col^.traits


--------------------------------------------------------------------------------------
-- Some functions need additional predicates because they are trait implementations
-- This pass adds those predicates to trait declarations and then uses those to add them
-- to function implementations
-- 
passAddDictionaryPreds :: Collection -> Collection
passAddDictionaryPreds col = col1 & functions %~ fmap addTraitPreds  where

  col1 = col & traits  %~ fmap addThisPred

  mkPred :: Trait -> Predicate
  mkPred tn = TraitPredicate (tn^.traitName)
                (Substs [TyParam (toInteger i) | i <- [0 .. ((length (tn^.traitParams)) - 1)] ])

  addThisPred :: Trait -> Trait
  addThisPred trait = trait & traitItems %~ map (addThis (mkPred trait))

  -- add predicates to trait methods
  addThis :: Predicate -> TraitItem -> TraitItem
  addThis pred (TraitMethod did sig) = TraitMethod did (sig & fspredicates %~ (addPred [pred]))
  addThis pred ti = ti

  -- add predicates to fn's that are implementation methods
  addTraitPreds :: Fn -> Fn
  addTraitPreds fn = fn & fsig %~ fspredicates %~ (addPred (newPreds fn))

  -- don't add redundant predicates
  addPred :: [Predicate] -> [Predicate] -> [Predicate]
  addPred pred preds = List.nub (pred++preds)

  -- determine the methods that are implementation methods
  -- and the new predicates they should satisfy (== preds for the traits that they impl)
  impls :: Map MethName [Predicate]
  impls = implMethods' col1

  newPreds :: Fn -> [Predicate]
  newPreds fn = Map.findWithDefault [] (fn^.fname) impls 


findMethodItem :: HasCallStack => MethName -> [TraitItem] -> Maybe TraitItem
findMethodItem mn (item@(TraitMethod did fsig):rest) =
  if (mn == did) then Just item else findMethodItem mn rest
findMethodItem mn (_:rest) = findMethodItem mn rest
findMethodItem mn [] = Nothing -- error $ "BUG: cannot find method " ++ fmt mn

implMethods' :: HasCallStack => Collection -> Map MethName [Predicate]
implMethods' col = foldMap g (col^.impls) where
  g :: TraitImpl -> Map MethName [Predicate]
  g impl = foldMap g2 (impl^.tiItems) where
     TraitRef tn ss = impl^.tiTraitRef
     items = case (col^.traits) Map.!? tn of
                 Just tr -> tr^.traitItems
                 -- Ignore impls that we know nothing about
                 Nothing -> []

     g2 :: TraitImplItem -> Map MethName [Predicate]
     g2 (TraitImplMethod mn ii _ preds _) =
        case findMethodItem ii items of
          Just (TraitMethod _ sig) ->
             Map.singleton mn (tySubst (ss <> (Substs $ TyParam <$> [0 .. ])) (sig^.fspredicates))
          Nothing -> error $ "BUG: addDictionaryPreds: Cannot find method " ++ fmt ii ++ " in trait " ++ fmt tn
     g2 _ = Map.empty

implMethods :: Collection -> Map MethName [(TraitName,Substs)]
implMethods col = foldr g Map.empty (col^.functions) where
  g fn m = foldr g2 m (getTraitImplementation col (fn^.fname)) where
     g2 (TraitRef traitName substs, _tii) m 
         = Map.insertWith (++) (fn^.fname) [(traitName, substs)] m


defaultMethods :: Collection -> Map MethName TraitName
defaultMethods col = foldr g Map.empty (col^.traits) where
  g trait m = foldr g2 m (trait^.traitItems) where
    g2 (TraitMethod methName _sig) m
       | Just _fn <- Map.lookup methName (col^.functions)
       = Map.insert (methName) (trait^.traitName) m
    g2 _ m = m




--------------------------------------------------------------------------------------
infixl 0 |>
(|>) :: a -> (a -> b) -> b
x |> f = f x
--------------------------------------------------------------------------------------

-- | transCollection: translate a MIR module
transCollection :: HasCallStack
      => M.Collection
      -> Int  
      -> FH.HandleAllocator s
      -> ST s (Map Text (Core.AnyCFG MIR))
transCollection col0 debug halloc = do

    -- The first part are some transformations on the collection itself.

    let passAddTraitAdts col       = col & adts   %~ (Map.union (defineTraitAdts (col^.M.traits)))
    let passMarkCStyle col         = markCStyle (cstyleAdts, col) col where
          cstyleAdts = Map.filter isCStyle (col^.M.adts)

    let passTrace :: String -> Collection -> Collection
        passTrace str col =
          if (debug > 3) then 
            ((trace $ "*********MIR collection " ++ str ++ "*******\n"
                    ++ fmt col ++ "\n****************************")
            col)
          else col

    let col  = col0
              |> passRemoveUnknownPreds  -- remove predicates that we don't know anything about
              |> passTrace "initial"
              |> passAddDictionaryPreds  -- add predicates to trait member functions
              |> passTrace "after dict preds"
              |> passExpandSuperTraits   -- add supertrait items
              |> passTrace "after super traits"
              |> passAbstractAssociated  -- replace associated types with additional type parameters
              |> passTrace "after associated types translated"
              |> passMarkCStyle          -- figure out which ADTs are enums and mark them
              |> passAddTraitAdts        -- add adts for declared traits

    when (debug > 3) $ do
      traceM $ "MIR collection"
      traceM $ show (pretty col)

    -- build up the state in the Generator

    hmap <- mkHandleMap col halloc 

    (gtm@(GenericTraitMap gm), stm, morePairs) <- buildTraitMap debug col halloc hmap

    when (debug > 2) $ do
      traceM $ "Trait map"
      traceM $ show (Map.keys gm)

    let fnState :: (forall s. FnState s)
        fnState = case gtm of
                     GenericTraitMap tm -> FnState Map.empty [] Map.empty hmap (TraitMap tm) stm debug col

    -- translate all of the functions
    pairs <- mapM (transDefine (col^.M.adts) fnState) (Map.elems (col^.M.functions))
    return $ Map.fromList (pairs ++ morePairs)

----------------------------------------------------------------------------------------------------------
-- * Traits


-- | The translation of the methods in a trait declaration: includes the types of all components
--   and an indexing map for the vtables
data TraitDecl ctx =
   TraitDecl M.DefId                                -- name of trait (for debugging/error messages)
             Int                                    -- number of trait parameters
             [(M.DefId,M.FnSig)]                    -- declared types of the methods
             (C.CtxRepr ctx)                        -- vtable type 
             (Map MethName (Some (Ctx.Index ctx)))  -- indices into the vtable
             (Map Int MethName)                     -- reverse vtable index (for convenience)

instance Show (TraitDecl ctx) where
  show (TraitDecl nm _n _msig _vtable mm _rm) = "TraitDecl(" ++ show nm ++ ":" ++ show (Map.keys mm) ++ ")"
instance ShowF TraitDecl



-- | Translate a trait declaration
mkTraitDecl :: Trait -> Some TraitDecl
mkTraitDecl tr = do
  let tname     = tr^.traitName
  let numparams = length (tr^.traitParams)
  let titems    = tr^.traitItems
  let meths     = [ (mname, tsig) |(M.TraitMethod mname tsig) <- titems]


  let go :: Some (Ctx.Assignment MethRepr)
         -> (MethName, M.FnSig)
         -> Some (Ctx.Assignment MethRepr)
      go (Some ctxr) (mname, sig)
        | Some ret  <- tyToRepr (sig^.fsreturn_ty)
        , Some args <- tyListToCtx ((sig^.fsarg_tys) ++ Maybe.mapMaybe dictTy (sig^.fspredicates)) Some
        , Some k    <- peanoLength (sig^.fsgenerics)

        = case testEquality k zeroP of
            Just Refl -> Some (ctxr `Ctx.extend` MethRepr mname (C.FunctionHandleRepr args ret))
            Nothing   -> Some (ctxr `Ctx.extend` MethRepr mname (C.PolyFnRepr k  args ret))

  case foldl go (Some Ctx.empty) meths of
    Some (mctxr :: Ctx.Assignment MethRepr ctx) ->
        let
            ctxr    :: Ctx.Assignment C.TypeRepr ctx
            ctxr    = Ctx.fmapFC getReprTy mctxr
            --
            midx    :: Map MethName (Some (Ctx.Index ctx))
            midx    = Ctx.forIndex
                          (Ctx.size mctxr)
                          (\mp idx -> Map.insert (getReprName (mctxr Ctx.! idx)) (Some idx) mp)
                          Map.empty

            -- reverse the method map, for convenience
            rm      :: Map Int MethName
            rm      = Map.foldrWithKey (\ mname (Some idx) m ->
                                             Map.insert (Ctx.indexVal idx) mname m) Map.empty midx

        in

           Some (TraitDecl tname numparams meths ctxr midx rm) 

-- Find an implementation of the given method 
resolveMethod :: Collection
              -> TraitName                       -- ^ trait that contains method
              -> (MethName, M.FnSig)             -- ^ name of method and declared type in trait
              -> (MirHandle, Substs)             -- ^ implementation handle and substs
              -> C.TypeRepr ty                   -- ^ expected type 
              -> Identity (GenericMirValue ty)
resolveMethod col tname (declName, declSig) (implHandle,implSubst) ty =
  case ty of
    C.PolyFnRepr k args ret -> 
       substToSubstCont implSubst $ \subst -> 
         case implHandle of 
           (MirHandle mname sig (fh :: FH.FnHandle fargs fret)) -> do
             let subst' = C.mkSubst subst
             let k'     = minusP k (ctxSizeP subst)
             case (testEquality (FH.handleArgTypes   fh) (C.instantiate subst' args),
                   testEquality (FH.handleReturnType fh) (C.instantiate subst' ret)) of
                 (Just Refl, Just Refl) ->
                   case peanoView k' of
                      SRepr _ ->
                        return (GenericMirValue $ 
                           let expr   = R.App $ E.PolyHandleLit k' fh in
                           let exprTy = C.PolyFnRepr k' (FH.handleArgTypes fh) (FH.handleReturnType fh) in
                           (MirValue subst exprTy expr sig))
                      ZRepr -> case (C.checkClosedCtx (FH.handleArgTypes fh),
                                     C.checkClosed (FH.handleReturnType fh)) of
                        (Just C.Dict, Just C.Dict) ->
                           return (GenericMirValue $
                              let expr   = R.App $ E.HandleLit fh in
                              let exprTy = C.FunctionHandleRepr (FH.handleArgTypes fh) (FH.handleReturnType fh) in
                              (MirValue subst exprTy expr sig))
                        (_,_) -> error $ "Function handle type not closed " ++ show fh
                 (_,_)   -> error $ "Type mismatch in method table for " ++ show tname
                             ++ "\n\tadding implementation: " ++ show mname
                             ++ "\n\timplHandle type is: "        ++ show (FH.handleType fh)
                             ++ "\n\tbut expected type is: "
                                ++ show (C.FunctionHandleRepr (C.instantiate subst' args)
                                                              (C.instantiate subst' ret))
                             ++ "\n\targs before subst: " ++ show args
                             ++ "\n\targs after subst: "  ++ show (C.instantiate subst' args)
                             ++ "\n\tret before subst: " ++ show ret
                             ++ "\n\tret after subst: "  ++ show (C.instantiate subst' ret)

                             ++ "\n\tdeclared name is: " ++ show declName
                             ++ "\n\tdeclared type is: "  ++ fmt (C.PolyFnRepr k args ret)




-- | Build the mapping from traits and types that implement them to VTables
-- For trait objects, this method will (eventually) involve defining new functions that
-- "wrap" (and potentially unwrap) the specific implementations, providing a uniform type for the trait methods. 
buildTraitMap :: Int -> M.Collection -> FH.HandleAllocator s -> HandleMap
              -> ST s (GenericTraitMap, StaticTraitMap, [(Text, Core.AnyCFG MIR)])
buildTraitMap debug col _halloc hmap = do

    when (debug > 6) $ do
       traceM $ "handle map contents in buildTraitMap:" 
       forM_ (Map.assocs hmap) $ \(methName, methHandle) -> do
           traceM $ "\t" ++ show methName

    -- translate the trait declarations
    let decls :: Map TraitName (Some TraitDecl)
        decls = foldr (\ trait m -> Map.insert (trait^.M.traitName) (mkTraitDecl trait) m)
                 Map.empty (col^.M.traits)

    -- find default methods for traits
    let default_methods :: Map TraitName [(MethName, MirHandle)]
        default_methods = foldr g Map.empty  (col^.M.traits) where
           g :: Trait -> Map TraitName [(MethName, MirHandle)] -> Map TraitName [(MethName, MirHandle)]
           g trait m = foldr g2 m (trait^.M.traitItems) where
               g2 (TraitMethod methName sig) m
                 | Just mh <- Map.lookup  methName hmap 
                 = Map.insertWith (++) (trait^.M.traitName) [(methName,mh)] m
               g2 _ m = m

    -- find all methods that are the implementations of traits at specific types
    -- this uses the name of the method and its type 
    let impls :: [(MethName, TraitName, MirHandle, Substs)]
        impls = [ (methName, traitName, methHandle, substs) 
                | (methName, methHandle) <- Map.assocs hmap
                , (TraitRef traitName substs, _tii)  <- getTraitImplementation col methName ]

    -- find the implementing methods for each type index (or default, if none is present)
    -- as well as the necessary substitutions
    let
        implsWithDefaults :: TraitName -> Map Int MethName -> ([Ty], [(MethName, MirHandle, Substs)]) -> [(MethName, MirHandle, Substs)]
        implsWithDefaults traitName revMap (typeName, implHandlesByType) = List.map getImpl (Map.elems revMap) where
          isImpl methName implName
            | Just methodEntry <- M.parseImplName implName
            = M.sameTraitMethod methodEntry methName
          isImpl _ _ = False

          getImpl methName
            -- there is a concrete implementation
            | Just (implName, implHandle, implSubst) <-
                  List.find (\(implName, _, _) -> isImpl methName implName) implHandlesByType 
            = (implName, implHandle, implSubst)

            -- there is a default implementation
            | Just ms <- Map.lookup traitName default_methods
            , Just (_, implHandle) <- List.find (\(mn,_) -> methName == mn) ms
            = (methName, implHandle, Substs [])

            -- can't find the implementation
            | otherwise
            = error $ "BUG: Cannot find implementation of method " ++ show (pretty methName)
                    ++ " in trait " ++ show (pretty traitName) ++ " for type " ++ show (pretty typeName)


    when (debug > 3) $ do
      if null impls
        then traceM "buildTraitMap: No trait implementations found"
        else forM_ impls $ \(mn, tn, mh, sub) -> do
          traceM $ "buildTraitMap: Implementing method of trait " ++ show tn ++ show (pretty sub)
          traceM $ "\t with " ++ show (pretty mh)
            

    -- TODO: use ctxr instead of subst for instantiation???
    let impl_vtable :: TraitDecl ctx                      
                    -> (C.CtxRepr implTys)                -- ^ implementation type for the trait
                    -> [(MethName, MirHandle, Substs)]    -- ^ impls for that type, must be in correct order
                    -> Ctx.Assignment GenericMirValue ctx
        impl_vtable (TraitDecl tname numParams methDecls ctxr methodIndex revIndex) implTy methImpls =
           let go :: Ctx.Index ctx ty -> C.TypeRepr ty -> Identity (GenericMirValue ty)
               go idx (C.FunctionHandleRepr args ret) = do
                  let i = Ctx.indexVal idx
                  when (i >= length methImpls) $ do
                      error $ "impl_vtable BUG: " ++ show i ++ " out of range for methImpls"
                  when (i >= length methDecls) $ do
                      error $ "impl_vtable BUG: " ++ show i ++ " out of range for methDecls"
                  let (declName, _declTy)                = methDecls !! i 
                  let (_implName, implHandle, implSubst) = methImpls !! i
                  error $ "TODO: finish this case"

               go idx (C.PolyFnRepr k args ret) = do
                  let i = Ctx.indexVal idx
                  when (i >= length methImpls) $ do
                      error $ "impl_vtable BUG: " ++ show i ++ " out of range for methImpls"
                  when (i >= length methDecls) $ do
                      error $ "impl_vtable BUG: " ++ show i ++ " out of range for methDecls"

                  let (declName, _declTy)                = methDecls !! i 
                  let (_implName, implHandle, implSubst) = methImpls !! i

                  substToSubstCont implSubst $ \subst -> 
                    case implHandle of 
                      (MirHandle mname sig (fh :: FH.FnHandle fargs fret)) -> do
                        let subst' = C.mkSubst subst
                        let k'     = minusP k (ctxSizeP subst)
                        case (testEquality (FH.handleArgTypes   fh) (C.instantiate subst' args),
                              testEquality (FH.handleReturnType fh) (C.instantiate subst' ret)) of
                            (Just Refl, Just Refl) ->
                              case peanoView k' of
                                 SRepr _ ->
                                   return (GenericMirValue $ 
                                      let expr   = R.App $ E.PolyHandleLit k' fh in
                                      let exprTy = C.PolyFnRepr k' (FH.handleArgTypes fh) (FH.handleReturnType fh) in
                                      (MirValue subst exprTy expr sig))
                                 ZRepr -> case (C.checkClosedCtx (FH.handleArgTypes fh),
                                                C.checkClosed (FH.handleReturnType fh)) of
                                   (Just C.Dict, Just C.Dict) ->
                                      return (GenericMirValue $
                                         let expr   = R.App $ E.HandleLit fh in
                                         let exprTy = C.FunctionHandleRepr (FH.handleArgTypes fh) (FH.handleReturnType fh) in
                                         (MirValue subst exprTy expr sig))
                                   (_,_) -> error $ "Function handle type not closed " ++ show fh
                            (_,_)   -> error $ "Type mismatch in method table for " ++ show tname
                                        ++ "\n\tadding implementation: " ++ show mname
                                        ++ "\n\tat implTy:"                  ++ show implTy
                                        ++ "\n\timplHandle type is: "        ++ show (FH.handleType fh)
                                        ++ "\n\tbut expected type is: "
                                           ++ show (C.FunctionHandleRepr (C.instantiate subst' args)
                                                                         (C.instantiate subst' ret))
                                        ++ "\n\targs before subst: " ++ show args
                                        ++ "\n\targs after subst: "  ++ show (C.instantiate subst' args)
                                        ++ "\n\tret before subst: " ++ show ret
                                        ++ "\n\tret after subst: "  ++ show (C.instantiate subst' ret)

                                        ++ "\n\tdeclared name is: " ++ show declName
                                        ++ "\n\tdeclared type is: "  ++ fmt (C.PolyFnRepr k args ret)
               go idx _ = error "buildTraitMap: can only handle trait definitions with polmorphic functions (no constants allowed)"
           in 
              runIdentity (Ctx.traverseWithIndex go ctxr)



    -- make the vtables for each implementation
    perTraitInfos <- forM (Map.assocs decls) $ \(traitName, Some decl@(TraitDecl _tname numParams _msigs ctx methodIndex revMap)) -> do

                     let implHandles = [ (methName, mirHandle, substs)
                                       | (methName, tn, mirHandle, substs) <- impls, traitName == tn]

                     vtables' <- forM (groupByType numParams implHandles) $ \pr@(tys, _) ->
                                   tyListToCtx (reverse tys) $ \ctxRepr -> do
                                        let vtable = impl_vtable decl ctxRepr (implsWithDefaults traitName revMap pr)
                                        return (Map.singleton tys vtable)

                     let vtables   = mconcat vtables'
                     let traitImpl = Some (mkGenericTraitImpls ctx methodIndex vtables)
 
                     return (traitName, traitImpl)

    let tm   = mkGenericTraitMap perTraitInfos
    let stm  = mkStaticTraitMap perTraitInfos

    return (tm, stm, [])


thisType :: HasCallStack => Int -> Substs -> [Ty]
thisType k (Substs tys)
  | length tys >= k   = take k tys
  | otherwise         = error $ "BUG: not enough types for implementation"

groupByType :: Int -> [(MethName, MirHandle, Substs)] -> [([Ty], [(MethName,MirHandle, Substs)])]
groupByType num meths =
  -- remove method implementations with no type instantiations
  let impls = filter (\(_,_,Substs s) -> not (null s)) meths in
  let impls' = map (\(methName, mh, substs) -> (thisType num substs, (methName,mh,substs))) impls
  in   
      -- convert double association list to double map
   Map.assocs $ foldr (\(ty,(mn,h,s)) -> Map.insertWith (++) ty [(mn,h,s)]) Map.empty impls'



-- Aux data structure for `mkTraitDecl`
data MethRepr ty where
  MethRepr :: MethName -> C.TypeRepr ty -> MethRepr ty
getReprName :: MethRepr ty -> MethName
getReprName (MethRepr name _) = name
getReprTy :: MethRepr ty -> C.TypeRepr ty
getReprTy (MethRepr _ ty) = ty





lookupMethodType :: Map TraitName (Some TraitDecl) -> TraitName -> MethName ->
    (forall ctx args ret. C.CtxRepr ctx -> C.CtxRepr args -> C.TypeRepr ret -> a) -> a
lookupMethodType traitDecls traitName implName k 
   | Just (Some (TraitDecl _tname _n _msig vreprs meths _revmap)) <- Map.lookup traitName traitDecls,
     Just (Some idx)                      <- Map.lookup implName  meths,
     C.FunctionHandleRepr (argsr Ctx.:> C.AnyRepr) retr <- (vreprs Ctx.! idx)
   = k vreprs argsr retr
   | otherwise = error "Internal error"
  

{-  Example of WRAPPING METHODS

    trait Foo {
       f (&self) -> u32     <-  wrapperName == "wrapped_f"
       g (&self) -> u32
    } 

    impl A {
       fn f (&self) { 3 }    <- implName == "f"
       fn g (&self) { 4 }
    }

    ==>

    f (x : A) { 3 }

    wrapped_f (Any x) -> u32 = 
       unPack x as (  y :: A ,  { f :: A -> u32,  g :: A -> u 32 } )
       f y

    wrapped_g (Any x) -> u32 = 
       unPack x as (  y :: A ,  { wrapped_f :: Dyn -> u32,  wrapped_g :: A -> u 32 } )
       g y

-}

{-
data WrappedMethod ty = 
    WrappedMethod { wmImplName      :: MethName
                  , wmImplHandle    :: MirHandle
                  , wmWrappedName   :: Text
                  , wmWrappedHandle :: MirValue ty
                  }
buildWrappedTraitMethods :: forall s ctx. HasCallStack => FH.HandleAllocator s
                        -> TraitName
                        -> TraitDecl ctx                 
                        -> [(MethName, MirHandle)]       -- impls for that type, must be in correct order
                        -> ST s (Ctx.Assignment MirValue ctx, [(Text,Core.AnyCFG MIR)])
buildWrappedTraitMethods halloc traitName (TraitDecl ctxr _idxs) meths = undefined
-}
 {-
   -- allocate new function handles for the trait with the generic type
   let go :: forall ty. Ctx.Index ctx ty -> C.TypeRepr ty -> ST s (WrappedMethod ty)
       go idx (C.PolyFnRepr (argsr :: C.CtxRepr args) (retr :: C.TypeRepr ret)) = do
          let argsr' :: C.CtxRepr (C.Instantiate (Ctx.EmptyCtx Ctx.::> C.AnyType) args)
              argsr' = C.instantiate (Empty :> C.AnyRepr) argsr
          let retr'  = C.instantiate (Empty :> C.AnyRepr) retr
          let i = Ctx.indexVal idx
          let (implName, implHandle) = if i < length meths then meths !! i else error "buildWrappedTraitMethods"
          let wrappedName = Text.pack "wrapped" <> (M.idText traitName) <> "::" <> M.idText implName
                                 
          nhandle <- FH.mkHandle' @s @(C.Instantiate (Ctx.EmptyCtx Ctx.::> C.AnyType) args)
                                     @(C.Instantiate (Ctx.EmptyCtx Ctx.::> C.AnyType) ret) 
                        halloc (FN.functionNameFromText wrappedName) argsr' retr'
          let fnValue :: MirValue (C.PolyFnType args ret)
              fnValue = FnValue @C.AnyType @args @ret C.AnyRepr nhandle
          return $ WrappedMethod implName implHandle wrappedName fnValue
       go _ _ = error "No MirValue for non-(polymorphic)-functions"

   full_vtable <- Ctx.traverseWithIndex go ctxr

   -- bind functions to go with those handles
   let defineCFG :: forall ty. WrappedMethod ty -> ST s (Text,Core.AnyCFG MIR)
       defineCFG (WrappedMethod implName   (MirHandle _ _sig (implHandle :: FH.FnHandle implArgs implRet))
                                wrappedName (FnValue (handle :: FH.FnHandle args ret))) = do

         -- traceM ("\n wrapping " ++ Text.unpack implName ++ show (FH.handleArgTypes implHandle))
         let argsr = FH.handleArgTypes   handle
         let retr  = FH.handleReturnType handle
         -- make sure that there is at least one argument to the function
         -- and that the wrapped function is almost the same type as the impl function
         case (FH.handleArgTypes implHandle :: C.CtxRepr implArgs) of
           Ctx.Empty -> error "methods must take self"
           (rest Ctx.:> argr) -> case testEquality (C.FunctionHandleRepr (rest Ctx.:> C.AnyRepr) (FH.handleReturnType implHandle))
                                                   (C.FunctionHandleRepr argsr retr) of
              Nothing   -> error $ "types don't match for:" ++ show implName
                                 ++ "\ncomparing:  " ++ show (C.FunctionHandleRepr (rest Ctx.:> C.AnyRepr) (FH.handleReturnType implHandle))
                                 ++ " with "  ++ show (C.FunctionHandleRepr argsr retr)
              Just Refl -> do

                 -- type of trait implementation
                   let objTyRepr = C.StructRepr (Ctx.Empty Ctx.:> C.AnyRepr Ctx.:> C.StructRepr ctxr)

                   let fnDef :: G.FunctionDef MIR h FnState args ret
                       fnDef (xs Ctx.:> x) = (res, body) where
                          res  = FnState Map.empty Map.empty Map.empty Map.empty (TraitMap Map.empty) Map.empty   -- CHECK THIS
                          body =
                            let yo = R.App $ E.FromJustValue objTyRepr (R.App (E.UnpackAny objTyRepr (R.AtomExpr x)))
                                            (R.App (E.TextLit (Text.pack ("bad wrapper :" <> (show objTyRepr)))))
                                y1  = R.App $ E.GetStruct yo Ctx.i1of2 C.AnyRepr
                                y2 = R.App $ E.FromJustValue argr (R.App (E.UnpackAny argr y1))
                                            (R.App (E.TextLit (Text.pack ("bad wrapper2 :" <> show argr))))
                                ys = Ctx.fmapFC R.AtomExpr xs
                            in G.call (R.App $ E.HandleLit implHandle) (ys Ctx.:> y2)
                       fnDef _ = error "impossible"

                   (R.SomeCFG cfg, _ignore) <- G.defineFunction PL.InternalPos handle fnDef
                   case SSA.toSSA cfg of
                     (Core.SomeCFG cfg') -> return (wrappedName, Core.AnyCFG cfg')

   let mkCFGs = Ctx.toListFC defineCFG full_vtable
   cfgs <- sequence mkCFGs

   return (Ctx.fmapFC wmWrappedHandle full_vtable, cfgs)
-}
   

{-
-- | Construct 'TraitImpls' for each trait. Involves finding data
-- types that implement a given trait and functions that implement
-- each method for a data type and building VTables for each
-- data-type/trait pair.
mkTraitImplementations ::
         M.Collection
      -> [(MethName, TraitName, Ty, MirHandle)]
      -> M.Trait
      -> Some TraitImpls
mkTraitImplementations _col trs trait@(M.Trait tname titems) =
  let impls :: Map Ty (Map MethName MirHandle)
      impls = thisTraitImpls trait trs

      meths = [(tname, tsig) |(M.TraitMethod tname tsig) <- titems]
  in
{-  trace ("Storing traits for " ++ show tname
           ++ "\nimpls is: " ++ show impls
           ++ "\ntrs is: " ++ show trs 
           ++ "\nTrait meths are: " ++ show meths) $ -}
  case foldl go (Some Ctx.empty) meths of

    Some (mctxr :: Ctx.Assignment MethRepr ctx) ->
        let
            ctxr    :: Ctx.Assignment C.TypeRepr ctx
            ctxr    = Ctx.fmapFC getReprTy mctxr
            --
            midx    :: Map MethName (Some (Ctx.Index ctx))
            midx    = Ctx.forIndex
                          (Ctx.size mctxr)
                          (\mp idx -> Map.insert (getReprName (mctxr Ctx.! idx)) (Some idx) mp)
                          Map.empty

            -- replace the (Map MethName MirHandle) with a
            -- an assignment from the method name to the appropriate function value
            vtables :: Map Ty (Ctx.Assignment MirValue ctx)
            vtables = Map.mapWithKey 
                        (\ ty (mmap :: Map MethName MirHandle) ->
                           Ctx.generate (Ctx.size mctxr)
                                        (\idx ->
                                            let (MethRepr name cty) = mctxr Ctx.! idx in
                                            case Map.lookup name mmap of
                                                    Just (MirHandle _ _ fh) -> case testEquality cty (FH.handleType fh) of
                                                        Just Refl -> FnValue fh 
                                                        Nothing   -> error $ "type mismatch between trait declr " ++ show (pretty cty)
                                                                   ++  " and instance type " ++ show (pretty (FH.handleType fh))
                                                    Nothing -> error $ "Cannot find method " ++ show name ++ " for type " ++ show ty
                                                                       ++ " in trait " ++ show tname)) impls
        in Some (TraitImpls ctxr midx vtables) 

  where 
        go :: Some (Ctx.Assignment MethRepr) -> (MethName, M.FnSig) -> Some (Ctx.Assignment MethRepr)
        go (Some tr) (mname, M.FnSig argtys retty) =
          case (tyToRepr retty, tyListToCtx argtys Some) of
                (Some retrepr, Some argsrepr) ->
                   Some (tr `Ctx.extend` MethRepr mname (C.FunctionHandleRepr argsrepr retrepr))


-}



 
-- | Find the mapping from types to method handles for *this* trait
thisTraitImpls :: M.Trait -> [(MethName,TraitName,Ty,MirHandle)] -> Map Ty (Map MethName MirHandle)
thisTraitImpls trait trs = do
  -- pull out method handles just for this trait
  let impls = [ (typeName, (methName, handle)) |
         (methName, traitName, typeName, handle) <- trs, traitName == trait^.M.traitName ]
  -- convert double association list to double map
  foldr (\(ty,(mn,h)) -> Map.insertWith Map.union ty (Map.singleton mn h)) Map.empty impls



--------------------------------------------------------------------------------------------------------------------------
-- * Data structure manipulation for implementing primitives

-- ** options

-- statically-typed option creation

mkSome' :: C.TypeRepr tp -> G.Expr MIR s tp -> G.Expr MIR s TaggedUnion
mkSome' ty val =
   let tty  = C.StructRepr (Ctx.empty Ctx.:> ty) in
   let tval = G.App $ E.MkStruct (Ctx.empty Ctx.:> ty) (Ctx.empty Ctx.:> val) in
   G.App $ E.MkStruct (Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr) 
                      (Ctx.empty Ctx.:> (S.app $ E.NatLit 1) Ctx.:> (S.app $ E.PackAny tty tval))

mkNone' :: G.Expr MIR s TaggedUnion
mkNone'=
  let ty  = C.StructRepr Ctx.empty in
  let val = S.app $ E.MkStruct Ctx.empty Ctx.empty in
  G.App $ E.MkStruct (Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr) 
                     (Ctx.empty Ctx.:> (S.app $ E.NatLit 0) Ctx.:> (S.app $ E.PackAny ty val))

-- dynamically-typed option

mkNone :: MirExp s
mkNone =
    buildTuple [MirExp C.NatRepr (S.app $ E.NatLit 0), packAny $ buildTuple []]

mkSome :: MirExp s -> MirExp s
mkSome a = buildTuple [MirExp C.NatRepr (S.app $ E.NatLit 1), packAny $ buildTuple [a]]

-- ** range

rangeStart :: C.TypeRepr ty -> R.Expr MIR s TaggedUnion -> MirGenerator h s ret (R.Expr MIR s ty)
rangeStart itemRepr r = do
   (MirExp C.AnyRepr tup) <- accessAggregate (MirExp taggedUnionRepr r) 1
   let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
   let strTy = C.StructRepr ctx
   let unp   = S.app $ E.FromJustValue strTy (S.app $ E.UnpackAny strTy tup)
                                     (fromString ("Bad Any unpack iter_next:" ++ show strTy))
   let start = S.getStruct Ctx.i1of2 unp
   return start

rangeEnd :: C.TypeRepr ty -> R.Expr MIR s TaggedUnion -> MirGenerator h s ret (R.Expr MIR s ty)
rangeEnd itemRepr r = do
   (MirExp C.AnyRepr tup) <- accessAggregate (MirExp taggedUnionRepr r) 1
   let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
   let strTy = C.StructRepr ctx
   let unp   = S.app $ E.FromJustValue strTy (S.app $ E.UnpackAny strTy tup)
                                     (fromString ("Bad Any unpack iter_next:" ++ show strTy))
   let end   = S.getStruct Ctx.i2of2 unp
   return end

mkRange :: C.TypeRepr ty -> R.Expr MIR s ty -> R.Expr MIR s ty -> R.Expr MIR s TaggedUnion
mkRange itemRepr start end = 
   let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
       strTy = C.StructRepr ctx
       y     = S.app $ E.PackAny strTy (S.app $ E.MkStruct ctx (Ctx.empty `Ctx.extend` start `Ctx.extend` end))
       j     = S.app $ E.MkStruct taggedUnionCtx (Ctx.empty `Ctx.extend` (S.litExpr 0) `Ctx.extend` y)
   in  j


--------------------------------------------------------------------------------------------------------------------------
-- *  Primitives & other custom stuff

-- Operation for a custom operation (that returns normally)
type ExplodedDefId = ([Text], Text, [Text])
data CustomOp      =
    CustomOp (forall h s ret. HasCallStack =>
      [M.Ty] -> M.Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s))
  | CustomMirOp (forall h s ret. HasCallStack =>
      [M.Operand] -> MirGenerator h s ret (MirExp s))
  | CustomOpExit            

type CustomRHS = Substs -> Maybe CustomOp

customOps :: Map ExplodedDefId CustomRHS
customOps = Map.fromList [
                           fn_call
                         , fn_call_once

                         , slice_get_unchecked_mut
                         , slice_len
                         , slice_get_mut
              
                         , ops_index
                         , ops_index_mut

                         , into_iter
                         , iter_next
                         , iter_map
                         , iter_collect

                         , wrapping_sub

                         , exit
                         ]

-- Can use the (static) type arguments to decide whether to override
memberCustomFunc :: M.DefId -> M.Substs -> Bool
memberCustomFunc defid substs =
  let edid = (map fst (M.did_path defid), fst (M.did_name defid), map fst (M.did_extra defid)) in
  case Map.lookup edid customOps of
    Just f  -> isJust (f substs)
    Nothing -> False

lookupCustomFunc :: M.DefId -> M.Substs -> Maybe CustomOp
lookupCustomFunc defid substs = 
  let edid = (map fst (M.did_path defid), fst (M.did_name defid), map fst (M.did_extra defid)) in
  case (Map.lookup edid customOps) of
    Just f -> f substs
    Nothing -> Nothing

 


-- if we want to be able to insert custom information just before runtime, the below can be dynamic, and baked into the Override monad.

customtyToRepr :: M.CustomTy -> Some C.TypeRepr
customtyToRepr (M.BoxTy t) = tyToRepr t -- Box<T> is the same as T
customtyToRepr (M.IterTy t) = tyToRepr $ M.TyTuple [M.TySlice t, M.TyUint M.USize]
-- Implement C-style enums as single integers
customtyToRepr (CEnum _adt _i) = Some C.IntegerRepr
customtyToRepr ty = error ("FIXME: unimplemented custom type: " ++ show (pretty ty))

-- Function names that are handled  by doCustomCall below
{-
isCustomFunc :: M.DefId -> Maybe Text
isCustomFunc defid = case (map fst (M.did_path defid), fst (M.did_name defid), map fst (M.did_extra defid)) of
     
--   (["ops", "index"], "Index",    ["index"])     -> Just "index"
--   (["ops", "index"], "IndexMut", ["index_mut"]) -> Just "index_mut"

--   (["ops","function"], "Fn",     ["call"])      -> Just "call"
--   (["ops","function"], "FnOnce", ["call_once"]) -> Just "call"

--   (["process"], "exit", []) -> Just "exit"

--   (["vec", "{{impl}}"], "with_capacity",[])     -> Just "vec_with_capacity"
--   (["vec", "{{impl}}"], "vec_asmutslice",[])    -> Just "vec_asmutslice"
--   (["vec"],             "from_elem",     [])    -> Just "vec_fromelem"

--   (["boxed","{{impl}}"], "new", [])             -> Just "new"

--   (["slice","{{impl}}"], "slice_tovec", [])      -> Just "slice_tovec"
   (["slice","{{impl}}"], "len", [])              -> Just "slice_len"
   (["slice"],"SliceIndex", ["get_unchecked"])    -> Just "slice_get_unchecked"
   (["slice"],"SliceIndex", ["get_unchecked_mut"]) -> Just "slice_get_unchecked_mut"

--   (["iter","traits"], "IntoIterator", ["into_iter"]) -> Just "into_iter"
--   (["iter","iterator"],"Iterator", ["next"])         -> Just "iter_next"
--   (["iter","iterator"],"Iterator", ["map"])          -> Just "iter_map"
--   (["iter","iterator"],"Iterator", ["collect"])      -> Just "iter_collect"

--   (["num","{{impl}}"], "wrapping_sub", [])       -> Just "wrapping_sub"

   _ -> Nothing
-}

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: Exit

exit :: (ExplodedDefId, CustomRHS)
exit = ((["process"], "exit", []), \s -> Just CustomOpExit)

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: Index

ops_index :: (ExplodedDefId, CustomRHS)
ops_index = ((["ops", "index"], "Index", ["index"]), index_op )

ops_index_mut :: (ExplodedDefId, CustomRHS)
ops_index_mut = ((["ops", "index"], "IndexMut", ["index_mut"]), index_op )


index_op :: Substs -> Maybe CustomOp
index_op substs = Just $ CustomMirOp $ \ ops ->
             case ops of
               [op1, op2] -> do
                  let v2 = M.varOfLvalue (M.lValueofOp op2)
                  evalLvalue (M.LProjection (M.LvalueProjection (M.lValueofOp op1) (M.Index v2)))
               _ -> fail $ "BUG: invalid arguments to index"

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: wrapping_sub

wrapping_sub :: (ExplodedDefId, CustomRHS)
wrapping_sub = ( (["num","{{impl}}"], "wrapping_sub", []),
   \ _substs -> Just $ CustomOp $ \ _opTys _retTy ops ->
     case ops of 
       [MirExp aty a, MirExp bty b] ->
         -- return (a - b) mod 2N  (this is the default behavior for BVSub)
         case (aty, bty) of
           (C.BVRepr wa, C.BVRepr wb) | Just Refl <- testEquality wa wb -> do
               let sub = R.App $ E.BVSub wa a b 
               return (MirExp aty sub)
           (_,_) -> fail $ "wrapping_sub: cannot call with types " ++ show aty ++ " and " ++ show bty

       _ -> fail $ "BUG: invalid arguments for wrapping_sub")

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: Iterator


into_iter :: (ExplodedDefId, CustomRHS)
into_iter = ((["iter","traits"], "IntoIterator", ["into_iter"]),
    \ (Substs subs) -> Just $ CustomOp $ \ _opTys _retTy ops ->
     case (subs, ops) of 
       ([ty], [arg]) -> do
         case ty of
           TyAdt defid (Substs [itemTy]) | defid == M.textId "::ops[0]::range[0]::Range[0]" -> 
             -- an identity function
             -- the range type just uses the default implementation of this trait
             return arg
{-           TyAdt defid (Substs [_,itemTy]) | defid == M.textId "::slice[0]::Iter[0]" -> do
             traceM $ "Found slice Iter"
             let x = buildTuple [arg, MirExp (C.NatRepr) (S.app $ E.NatLit 0)]
             let y = buildTuple [MirExp C.NatRepr (S.app $ E.NatLit 0), packAny x]
             return y -}
           _ -> do
             -- vector iterator: a pair of the vector and the index
             --traceM $ "Found " ++ show ty
             let x = buildTuple [arg, MirExp (C.NatRepr) (S.app $ E.NatLit 0)]
             let y = buildTuple [MirExp C.NatRepr (S.app $ E.NatLit 0), packAny x]
             return y
             
       _ -> fail $ "BUG: invalid arguments for into_iter")

iter_next :: (ExplodedDefId, CustomRHS)
iter_next = ((["iter","iterator"],"Iterator", ["next"]), iter_next_op) where
  iter_next_op (Substs [TyAdt defid (Substs [itemTy])])
    | defid == M.textId "::ops[0]::range[0]::Range[0]"  = Just (CustomOp (iter_next_op_range itemTy))
  iter_next_op (Substs [TyAdt defid (Substs [_,itemTy])])
    | defid == M.textId "::slice[0]::Iter[0]" = Just (CustomOp (iter_next_op_array itemTy))
  iter_next_op (Substs [TyArray itemTy _len]) = Just (CustomOp (iter_next_op_array itemTy))
  iter_next_op _ = Nothing


iter_next_op_range :: forall h s ret. HasCallStack => M.Ty -> [M.Ty] -> M.Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_next_op_range itemTy _opTys _retTy ops =
    case ops of 
       [ MirExp (MirReferenceRepr tr) ii ]
         | Just Refl <- testEquality tr taggedUnionRepr
         -> do
             -- iterator is a struct of a "start" and "end" value of type 'itemTy'
             -- to increment the iterator, make sure the start < end and then
             tyToReprCont itemTy $ \itemRepr -> do

                r <- readMirRef tr ii
                start <- rangeStart itemRepr r
                end   <- rangeEnd   itemRepr r

                plus_one <- incrExp itemRepr start
                let good_ret = mkSome' itemRepr start
                let bad_ret  = mkNone'
                let  updateRange :: MirGenerator h s ret ()
                     updateRange = writeMirRef ii (mkRange itemRepr plus_one end)

                (MirExp C.BoolRepr boundsCheck)
                     <- evalBinOp M.Lt (arithType itemTy) (MirExp itemRepr start)
                                                          (MirExp itemRepr end)
                ret <- G.ifte boundsCheck
                           (updateRange >> return good_ret)
                           (return bad_ret)
                return (MirExp taggedUnionRepr ret)
       _ -> fail $ "BUG: invalid arguments for iter_next"


iter_next_op_array :: forall h s ret. HasCallStack => M.Ty -> [M.Ty] -> M.Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_next_op_array itemTy _opTys retTy ops = 
    -- iterator is a struct containing (vec, pos of nat)
    -- if pos < size of vec, return (Some(vec[pos]), (vec, pos+1)).
    -- otherwise return (None, (vec, pos))
  case ops of
    [iter] -> do
      (MirExp (C.VectorRepr elemTy) iter_vec) <- accessAggregate iter 0
      (MirExp C.NatRepr iter_pos) <- accessAggregate iter 1
      let is_good    = S.app $ E.NatLt iter_pos (S.app $ E.VectorSize iter_vec)
          ret_1_ty   = taggedUnionRepr
          ret_2_ctx  = Ctx.empty Ctx.:> (C.VectorRepr elemTy) Ctx.:> C.NatRepr
          ret_2_ty   = C.StructRepr ret_2_ctx
          ty_ctx     = (Ctx.empty Ctx.:> ret_1_ty Ctx.:> ret_2_ty)
          ty         = C.StructRepr ty_ctx

          mk_ret opt vec pos = G.App (E.MkStruct ty_ctx (Ctx.empty Ctx.:> opt Ctx.:> ret_2)) where
             ret_2 = G.App (E.MkStruct ret_2_ctx (Ctx.empty Ctx.:> vec Ctx.:> pos))

          good_ret_1 = mkSome' elemTy (S.app $ E.VectorGetEntry elemTy iter_vec iter_pos)

          good_ret   = mk_ret good_ret_1 iter_vec (S.app $ E.NatAdd iter_pos (S.app $ E.NatLit 1))
          bad_ret    = mk_ret mkNone'    iter_vec iter_pos

      ret <- withRepr ty $ G.ifte is_good
              (return good_ret)
              (return bad_ret)
      return $ MirExp ty ret
    _ -> fail $ "BUG: invalid args to iter_next_op_array"


-- SCW: not sure if this one is up-to-date
iter_map :: (ExplodedDefId, CustomRHS)
iter_map = ((["iter","iterator"],"Iterator", ["map"]), \subst -> Just $ CustomOp $ iter_map_op subst)

iter_map_op :: forall h s ret. HasCallStack => Substs -> [M.Ty] -> M.Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_map_op _subst opTys _retTy ops =
  case (opTys, ops) of
   ([ iter_ty , closure_ty ], [ iter_e  , closure_e ]) ->
      performMap iter_ty iter_e closure_ty closure_e
   _ -> fail $ "BUG: invalid arguments to iter_map"

iter_collect :: (ExplodedDefId, CustomRHS)
iter_collect = ((["iter","iterator"],"Iterator", ["collect"]), \subst -> Just $ CustomOp $ iter_collect_op subst)

iter_collect_op ::  forall h s ret. HasCallStack => Substs -> [M.Ty] -> M.Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_collect_op _subst _opTys _retTy ops =
   case ops of
     [ iter ] -> accessAggregate iter 0
     _ -> fail $ "BUG: invalid arguments to iter_collect"


--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: slice




slice_len :: (ExplodedDefId, CustomRHS)
slice_len =
  ((["slice","{{impl}}"], "len", [])
  , \(Substs [_]) -> Just $ CustomOp $ \ _optys _retTy ops -> 
     case ops of 
     -- type of the structure is &mut[ elTy ]
       [MirExp (C.VectorRepr _) vec_e] -> do
            return (MirExp C.NatRepr  (G.App $ E.VectorSize vec_e))
       _ -> fail $ "BUG: invalid arguments to " ++ "slice_len")


-- Only works when the sequence is accessed by a range
slice_get_mut :: (ExplodedDefId, CustomRHS)
slice_get_mut =
  ((["slice", "{{impl}}"],"get_mut", [])
  , \subs -> case subs of
               (Substs [elTy, TyAdt defid (Substs [M.TyUint M.USize])])
                 | defid == M.textId "::ops[0]::range[0]::Range[0]"
                 -> Just $ CustomOp $ \ optys retTy ops -> do
                    case ops of
                      [MirExp (C.VectorRepr ety) vec_e, MirExp tr range_e ]
                        | Just Refl <- testEquality tr taggedUnionRepr -> do
                         start <- rangeStart C.NatRepr range_e
                         stop  <- rangeEnd   C.NatRepr range_e 
                         v <- vectorCopy ety start stop vec_e
                         return $ mkSome (MirExp (C.VectorRepr ety) v)

                      [MirExp (MirSliceRepr ty) vec_e, MirExp tr range_e] 
                        | Just Refl <- testEquality tr taggedUnionRepr -> do
                         start <- rangeStart C.NatRepr range_e
                         stop  <- rangeEnd   C.NatRepr range_e 
                         let newLen = (S.app $ E.NatSub stop start)
                         let s1 = updateSliceLB  ty vec_e start
                         let s2 = updateSliceLen ty s1    newLen
                         return $ mkSome (MirExp (MirSliceRepr ty) s2)

                      _ -> fail $ "BUG: invalid arguments to slice_get_mut:" ++ show ops
               (Substs _) -> Nothing)

slice_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_get_unchecked_mut =
  ((["slice"],"SliceIndex", ["get_unchecked_mut"])
  , \(Substs _subs) -> Just $ CustomOp $ \ optys _retTy ops -> do
      case ops of
        [self, MirExp (MirSliceRepr ty) slice] -> do
           idx <- generateIndex self
           let ref  = S.getStruct Ctx.i1of3 slice
           let base = getSliceLB slice
           v <- subindexRef ty ref (S.app (E.NatAdd idx base))
           return (MirExp (MirReferenceRepr ty) v)
        _ -> fail $ "BUG: invalid arguments to " ++ "slice_get_unchecked_mut")

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: vec

-- A vector is an array tupled with a length, as an Adt
-- 

{-
vec_with_capacity :: (ExplodedDefId, CustomRHS)
vec_with_capacity =
  ((["vec"],"Vec", "with_capacity"),
  \subst -> Just $ CustomOp $ \optys _retTy ops -> do
     case ops of
       [ MirExp C.NatRepr capacity ] -> 
-}     



--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: call

fn_call :: (ExplodedDefId, CustomRHS)
fn_call = ((["ops","function"], "Fn", ["call"]), \subst -> Just $ CustomOp $ fn_call_op subst)

fn_call_once :: (ExplodedDefId, CustomRHS)
fn_call_once = ((["ops","function"], "FnOnce", ["call_once"]), \subst -> Just $ CustomOp $ fn_call_op subst)

fn_call_op ::  forall h s ret. HasCallStack => Substs -> [M.Ty] -> M.Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s)
fn_call_op (Substs [_ty1, aty, _rp]) [argTy1,_] retTy [fn,argtuple] = do
     extra_args   <- getAllFieldsMaybe argtuple

     -- returns the function (perhaps with a coerced type, in the case of polymorphism)
     -- paired with it unpacked as a closure
     let unpackClosure :: M.Ty -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s, MirExp s)

         unpackClosure (M.TyRef ty M.Immut) rty  arg   = unpackClosure ty rty arg

         unpackClosure (M.TyClosure defid clargs) _rty arg = do
             (clty, _rty2) <- buildClosureType defid clargs
             (arg,) <$> unpackAny clty arg

         unpackClosure (M.TyDynamic _id)    rty  arg   = do
             -- a Fn object looks like a pair of
             -- a function that takes any "Any" arguments (the closure) and a struct
             --      of the actual arguments (from the funsubst) and returns type rty
             -- and an environment of type "Any

             tyToReprCont rty $ \rr ->
               case aty of
                  (TyTuple aas) -> tyListToCtx aas $ \r2 -> do
                     let args = (Ctx.empty Ctx.:> C.AnyRepr)  Ctx.<++> r2
                     let t = Ctx.empty Ctx.:> C.FunctionHandleRepr args rr Ctx.:> C.AnyRepr
                     (arg,) <$> unpackAny (Some (C.StructRepr t)) arg
                  _ -> fail $ "aty must be tuple type in dynamic call, found " ++ show (pretty aty)

         unpackClosure (M.TyParam i) rty arg = do
           -- TODO: this is a really hacky implementation of higher-order function calls
           -- we should replace it with additional arguments being passed in for the constraints
           -- Here, instead we assume that the type that is instantiating the type variable i is
           -- some closure type. We then look at the constraint to see what type of closure type it
           -- could be and then instantiate that type variable with "Any" 
           -- If we are wrong, we'll get a segmentation fault(!!!)
           -- (This means we have some unsafe instantiation code around, e.g. for Nonces,
           -- so we should get rid of that too!)
           ps <- use preds
--           traceM $ "unpackClosure: called with "
--                  ++ "\n\t param " ++ fmt i
--                  ++ "\n\t rty   " ++ fmt rty
--                  ++ "\n\t preds " ++ fmt ps
           let findFnType (TraitProjection defid (Substs ([M.TyParam j, M.TyTuple argTys])) retTy : rest)
                 | i == j     = 
                  tyListToCtx argTys $ \argsctx -> 
                  tyToReprCont retTy $ \ret     ->
                     (Some argsctx, Some ret)

                 | otherwise  =  findFnType rest
               findFnType (_ : rest) = findFnType rest
               findFnType [] = error $ "no appropriate predicate in scope for call: " ++ show (pretty ps)

           case (arg, findFnType ps) of 
             (MirExp _ty cp,
              (Some (argsctx :: C.CtxRepr args), Some (rr :: C.TypeRepr r))) -> do
                let cp'  :: R.Expr MIR s C.AnyType
                    cp'  = unsafeCoerce cp
                let args = (Ctx.empty Ctx.:> C.AnyRepr)  Ctx.<++> argsctx
                let t = Ctx.empty Ctx.:> C.FunctionHandleRepr args rr Ctx.:> C.AnyRepr
                let arg' = MirExp C.AnyRepr cp'
                (arg',) <$> unpackAny (Some (C.StructRepr t)) arg'


         unpackClosure ty _ _arg      =
           fail $ "Don't know how to unpack Fn::call arg of type " ++ show (pretty ty)

     (fn', unpack_closure) <- unpackClosure argTy1 retTy fn
     handle <- accessAggregate unpack_closure 0
     extra_args <- getAllFieldsMaybe argtuple
     case handle of
       MirExp hand_ty handl ->
           case hand_ty of
             C.FunctionHandleRepr fargctx fretrepr -> do
                exp_to_assgn (fn' : extra_args) $ \ctx asgn ->
                   case (testEquality ctx fargctx) of
                     Just Refl -> do
                       ret_e <- G.call handl asgn
                       return (MirExp fretrepr ret_e)
                     Nothing ->
                       fail $ "type mismatch in Fn::call, expected " ++ show ctx ++ "\n received " ++ show fargctx
             _ -> fail $ "bad handle type"

fn_call_op ss args ret _exps = fail $ "\n\tBUG: invalid arguments to call/call_once:"
                                    ++ "\n\t ss   = " ++ fmt ss
                                    ++ "\n\t args = " ++ fmt args
                                    ++ "\n\t ret  = " ++ fmt ret

--------------------------------------------------------------------------------------------------------------------------



--
-- Generate a loop that copies a vector 
vectorCopy :: C.TypeRepr elt ->
             G.Expr MIR s C.NatType ->
             G.Expr MIR s C.NatType ->
             G.Expr MIR s (C.VectorType elt) ->
             MirGenerator h s ret (G.Expr MIR s (C.VectorType elt))
vectorCopy ety start stop inp = do
  let elt = S.app $ E.VectorGetEntry ety inp (S.app $ E.NatLit 0)
  let sz  = S.app $ E.NatSub stop start
  let out = S.app $ E.VectorReplicate ety sz elt
  ir <- G.newRef start
  or <- G.newRef out
  let pos = PL.InternalPos
  G.while (pos, do i <- G.readRef ir
                   return (G.App (E.NatLt i stop)))
          (pos, do i <- G.readRef ir
                   let elt = S.app $ E.VectorGetEntry ety inp i
                   o   <- G.readRef or
                   let o' = S.app $ E.VectorSetEntry ety o i elt
                   G.writeRef or o'
                   G.writeRef ir (G.App (E.NatAdd i (G.App $ E.NatLit 1))))
  o <- G.readRef or
  return o


-- Type-indexed version of "1"
oneExp :: C.TypeRepr ty -> MirExp s
oneExp C.NatRepr    = MirExp C.NatRepr (S.litExpr 1)
oneExp (C.BVRepr w) = MirExp (C.BVRepr w) (R.App (E.BVLit w 1))
oneExp ty = error $ "oneExp: unimplemented for type " ++ show ty

-- Add one to an expression
incrExp :: C.TypeRepr ty -> R.Expr MIR s ty -> MirGenerator h s ret (R.Expr MIR s ty)
incrExp ty e = do res <- evalBinOp M.Add Nothing (MirExp ty e) (oneExp ty)
                  case res of 
                    (MirExp ty' e') | Just Refl <- testEquality ty ty'
                                    -> return e'
                    _ -> error "BUG: incrExp should return same type"




extractVecTy :: forall a t. C.TypeRepr t -> (forall t2. C.TypeRepr t2 -> a) -> a
extractVecTy (C.VectorRepr a) f = f a
extractVecTy _ _ = error "Expected vector type in extraction"


-- Coerce an expression to be appropriate as an array index
generateIndex :: MirExp s -> MirGenerator h s ret (R.Expr MIR s C.NatType)
generateIndex (MirExp C.NatRepr e) = return e
generateIndex (MirExp ty _) = error $ "Don't know how to create an index from an " ++ show ty







{-
doCustomCall :: forall h s ret a. HasCallStack => M.DefId -> Substs -> [M.Operand] -> M.Lvalue -> M.BasicBlockInfo -> MirGenerator h s ret a
doCustomCall fname funsubst ops lv dest
{-  | Just "slice_get_unchecked" <- isCustomFunc fname
  ,  [op1, op2] <- ops
  ,  Substs subs <- funsubst = do
       self  <- evalOperand op1
       sl <- evalOperand op2

       error $ "slice get_unchecked unimplemented " ++ show (pretty subs) -}
{-
  | Just "slice_get_unchecked_mut" <- isCustomFunc fname
  ,  [op1, op2] <- ops
  ,  Substs subs <- funsubst = do
       self  <- evalOperand op1
       sl <- evalOperand op2
       case sl of
         (MirExp (MirSliceRepr ty) slice) -> do
           idx <- generateIndex self
           let ref  = S.getStruct Ctx.i1of3 slice
           let base = getSliceLB slice
           v <- subindexRef ty ref (S.app (E.NatAdd idx base))

           -- vec <- readMirRef (C.VectorRepr ty) ref
           -- let v = S.app $ E.VectorGetEntry ty vec 
           assignLvExp lv (MirExp (MirReferenceRepr ty) v)
           jumpToBlock dest

         _ -> error $ "slice get_unchecked_mut unimplemented " ++ show (pretty (typeOf op1)) ++ " and " ++ show (pretty (typeOf op2))
-}

{- | Just "slice_get" <-  isCustomFunc fname,
   [vec,range] <- ops,
   Substs [ty1, ty2] <- funsubst = do
     vec_e <- evalOperand vec
     range_e <- evalOperand range
     let v = error "slice_get: unimplemented"
     assignLvExp lv v
     jumpToBlock dest -}
{-
 | Just "slice_get_mut" <-  isCustomFunc fname,
   [vec, range] <- ops,
   Substs [elTy, idxTy] <- funsubst = do

     -- type of the structure is &mut[ elTy ]
     (MirExp vty vec_e) <- evalOperand vec
     case vty of
       C.VectorRepr ety -> do
         range_e <- evalOperand range
         (MirExp C.NatRepr start) <- accessAggregate range_e 0
         (MirExp C.NatRepr stop ) <- accessAggregate range_e 1
         v <- vectorCopy ety start stop vec_e
         assignLvExp lv (MirExp (C.VectorRepr ety) v)
         jumpToBlock dest
       _ -> fail $ " slice_get_mut type is " ++ show vty ++ " from " ++ show (M.typeOf vec)
-}


  | Just "boxnew" <- isCustomFunc fname,
  [op] <- ops =  do
        e <- evalOperand op
        assignLvExp lv e
        jumpToBlock dest

  | Just "slice_tovec" <- isCustomFunc fname,
  [op] <- ops = do
        e <- evalOperand op
        assignLvExp lv e
        jumpToBlock dest

  | Just "vec_asmutslice" <- isCustomFunc fname,
  [op] <- ops = do
        ans <- evalOperand op
        assignLvExp lv ans
        jumpToBlock dest

 | Just "index" <- isCustomFunc fname,
    [op1, op2] <- ops = do
        let v2 = M.varOfLvalue (M.lValueofOp op2)
        ans <- evalLvalue (M.LProjection (M.LvalueProjection (M.lValueofOp op1) (M.Index v2)))
        assignLvExp lv ans
        jumpToBlock dest

 | Just "index_mut" <- isCustomFunc fname,
    [op1, op2] <- ops = do
        let v2 = M.varOfLvalue (M.lValueofOp op2)
        ans <- evalLvalue (M.LProjection (M.LvalueProjection (M.lValueofOp op1) (M.Index v2)))
        assignLvExp lv ans
        jumpToBlock dest

 | Just "vec_fromelem" <- isCustomFunc fname,
    [elem, u] <- ops = do
        ans <- buildRepeat_ elem u
        assignLvExp lv ans
        jumpToBlock dest
{-
 | Just "vec_with_capacity" <- isCustomFunc fname,
    [op1] <- ops = do
    error "no implementation for with capacity"
--    jumpToBlock dest
-}

{-
 | Just "into_iter" <- isCustomFunc fname, 
    [v] <- ops,
    Substs [ty] <- funsubst = do
    arg <- evalOperand v
    case ty of
     TyAdt defid (Substs [itemTy]) | defid == M.textId "::ops[0]::range[0]::Range[0]" -> do
        -- an identity function
        -- the range type just uses the default implementation of this trait
        assignLvExp lv arg
        jumpToBlock dest
     _ -> do
     -- default case: create a vec iterator
     -- vec -> (vec, 0)    
        let t = buildTuple [arg, MirExp (C.NatRepr) (S.app $ E.NatLit 0)]
        assignLvExp lv t
        jumpToBlock dest

 | Just "iter_next" <- isCustomFunc fname,
     [o] <- ops,
     Substs [ty] <- funsubst = do
     iter <- evalOperand o 
     case (ty, iter) of
       (TyAdt defid (Substs [itemTy]),
        MirExp (MirReferenceRepr tr) ii) 
         | defid == M.textId "::ops[0]::range[0]::Range[0]"
         , Just Refl <- testEquality tr taggedUnionRepr
         -> do -- iterator is a struct of a "start" and "end" value of type 'itemTy'
               -- to increment the iterator, make sure the start < end and then
               tyToReprCont itemTy $ \itemRepr -> do

                  r <- readMirRef tr ii
                  (MirExp C.AnyRepr tup) <- accessAggregate (MirExp tr r) 1

                  -- a "Range" is a pair of a start and end value
                  let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
                  let strTy = C.StructRepr ctx
                  let unp   = S.app $ E.FromJustValue strTy (S.app $ E.UnpackAny strTy tup)
                                       (fromString ("Bad Any unpack: " ++ show strTy))
                  let start = S.getStruct Ctx.i1of2 unp
                  let end   = S.getStruct Ctx.i2of2 unp

                  plus_one <- incrExp itemRepr start
                  let good_ret = mkSome (MirExp itemRepr start)
                  let bad_ret  = mkNone
                  let  updateRange :: MirGenerator h s ret ()
                       updateRange = let y  = S.app $ E.PackAny strTy (S.app $ E.SetStruct ctx unp Ctx.i1of2 plus_one)
                                         jj = S.app $ E.MkStruct taggedUnionCtx (Ctx.empty `Ctx.extend` (S.litExpr 0) `Ctx.extend` y)
                                    in
                                        writeMirRef ii jj

                  (MirExp C.BoolRepr boundsCheck)
                       <- evalBinOp M.Lt (arithType itemTy) (MirExp itemRepr start)
                                                            (MirExp itemRepr end)
                  ifteAny boundsCheck
                      (updateRange >> assignLvExp lv good_ret >> jumpToBlock dest)
                      (assignLvExp lv bad_ret >> jumpToBlock dest)

       _ -> do
         -- iter = struct (vec, pos of nat).
         -- if pos < size of vec, return (Some(vec[pos]), (vec, pos+1)).
         -- otherwise return (None, (vec, pos))
         (MirExp (C.VectorRepr elemty) iter_vec) <- accessAggregate iter 0
         (MirExp C.NatRepr iter_pos) <- accessAggregate iter 1
         let is_good = S.app $ E.NatLt iter_pos (S.app $ E.VectorSize iter_vec)
             good_ret_1 = mkSome $ MirExp elemty $ S.app $ E.VectorGetEntry elemty iter_vec iter_pos
             good_ret_2 = buildTuple [MirExp (C.VectorRepr elemty) iter_vec, MirExp C.NatRepr (S.app $ E.NatAdd iter_pos (S.app $ E.NatLit 1))]
             good_ret = buildTuple [good_ret_1, good_ret_2]

             bad_ret_1 = mkNone
             bad_ret_2 = buildTuple [MirExp (C.VectorRepr elemty) iter_vec, MirExp C.NatRepr iter_pos]
             bad_ret = buildTuple [bad_ret_1, bad_ret_2]

         ifteAny is_good
                 (assignLvExp lv good_ret >> jumpToBlock dest)
                 (assignLvExp lv bad_ret >> jumpToBlock dest)

 | Just "iter_map" <- isCustomFunc fname, [iter, closure] <- ops = do
     iter_e <- evalOperand iter
     closure_e <- evalOperand closure
     iter2 <- performMap (M.typeOf iter) iter_e (M.typeOf closure) closure_e
     assignLvExp lv iter2
     jumpToBlock dest

 | Just "iter_collect" <- isCustomFunc fname, [o] <- ops = do
     iter <- evalOperand o
     v <- accessAggregate iter 0
     assignLvExp lv v
     jumpToBlock dest
-}

{-
 | Just "slice_len" <-  isCustomFunc fname, [vec] <- ops, Substs [_] <- funsubst = do
     -- type of the structure is &mut[ elTy ]
     (MirExp vty vec_e) <- evalOperand vec
     case vty of
       (C.VectorRepr _) -> do
           let ans = (MirExp C.NatRepr  (G.App $ E.VectorSize vec_e))
           assignLvExp lv ans
           jumpToBlock dest
       _ -> fail $ " slice_len type is " ++ show vty ++ " from " ++ show (M.typeOf vec)
-}
{-
 | Just "wrapping_sub" <- isCustomFunc fname,
    [o1, o2] <- ops = do
       (MirExp aty a) <- evalOperand o1
       (MirExp bty b) <- evalOperand o2
       -- return (a - b) mod 2N  (this is the default behavior for BVSub)
       case (aty, bty) of
         (C.BVRepr wa, C.BVRepr wb) | Just Refl <- testEquality wa wb -> do
             traceM "WARNING: wrapping_sub does not actually wrap"
             let sub = R.App $ E.BVSub wa a b 
             let v = MirExp aty sub
             assignLvExp lv v
             jumpToBlock dest
         (_,_) -> error $ "wrapping_sub: cannot call with types " ++ show aty ++ " and " ++ show bty
-}
{-
 | Just "call" <- isCustomFunc fname, -- perform function call with a closure
   [o1, o2] <- ops,
   Substs [_ty1, aty] <- funsubst = do


     fn           <- evalOperand o1
     argtuple     <- evalOperand o2
     extra_args   <- getAllFieldsMaybe argtuple

     -- returns the function (perhaps with a coerced type, in the case of polymorphism)
     -- paired with it unpacked as a closure
     let unpackClosure :: M.Ty -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s, MirExp s)

         unpackClosure (M.TyRef ty M.Immut) rty  arg   = unpackClosure ty rty arg

         unpackClosure (M.TyClosure defid clargs) _rty arg = do
             (clty, _rty2) <- buildClosureType defid clargs
             (arg,) <$> unpackAny clty arg

         unpackClosure (M.TyDynamic _id)    rty  arg   = do
             -- a Fn object looks like a pair of
             -- a function that takes any "Any" arguments (the closure) and a struct
             --      of the actual arguments (from the funsubst) and returns type rty
             -- and an environment of type "Any

             tyToReprCont rty $ \rr ->
               case aty of
                  (TyTuple aas) -> tyListToCtx aas $ \r2 -> do
                     let args = (Ctx.empty Ctx.:> C.AnyRepr)  Ctx.<++> r2
                     let t = Ctx.empty Ctx.:> C.FunctionHandleRepr args rr Ctx.:> C.AnyRepr
                     (arg,) <$> unpackAny (Some (C.StructRepr t)) arg
                  _ -> fail $ "aty must be tuple type in dynamic call, found " ++ show (pretty aty)

         unpackClosure (M.TyParam i) rty arg = do
           -- TODO: this is a really hacky implementation of higher-order function calls
           -- we should replace it with additional arguments being passed in for the constraints
           -- Here, instead we assume that the type that is instantiating the type variable i is
           -- some closure type. We then look at the constraint to see what type of closure type it
           -- could be and then instantiate that type variable with "Any" 
           -- If we are wrong, we'll get a segmentation fault(!!!)
           -- (This means we have some unsafe instantiation code around, e.g. for Nonces,
           -- so we should get rid of that too!)
           ps <- use preds
           let findFnType (TraitProjection defid (Substs ([M.TyParam j, M.TyTuple argTys])) retTy : rest)
                 | i == j     = 
                  tyListToCtx argTys $ \argsctx -> 
                  tyToReprCont retTy $ \ret     ->
                     (Some argsctx, Some ret)

                 | otherwise  =  findFnType rest
               findFnType (_ : rest) = findFnType rest
               findFnType [] = error $ "no appropriate predicate in scope for call: " ++ show (pretty ps)

           case (arg, findFnType ps) of 
             (MirExp _ty cp,
              (Some (argsctx :: C.CtxRepr args), Some (rr :: C.TypeRepr r))) -> do
                let cp'  :: R.Expr MIR s C.AnyType
                    cp'  = unsafeCoerce cp
                let args = (Ctx.empty Ctx.:> C.AnyRepr)  Ctx.<++> argsctx
                let t = Ctx.empty Ctx.:> C.FunctionHandleRepr args rr Ctx.:> C.AnyRepr
                let arg' = MirExp C.AnyRepr cp'
                (arg',) <$> unpackAny (Some (C.StructRepr t)) arg'


         unpackClosure ty _ _arg      =
           fail $ "Don't know how to unpack Fn::call arg of type " ++ show (pretty ty)

     (fn', unpack_closure) <- unpackClosure (M.typeOf o1) (M.typeOf lv) fn
     handle <- accessAggregate unpack_closure 0
     extra_args <- getAllFieldsMaybe argtuple
     case handle of
       MirExp hand_ty handl ->
           case hand_ty of
             C.FunctionHandleRepr fargctx fretrepr -> do
                exp_to_assgn (fn' : extra_args) $ \ctx asgn ->
                   case (testEquality ctx fargctx) of
                     Just Refl -> do
                       ret_e <- G.call handl asgn
                       assignLvExp lv (MirExp fretrepr ret_e)
                       jumpToBlock dest
                     Nothing ->
                       fail $ "type mismatch in Fn::call, expected " ++ show ctx ++ "\n received " ++ show fargctx
             _ -> fail $ "bad handle type"
-}

 | Just cf <- isCustomFunc fname = fail $ "custom function not handled: " ++ (show cf)

 | otherwise =  fail $ "doCustomCall unhandled: " ++ (show $ fname)
-}


transCustomAgg :: M.CustomAggregate -> MirGenerator h s ret (MirExp s) -- deprecated
transCustomAgg (M.CARange _ty f1 f2) = evalRval (M.Aggregate M.AKTuple [f1,f2])

performUntil :: R.Expr MIR s C.NatType -> (R.Reg s C.NatType -> MirGenerator h s ret ()) -> MirGenerator h s ret ()
performUntil n f = do -- perform (f i) for i = 0..n (not inclusive). f takes as input a nat register (but shouldn't increment it)
    ind <- G.newReg $ S.app $ E.NatLit 0
    G.while (PL.InternalPos, test n ind) (PL.InternalPos, (run_incr f) ind)

   where test :: R.Expr MIR s C.NatType -> R.Reg s C.NatType -> MirGenerator h s ret (R.Expr MIR s C.BoolType)
         test n r = do
             i <- G.readReg r
             return $ S.app $ E.NatLt i n

         run_incr :: (R.Reg s C.NatType -> MirGenerator h s ret ()) -> (R.Reg s C.NatType -> MirGenerator h s ret ())
         run_incr f = \r -> do
             f r
             i <- G.readReg r
             G.assignReg r (S.app $ E.NatAdd i (S.app $ E.NatLit 1))

-- TODO: this, performMap, and "call" above should be unified. below, closure_pack is at the end of the arg list, while above, closure_pack is at the beginning. I'm not sure why, but both typecheck & work.
performClosureCall :: MirExp s -> MirExp s -> [MirExp s] -> MirGenerator h s ret (MirExp s)
performClosureCall closure_pack handle args =
    case handle of
      MirExp hand_ty handl ->
          case hand_ty of
            C.FunctionHandleRepr fargctx fretrepr ->
                exp_to_assgn (args ++ [closure_pack]) $ \ctx asgn -> -- arguments needs to be backwards for perform map below and I'm not sure why; it is forwards for FnCall.
                    case (testEquality ctx fargctx) of
                      Just Refl -> do
                          ret_e <- G.call handl asgn
                          return $ MirExp fretrepr ret_e
                      _ -> fail $ "type error in closurecall testequality: got " ++ (show ctx) ++ ", " ++ (show fargctx)
            _ -> fail $ "type error in closurecall handlety: was actually " ++ (show hand_ty)

performMap :: M.Ty -> MirExp s -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s) -- return result iterator
performMap iterty iter closurety closure =
    case (iterty, closurety) of
      (M.TyCustom (M.IterTy _t), M.TyClosure defid clargs) -> do
          (clty, rty) <- buildClosureType defid clargs
          unpack_closure <- unpackAny clty closure
          handle <- accessAggregate unpack_closure 0
          (MirExp (C.VectorRepr elemty) iter_vec) <- accessAggregate iter 0
          iter_pos <- accessAggregate iter 1
          vec_work <- G.newReg $ iter_vec -- register for modifying the vector in place
          case closure of
            MirExp clo_ty closure_e -> do
              closure_reg <- G.newReg $ closure_e -- maps take mutref closures so we need to update the closure each iteration
              performUntil (S.app $ E.VectorSize iter_vec) $ \ireg -> do
                  i <- G.readReg ireg -- loop index / index into vec
                  vec <- G.readReg vec_work -- current state of vector
                  clo <- G.readReg closure_reg -- current closure
                  let ith_vec = S.app $ E.VectorGetEntry elemty vec i -- vec[i]
                  call_res <- performClosureCall (MirExp clo_ty clo) handle [MirExp elemty ith_vec]
                  (MirExp elemty2 ith_vec') <- accessAggregate call_res 0 -- new vec[i]
                  (MirExp clo'_ty clo') <- accessAggregate call_res 1 -- new closure after call
                  case (testEquality elemty elemty2, testEquality clo_ty clo'_ty) of
                    (Just Refl, Just Refl)-> do
                      let vec' = S.app $ E.VectorSetEntry elemty vec i ith_vec'
                      G.assignReg closure_reg clo'
                      G.assignReg vec_work vec'
                    _ -> fail $ "type error in performap: " ++ (show elemty) ++ ", " ++ (show elemty2)
              new_vec <- G.readReg vec_work
              return $ buildTuple [MirExp (C.VectorRepr elemty) new_vec, iter_pos] -- we keep iter_pos the same as before. so if I called next() on an iterator and then map(), I'm where I left off. I assume this is right

      _ -> fail "bad type"

------------------------------------------------------------------------------------------------

--  LocalWords:  params IndexMut FnOnce Fn IntoIterator iter impl
--  LocalWords:  tovec fromelem tmethsubst
