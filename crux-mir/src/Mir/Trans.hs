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

{-# OPTIONS_GHC -Wincomplete-patterns -Wall -fno-warn-name-shadowing
                -fno-warn-unticked-promoted-constructors -fno-warn-unused-imports #-}
module Mir.Trans where

import Control.Monad
import Control.Monad.ST
import Control.Lens hiding (op)
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
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
import qualified Lang.Crucible.Types as CT


import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableFC as Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.Some

import Mir.Mir
import qualified Mir.Mir as M
import qualified Mir.DefId as M
import Mir.Intrinsics

--import Mir.Prims (relocateDefId)

import Mir.PP()
import Text.PrettyPrint.ANSI.Leijen(Pretty(..),hang,text,vcat)

import GHC.Stack

import Debug.Trace

-- See end of [Intrinsics] for definition of generator state FnState


-- | The main data type for values, bundling the term-level type tp along with a crucible expression of type tp.
data MirExp s where
    MirExp :: CT.TypeRepr tp -> G.Expr MIR s tp -> MirExp s

instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)

-- h for state monad
-- s phantom parameter for CFGs
type MirGenerator h s ret = G.Generator MIR h s FnState ret

-----------------------------------------------------------------------
-- ** Type translation, MIR types to Crucible types

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

tyToRepr :: HasCallStack => M.Ty -> Some CT.TypeRepr
tyToRepr t0 = case t0 of
  M.TyBool -> Some CT.BoolRepr
  M.TyTuple ts ->  tyListToCtx ts $ \repr -> Some (CT.StructRepr repr)
  M.TyArray t _sz -> tyToReprCont t $ \repr -> Some (CT.VectorRepr repr)

               -- FIXME, this should be configurable
  M.TyInt M.USize  -> Some CT.IntegerRepr
  M.TyUint M.USize -> Some CT.NatRepr

  M.TyInt M.B8 -> Some $ CT.BVRepr (knownNat :: NatRepr 8)
  M.TyInt M.B16 -> Some $ CT.BVRepr (knownNat :: NatRepr 16)
  M.TyInt M.B32 -> Some $ CT.BVRepr (knownNat :: NatRepr 32)
  M.TyInt M.B64 -> Some $ CT.BVRepr (knownNat :: NatRepr 64)
  M.TyInt M.B128 -> Some $ CT.BVRepr (knownNat :: NatRepr 128)
  M.TyUint M.B8 -> Some $ CT.BVRepr (knownNat :: NatRepr 8)
  M.TyUint M.B16 -> Some $ CT.BVRepr (knownNat :: NatRepr 16)
  M.TyUint M.B32 -> Some $ CT.BVRepr (knownNat :: NatRepr 32)
  M.TyUint M.B64 -> Some $ CT.BVRepr (knownNat :: NatRepr 64)
  M.TyUint M.B128 -> Some $ CT.BVRepr (knownNat :: NatRepr 128)
  M.TyRef (M.TySlice t) M.Immut -> tyToReprCont t $ \repr -> Some (CT.VectorRepr repr)
  M.TyRef (M.TySlice t) M.Mut   -> tyToReprCont t $ \repr -> Some (MirSliceRepr repr)
  M.TyRef t M.Immut -> tyToRepr t -- immutable references are erased!
  M.TyRef t M.Mut   -> tyToReprCont t $ \repr -> Some (MirReferenceRepr repr)
  M.TyChar -> Some $ CT.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes
  M.TyCustom custom_t -> customtyToRepr custom_t
  M.TyClosure _def_id _substs -> Some CT.AnyRepr
  M.TyStr -> Some CT.StringRepr
  M.TyAdt _defid _tyargs -> Some taggedUnionType
  M.TyDowncast _adt _i   -> Some taggedUnionType
  M.TyFloat _ -> Some CT.RealValRepr
  M.TyParam _ -> Some CT.AnyRepr -- FIXME??
  M.TyFnPtr _fnSig -> Some CT.AnyRepr
  M.TyDynamic _def -> Some CT.AnyRepr
  M.TyProjection _def _tyargs -> Some CT.AnyRepr
  _ -> error $ unwords ["unknown type?", show t0]


-- | Convert field to type. Perform the corresponding subtitution if field is a type param.
-- TODO: deeper substitution
fieldToRepr :: HasCallStack => M.Field -> M.Ty
fieldToRepr (M.Field _ t substs) = M.tySubst substs t

-- replace the subst on the Field 
substField :: [Maybe M.Ty] -> M.Field -> M.Field
substField subst (M.Field a t _subst)  = M.Field a t subst

-- Note: any args on the fields are replaced by args on the variant
variantToRepr :: HasCallStack => M.Variant -> [Maybe M.Ty] -> Some CT.CtxRepr
variantToRepr (M.Variant _vn _vd vfs _vct) args = 
    tyListToCtx (map fieldToRepr (map (substField args) vfs)) $ \repr -> Some repr

adtToRepr :: M.Adt -> Some CT.TypeRepr
adtToRepr (M.Adt _adtname _variants) = Some taggedUnionType

taggedUnionType :: CT.TypeRepr TaggedUnion
taggedUnionType = CT.StructRepr $ Ctx.empty Ctx.:> CT.NatRepr Ctx.:> CT.AnyRepr



-- As in the CPS translation, functions which manipulate types must be
-- in CPS form, since type tags are generally hidden underneath an
-- existential.

tyToReprCont :: forall a. HasCallStack => M.Ty -> (forall tp. HasCallStack => CT.TypeRepr tp -> a) -> a
tyToReprCont t f = case tyToRepr t of
                 Some x -> f x


tyListToCtx :: forall a. HasCallStack => [M.Ty] -> (forall ctx. CT.CtxRepr ctx -> a) -> a
tyListToCtx ts f =  go (map tyToRepr ts) Ctx.empty
 where go :: forall ctx. [Some CT.TypeRepr] -> CT.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)

reprsToCtx :: forall a. [Some CT.TypeRepr] -> (forall ctx. CT.CtxRepr ctx -> a) -> a
reprsToCtx rs f = go rs Ctx.empty
 where go :: forall ctx. [Some CT.TypeRepr] -> CT.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)


-----------------------------------------------------------------------




   

-----------
-- ** MIR intrinsics

newMirRef ::
  CT.TypeRepr tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
newMirRef tp = G.extensionStmt (MirNewRef tp)

dropMirRef ::
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret ()
dropMirRef refExp = void $ G.extensionStmt (MirDropRef refExp)

readMirRef ::
  CT.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret (R.Expr MIR s tp)
readMirRef tp refExp = G.extensionStmt (MirReadRef tp refExp)

writeMirRef ::
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s tp ->
  MirGenerator h s ret ()
writeMirRef ref x = void $ G.extensionStmt (MirWriteRef ref x)

subfieldRef ::
  CT.CtxRepr ctx ->
  R.Expr MIR s (MirReferenceType TaggedUnion) ->
  Ctx.Index ctx tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subfieldRef ctx ref idx = G.extensionStmt (MirSubfieldRef ctx ref idx)

subindexRef ::
  CT.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType (CT.VectorType tp)) ->
  R.Expr MIR s CT.NatType ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subindexRef tp ref idx = G.extensionStmt (MirSubindexRef tp ref idx)

-----------
-- ** Expression generation

packBase
    :: CT.TypeRepr tp
    -> CT.CtxRepr ctx
    -> Ctx.Assignment (R.Atom s) ctx
    -> (forall ctx'. Some (R.Atom s) -> CT.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a)
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
    -> CT.CtxRepr ctx
    -> Ctx.Assignment (R.Atom s) ctx
    -> (forall ctx'. Some (R.Atom s) -> CT.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a)
    -> a
unfold_ctx_assgn tp ctx asgn k =
    tyToReprCont tp $ \repr ->
        packBase repr ctx asgn k

exp_to_assgn :: HasCallStack => [MirExp s] -> (forall ctx. CT.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> a) -> a
exp_to_assgn =
    go Ctx.empty Ctx.empty 
        where go :: CT.CtxRepr ctx -> Ctx.Assignment (R.Expr MIR s) ctx -> [MirExp s] -> (forall ctx'. CT.CtxRepr ctx' -> Ctx.Assignment (R.Expr MIR s) ctx' -> a) -> a
              go ctx asgn [] k = k ctx asgn
              go ctx asgn ((MirExp tyr ex):vs) k = go (ctx Ctx.:> tyr) (asgn Ctx.:> ex) vs k


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

transConstVal :: HasCallStack => Some CT.TypeRepr -> M.ConstVal -> MirGenerator h s ret (MirExp s)
transConstVal (Some (CT.BVRepr w)) (M.ConstInt i) =
    return $ MirExp (CT.BVRepr w) (S.app $ E.BVLit w (fromInteger (M.fromIntegerLit i)))
transConstVal (Some (CT.BoolRepr)) (M.ConstBool b) = return $ MirExp (CT.BoolRepr) (S.litExpr b)
transConstVal (Some (CT.NatRepr)) (M.ConstInt i) =
    do let n = fromInteger (M.fromIntegerLit i)
       return $ MirExp CT.NatRepr (S.app $ E.NatLit n)
transConstVal (Some (CT.IntegerRepr)) (ConstInt i) =
      return $ MirExp CT.IntegerRepr (S.app $ E.IntLit (fromIntegerLit i))
transConstVal (Some (CT.StringRepr)) (M.ConstStr str) =
    do let t = Text.pack str
       return $ MirExp CT.StringRepr (S.litExpr t)
transConstVal (Some (CT.BVRepr w)) (M.ConstChar c) =
    do let i = toInteger (Char.ord c)
       return $ MirExp (CT.BVRepr w) (S.app $ E.BVLit w i)
transConstVal tp cv = fail $ "fail or unimp constant: " ++ (show tp) ++ " " ++ (show cv)


lookupVar :: M.Var -> MirGenerator h s ret (MirExp s)
lookupVar (M.Var vname _ vty _ pos) = do
    vm <- use varMap
    case (Map.lookup vname vm, tyToRepr vty) of
      (Just (Some varinfo), Some vtr)
        | Just CT.Refl <- CT.testEquality vtr (varInfoRepr varinfo) ->
            case varinfo of
              VarRegister reg ->
                do r <- G.readReg reg
                   return $ MirExp vtr r
              VarReference reg ->
                do r <- readMirRef vtr =<< G.readReg reg
                   return $ MirExp vtr r
              VarAtom a ->
                do return $ MirExp vtr (R.AtomExpr a)

        | otherwise -> fail ("bad type in lookupVar: " <> show vname <> " at " <> Text.unpack pos)
      _ -> fail ("register not found: " <> show vname <> " at " <> Text.unpack pos)

-- The return var in the MIR output is always "_0"

lookupRetVar :: HasCallStack => CT.TypeRepr ret -> MirGenerator h s ret (R.Expr MIR s ret)
lookupRetVar tr = do
    vm <- use varMap
    case (Map.lookup "_0" vm) of
      Just (Some varinfo) ->
        case  CT.testEquality tr (varInfoRepr varinfo) of 
          Just CT.Refl ->
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


evalOperand :: HasCallStack => M.Operand -> MirGenerator h s ret (MirExp s)
evalOperand (M.Consume lv) = evalLvalue lv
evalOperand (M.OpConstant (M.Constant conty conlit)) =
    case conlit of
       M.Value constval   -> transConstVal (tyToRepr conty) constval
       M.Item defId _args -> fail $ "cannot translate item " ++ show defId
       M.LPromoted prom   -> fail $ "cannot translate promoted " ++ show prom


-- Given two bitvectors, extend the length of the shorter one so that they
-- have the same length
-- Use the sign of the first bitvector to determine how to sign extend
extendToMax :: (1 <= n, 1 <= m) =>
               NatRepr n -> G.Expr MIR s (CT.BVType n) ->
               NatRepr m -> G.Expr MIR s (CT.BVType m) -> Maybe M.ArithType ->
   (forall n. (1 <= n) => NatRepr n -> G.Expr MIR s (CT.BVType n) -> G.Expr MIR s (CT.BVType n) -> a) -> a
extendToMax n e1 m e2 (Just arith) k =
   let extend :: (1 <= w, 1 <= r, w+1 <= r) => (NatRepr r)
         -> (NatRepr w)
         -> (f (CT.BVType w))
         -> E.App MIR f (CT.BVType r)
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



transBinOp :: M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
transBinOp bop op1 op2 = do
    me1 <- evalOperand  op1
    me2 <- evalOperand  op2
    case (me1, me2) of
      (MirExp (CT.BVRepr na) e1a, MirExp (CT.BVRepr ma) e2a) ->
          extendToMax na e1a ma e2a (M.arithType op1) $ \ n e1 e2 -> 
          -- TODO: if the BVs are not the same width extend the shorter one
            case (bop, M.arithType op1) of
              (M.Add, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVAdd n e1 e2)
              (M.Sub, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSub n e1 e2)
              (M.Mul, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVMul n e1 e2)
              (M.Div, Just M.Unsigned) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVUdiv n e1 e2)
              (M.Div, Just M.Signed) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSdiv n e1 e2)
              (M.Rem, Just M.Unsigned) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVUrem n e1 e2)
              (M.Rem, Just M.Signed) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSrem n e1 e2)
              (M.BitXor, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVXor n e1 e2)
              (M.BitAnd, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVAnd n e1 e2)
              (M.BitOr, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVOr n e1 e2)
              (M.Shl, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVShl n e1 e2)
              (M.Shr, Just M.Unsigned) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVLshr n e1 e2)
              (M.Shr, Nothing) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVLshr n e1 e2)
              (M.Shr, Just M.Signed) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVAshr n e1 e2)
              (M.Lt, Just M.Unsigned) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVUlt n e1 e2)
              (M.Lt, Just M.Signed) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVSlt n e1 e2)
              (M.Le, Just M.Unsigned) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVUle n e1 e2)
              (M.Le, Just M.Signed) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVSle n e1 e2)
              (M.Ne, _) -> return $ MirExp (CT.BoolRepr) (S.app $ E.Not $ S.app $ E.BVEq n e1 e2)
              (M.Beq, _) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVEq n e1 e2)
              _ -> fail $ "bad binop: " ++ show (M.BinaryOp bop op1 op2)
      (MirExp CT.BoolRepr e1, MirExp CT.BoolRepr e2) ->
          case bop of
            M.BitAnd -> return $ MirExp CT.BoolRepr (S.app $ E.And e1 e2)
            M.BitXor -> return $ MirExp CT.BoolRepr (S.app $ E.BoolXor e1 e2)
            M.BitOr -> return $ MirExp CT.BoolRepr (S.app $ E.Or e1 e2)
            M.Beq -> return $ MirExp CT.BoolRepr (S.app $ E.Not $ S.app $ E.BoolXor e1 e2)
            _ -> fail "bad binop"
      (MirExp CT.NatRepr e1, MirExp CT.NatRepr e2) ->
          case bop of
            M.Beq -> return $ MirExp CT.BoolRepr (S.app $ E.NatEq e1 e2)
            M.Lt -> return $ MirExp CT.BoolRepr (S.app $ E.NatLt e1 e2)
            M.Le -> return $ MirExp CT.BoolRepr (S.app $ E.NatLe e1 e2)
            M.Add -> return $ MirExp CT.NatRepr (S.app $ E.NatAdd e1 e2)
            M.Sub -> return $ MirExp CT.NatRepr (S.app $ E.NatSub e1 e2)
            M.Mul -> return $ MirExp CT.NatRepr (S.app $ E.NatMul e1 e2)
            M.Ne -> return $ MirExp CT.BoolRepr (S.app $ E.Not $ S.app $ E.NatEq e1 e2)
            _ -> fail "bad natural number binop"

      (_, _) -> fail $ "bad or unimplemented type: " ++ (show bop) ++ ", " ++ (show me1) ++ ", " ++ (show me2)



transCheckedBinOp ::  M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s) -- returns tuple of (result, bool)
transCheckedBinOp  a b c = do
    res <- transBinOp a b c
    return $ buildTuple [res, MirExp (CT.BoolRepr) (S.litExpr False)] -- This always succeeds, since we're checking correctness. We can also check for overflow if desired.


-- Nullary ops in rust are used for resource allocation, so are not interpreted
transNullaryOp ::  M.NullOp -> M.Ty -> MirGenerator h s ret (MirExp s)
transNullaryOp _ _ = fail "nullop"

transUnaryOp :: M.UnOp -> M.Operand -> MirGenerator h s ret (MirExp s)
transUnaryOp uop op = do
    mop <- evalOperand op
    case (uop, mop) of
      (M.Not, MirExp CT.BoolRepr e) -> return $ MirExp CT.BoolRepr $ S.app $ E.Not e
      (M.Neg, MirExp (CT.BVRepr n) e) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSub n (S.app $ E.BVLit n 0) e)
      _ -> fail "bad op or type for unary"


-- a -> u -> [a;u]
buildRepeat :: M.Operand -> M.ConstUsize -> MirGenerator h s ret (MirExp s)
buildRepeat op size = do
    (MirExp tp e) <- evalOperand op
    let n = fromInteger size
    return $ MirExp (CT.VectorRepr tp) (S.app $ E.VectorReplicate tp (S.app $ E.NatLit n) e)

buildRepeat_ :: M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
buildRepeat_ op size = do
    let (M.OpConstant (M.Constant _ (M.Value (M.ConstInt i)))) = size
    buildRepeat op (M.fromIntegerLit i)


-- array in haskell -> crucible array
buildArrayLit :: forall h s tp ret.  CT.TypeRepr tp -> [MirExp s] -> MirGenerator h s ret (MirExp s)
buildArrayLit trep exps = do
    vec <- go exps V.empty
    return $ MirExp (CT.VectorRepr trep) $  S.app $ E.VectorLit trep vec
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
    MirExp (CT.StructRepr ctx) (S.app $ E.MkStruct ctx asgn)

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
      MirExp (CT.StructRepr ctx) _ -> do
        let s = Ctx.sizeInt (Ctx.size ctx)
        mapM (accessAggregate e) [0..(s-1)]
      _ -> fail "getallfields of non-struct"

accessAggregate :: HasCallStack => MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregate (MirExp (CT.StructRepr ctx) ag) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
      let tpr = ctx Ctx.! idx
      return $ MirExp tpr (S.getStruct idx ag)
accessAggregate (MirExp ty a) b = fail $ "invalid access: " ++ (show a) ++ " : " ++ show ty ++ ", " ++ (show b)

modifyAggregateIdx :: MirExp s -> -- aggregate to modify
                      MirExp s -> -- thing to insert
                      Int -> -- index
                      MirGenerator h s ret (MirExp s)
modifyAggregateIdx (MirExp (CT.StructRepr agctx) ag) (MirExp instr ins) i
  | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size agctx) = do
      let tpr = agctx Ctx.! idx
      case (testEquality tpr instr) of
          Just Refl -> return $ MirExp (CT.StructRepr agctx) (S.setStruct agctx ag idx ins)
          _ -> fail "bad modify"

modifyAggregateIdx (MirExp ty _) _ _ =
  do fail ("modfiyAggregateIdx: Expected Crucible structure type, but got:" ++ show ty)


-- casts

extendUnsignedBV :: MirExp s -> M.BaseSize -> MirGenerator h s ret (MirExp s)
extendUnsignedBV (MirExp tp e) b =
    case (tp, b) of
      (CT.BVRepr n, M.B16) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 16) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 16)) (S.app $ E.BVZext (knownNat :: NatRepr 16) n e)
      (CT.BVRepr n, M.B32) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 32) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 32)) (S.app $ E.BVZext (knownNat :: NatRepr 32) n e)
      (CT.BVRepr n, M.B64) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 64) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 64)) (S.app $ E.BVZext (knownNat :: NatRepr 64) n e)
      (CT.BVRepr n, M.B128) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 128) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 128)) (S.app $ E.BVZext (knownNat :: NatRepr 128) n e)
      _ -> fail "unimplemented unsigned bvext"

extendSignedBV :: MirExp s -> M.BaseSize -> MirGenerator h s ret (MirExp s)
extendSignedBV (MirExp tp e) b =
    case (tp, b) of
      (CT.BVRepr n, M.B16) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 16) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 16)) (S.app $ E.BVSext (knownNat :: NatRepr 16) n e)
      (CT.BVRepr n, M.B32) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 32) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 32)) (S.app $ E.BVSext (knownNat :: NatRepr 32) n e)
      (CT.BVRepr n, M.B64) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 64) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 64)) (S.app $ E.BVSext (knownNat :: NatRepr 64) n e)
      (CT.BVRepr n, M.B128) | Just LeqProof <- testLeq (incNat n) (knownNat :: NatRepr 128) ->
                return $ MirExp (CT.BVRepr (knownNat :: NatRepr 128)) (S.app $ E.BVSext (knownNat :: NatRepr 128) n e)
      _ -> fail "unimplemented unsigned bvext"

-- | convert a baseSize to a nat repr
-- The BaseSize must *not* be USize.
baseSizeToNatCont :: HasCallStack => M.BaseSize -> (forall w. (1 <= w) => CT.NatRepr w -> a) -> a
baseSizeToNatCont M.B8   k = k (knownNat :: NatRepr 8)
baseSizeToNatCont M.B16  k = k (knownNat :: NatRepr 16)
baseSizeToNatCont M.B32  k = k (knownNat :: NatRepr 32)
baseSizeToNatCont M.B64  k = k (knownNat :: NatRepr 64)
baseSizeToNatCont M.B128 k = k (knownNat :: NatRepr 128)
baseSizeToNatCont M.USize _k = error "BaseSize is undetermined"

evalCast' :: M.CastKind -> M.Ty -> MirExp s -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast' ck ty1 e ty2  =
    case (ck, ty1, ty2) of
      (M.Misc,a,b) | a == b -> return e
      (M.Misc, M.TyUint _, M.TyUint s) -> extendUnsignedBV e s
      (M.Misc, M.TyInt _, M.TyInt s) -> extendSignedBV e s
      (M.Misc, M.TyCustom (M.BoxTy tb1), M.TyCustom (M.BoxTy tb2)) -> evalCast' ck tb1 e tb2

      (M.Unsize, M.TyRef (M.TyArray tp _sz) M.Immut, M.TyRef (M.TySlice tp') M.Immut)
        | tp == tp' -> return e -- arrays and immutable slices have the same denotation
        | otherwise -> fail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray tp _sz) M.Mut, M.TyRef (M.TySlice tp') M.Immut)
        | tp == tp' -> fail "FIXME! implement mut->immut unsize cast!"
        | otherwise -> fail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray tp sz) M.Mut, M.TyRef (M.TySlice tp') M.Mut)
        | tp == tp', MirExp (MirReferenceRepr (CT.VectorRepr elem_tp)) ref <- e
        -> do let start = S.litExpr 0
              let end   = S.litExpr (fromIntegral sz)
              let tup   = S.mkStruct
                              (Ctx.Empty Ctx.:> MirReferenceRepr (CT.VectorRepr elem_tp) Ctx.:> CT.NatRepr Ctx.:> CT.NatRepr)
                              (Ctx.Empty Ctx.:> ref Ctx.:> start Ctx.:> end)
              return $ MirExp (MirSliceRepr elem_tp) tup
        | otherwise -> fail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray _ _) M.Immut, M.TyRef (M.TySlice _) M.Mut) ->
         fail "Cannot cast an immutable array to a mutable slice"

      -- Trait object creation.
      (M.Unsize, M.TyRef baseType _, M.TyRef (M.TyDynamic traitName) _) ->
        mkTraitObject traitName baseType e

      -- C-style adts, casting an enum value to a TyInt
      (M.Misc, M.TyCustom (CEnum _n), M.TyInt USize) -> return e
      (M.Misc, M.TyCustom (CEnum _n), M.TyInt sz) | (MirExp CT.IntegerRepr e0) <- e ->
         baseSizeToNatCont sz $ \nat ->
           -- TODO: what happened to E.IntegerToSBV? Will we lose the sign here?
           return $ MirExp (CT.BVRepr nat) (R.App $ E.IntegerToBV nat e0)

      -- C-style adts, casting a TyInt to an enum value
      (M.Misc, M.TyInt USize, M.TyCustom (CEnum _n)) -> return e
      (M.Misc, M.TyInt _sz,   M.TyCustom (CEnum _n)) | (MirExp (CT.BVRepr nat) e0) <- e ->
           return $ MirExp knownRepr (R.App $ E.SbvToInteger nat e0)


      _ -> fail $ "unimplemented cast: " ++ (show ck) ++ " " ++ (show ty1) ++ " as " ++ (show ty2)
 
evalCast :: M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast ck op ty = do
    e <- evalOperand op
    evalCast' ck (M.typeOf op) e ty



-- | Create a new trait object for the given trait for the given
-- value. Fails if the value does not implement the trait.
mkTraitObject :: HasCallStack => M.DefId -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s)
mkTraitObject traitName baseType (MirExp baseTyr baseValue) = do
  (Some timpls) <- traitImplsLookup traitName
  case Map.lookup (typeName baseType) (timpls^.vtables) of
    Nothing -> fail $ Text.unpack $ Text.unwords ["Error while creating a trait object: type ",
                                                   Text.pack (show baseType)," does not implement trait ", M.idText traitName]
    Just vtbl -> do
      let vtableCtx = timpls^.vtableTyRepr
      let ctxr      = Ctx.empty Ctx.:> CT.AnyRepr Ctx.:> CT.StructRepr vtableCtx
      let assn      = R.App $ E.MkStruct vtableCtx (Ctx.fmapFC valueToExpr vtbl)
      let obj       = R.App $ E.PackAny (CT.StructRepr ctxr)
                       (R.App $ E.MkStruct ctxr (Ctx.empty Ctx.:> (R.App $ E.PackAny baseTyr baseValue) Ctx.:> assn))
      return $
        MirExp CT.AnyRepr obj

      
traitImplsLookup :: HasCallStack => M.DefId -> MirGenerator h s ret (Some TraitImpls)
traitImplsLookup traitName = do
  (TraitMap mp) <- use traitMap
  case Map.lookup traitName mp of
    Nothing -> fail $ Text.unpack $ Text.unwords ["Trait does not exist ", M.idText traitName]
    Just timpls -> return timpls
    
-- | TODO: implement. Returns the name of the name, as seen MIR
-- NOTE: this is very wrong
typeName :: M.Ty -> M.Ty
typeName = id


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

getVariant :: HasCallStack => M.Ty -> MirGenerator h s ret (M.Variant, [Maybe M.Ty])
getVariant (M.TyAdt nm args) = do
    am <- use adtMap
    case Map.lookup nm am of
       Nothing -> fail ("Unknown ADT: " ++ show nm)
       Just [struct_variant] -> return (struct_variant, args)
       _      -> fail ("Expected ADT with exactly one variant: " ++ show nm)
getVariant (M.TyDowncast (M.TyAdt nm args) ii) = do
    let i = fromInteger ii
    am <- use adtMap
    case Map.lookup nm am of
       Nothing -> fail ("Unknown ADT: " ++ show nm)
       Just vars | i < length vars -> return $ (vars !! i, args)
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
            | CT.StructRepr (Ctx.Empty Ctx.:> CT.NatRepr Ctx.:> CT.AnyRepr) <- elty
            -> do
             (struct_variant, args) <- getVariant (M.typeOf base)
             Some ctx <- return $ variantToRepr struct_variant args
             case Ctx.intIndex idx (Ctx.size ctx) of
                     Nothing -> fail ("Invalid index: " ++ show idx)
                     Just (Some idx') -> 
                        do r' <- subfieldRef ctx ref idx'
                           return (MirExp (MirReferenceRepr (ctx Ctx.! idx')) r')

          M.ConstantIndex offset _min_len fromend
            | CT.VectorRepr tp' <- elty
            , fromend == False ->
                do let natIdx = S.litExpr (fromIntegral offset)
                   r' <- subindexRef tp' ref natIdx
                   return (MirExp (MirReferenceRepr tp') r')

            | CT.VectorRepr _tp' <- elty
            , fromend == True ->
                fail ("FIXME: implement constant fromend indexing in reference projection")

          M.Index op
            | CT.VectorRepr tp' <- elty
            -> do MirExp idxTy idx <- evalOperand op
                  case idxTy of
                    CT.NatRepr ->
                      do r' <- subindexRef tp' ref idx
                         return (MirExp (MirReferenceRepr tp') r')
                    CT.BVRepr w ->
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
                   return $ MirExp CT.NatRepr end
              _ -> fail "Expected mutable slice value"
    _ ->
      do MirExp t e <- evalLvalue lv
         case t of
           CT.VectorRepr _ -> return $ MirExp CT.NatRepr $ S.vectorSize e -- might need to convert nat to bv later
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
      TyCustom (CEnum _adt) -> return e
      _ -> do (MirExp CT.NatRepr idx) <- accessAggregate e 0
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
                                   M.AKClosure defid _argsm -> do
                                       args <- mapM evalOperand ops
                                       buildClosureHandle defid args
evalRval (M.RAdtAg (M.AdtAg adt agv [])) | isCStyle adt  = do
    return $ (MirExp knownRepr (R.App (E.IntLit agv)))
evalRval (M.RAdtAg (M.AdtAg _adt agv ops))  = do
    es <- mapM evalOperand ops
    return $ buildTaggedUnion agv es

-- A closure is (packed into an any) of the form [handle, arguments] (arguments being those packed into the closure, not the function arguments)
buildClosureHandle :: M.DefId -> [MirExp s] -> MirGenerator h s ret (MirExp s)
buildClosureHandle funid args = do
    hmap <- use handleMap
    case (Map.lookup funid hmap) of
      Just (MirHandle _ _ fhandle) -> do
          let closure_arg = buildTuple args
          let handle_cl = S.app $ E.HandleLit fhandle
              handle_cl_ty = FH.handleType fhandle
              handl = MirExp handle_cl_ty handle_cl
          let closure_unpack = buildTuple [handl, closure_arg]
          return $ packAny closure_unpack
      _ ->
       do fail ("buildClosureHandle: unknmown function: " ++ show funid)


buildClosureType :: M.DefId -> [M.Ty] -> MirGenerator h s ret (Some CT.TypeRepr) -- get type of closure, in order to unpack the any
buildClosureType defid args = do
    hmap <- use handleMap
    case (Map.lookup defid hmap) of
      Just (MirHandle _ _ fhandle) -> do
          -- build type StructRepr [HandleRepr, StructRepr [args types]]
          tyListToCtx args $ \argsctx -> do
              let argstruct = CT.StructRepr argsctx
                  handlerepr = FH.handleType fhandle
              reprsToCtx [Some handlerepr, Some argstruct] $ \t ->
                  return $ Some (CT.StructRepr t)
      _ ->
       do fail ("buildClosureType: unknmown function: " ++ show defid)


unpackAny :: HasCallStack => Some CT.TypeRepr -> MirExp s -> MirGenerator h s ret (MirExp s)
unpackAny (Some tr) e@(MirExp CT.AnyRepr _) = return $ unpackAnyE tr e
unpackAny _ (MirExp tr _) = fail $ "bad anytype, found " ++ show (pretty tr) 


unpackAnyE :: HasCallStack => CT.TypeRepr t -> MirExp s -> MirExp s
unpackAnyE tr (MirExp CT.AnyRepr e) =
   MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) ("Bad Any unpack"))
unpackAnyE _ _ = error $ "bad anytype unpack"


packAny ::  MirExp s -> (MirExp s)
packAny (MirExp e_ty e) = MirExp CT.AnyRepr (S.app $ E.PackAny e_ty e)

filterMaybes :: [Maybe a] -> [a]
filterMaybes [] = []
filterMaybes ((Just a):as) = a : (filterMaybes as)
filterMaybes ((Nothing):as) = filterMaybes as

evalLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalLvalue (M.Tagged l _) = evalLvalue l
evalLvalue (M.Local var) = do -- traceM $ "evalLValue local" ++ show (pretty var)
                              lookupVar var
evalLvalue (M.LProjection (M.LvalueProjection lv (M.PField field _ty))) = do
    am <- use adtMap
    case M.typeOf lv of
      M.TyAdt nm args ->
        case Map.lookup nm am of
          Nothing -> fail ("Unknown ADT: " ++ show nm )
          Just [struct_variant] ->
            do etu <- evalLvalue lv
               e   <- accessAggregate etu 1 -- get the ANY data payload
               Some ctx <- return $ variantToRepr struct_variant args
               struct <- unpackAny (Some (CT.StructRepr ctx)) e
               accessAggregate struct field
          Just _ -> fail ("Expected ADT with exactly one variant: " ++ show nm)

      M.TyClosure defid argsm -> do -- if lv is a closure, then accessing the ith component means accessing the ith arg in the struct
        e <- evalLvalue lv
        let args = filterMaybes argsm
        clty <- buildClosureType defid args
        unpack_closure <- unpackAny clty e
        clargs <- accessAggregate unpack_closure 1
        accessAggregate clargs field

      mty@(M.TyDowncast _ _) -> do
         (struct_variant, args) <- getVariant mty 
         e <- evalLvalue lv
         Some ctx <- return $ variantToRepr struct_variant args
         struct <- unpackAny (Some (CT.StructRepr ctx)) e
         res <- accessAggregate struct field
         return res


      _ -> do -- otherwise, lv is a tuple
        ag <- evalLvalue lv
        accessAggregate ag field
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Index i))) = do
    (MirExp arr_tp arr) <- evalLvalue lv
    (MirExp ind_tp ind) <- evalOperand i
    case (arr_tp, ind_tp) of
      (CT.VectorRepr elt_tp, CT.NatRepr) -> do
          G.assertExpr (ind S..< (S.app (E.VectorSize arr)))
                       (S.litExpr "Index out of range")
          return $ MirExp elt_tp $ S.app $ E.VectorGetEntry elt_tp arr ind
      _ -> fail "Bad index"

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
              _ -> error $ unwords ["Expected reference value in mutable dereference", show lv]
     tp ->
       fail $ unwords ["Expected reference type in dereference", show tp, show lv]

-- downcast: extracting the injection from an ADT. This is done in rust after switching on the discriminant.
-- We don't really do anything here --- all the action is when we project from the downcasted adt
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Downcast _i))) = do
    (MirExp tyr lve) <- evalLvalue lv
    case testEquality tyr taggedUnionType of
       Just Refl -> accessAggregate (MirExp tyr lve) 1
       Nothing   -> fail $ "expected ADT type, instead found type: " ++ show (pretty (M.typeOf lv)) ++ " aka " ++ show tyr 
evalLvalue lv = fail $ "unknown lvalue access: " ++ (show lv)




--------------------------------------------------------------------------------------
-- ** Statements
--

-- v := rvalue
--
assignVarRvalue :: M.Var -> M.Rvalue -> MirGenerator h s ret ()
assignVarRvalue var rv = assignVarExp var (Just (M.typeOf rv)) =<< evalRval rv

-- v := mirexp
-- FIXME... this 'Maybe Ty' argument should really just by 'Ty', but
--  we need to reoganize call sites to pass this information through
assignVarExp :: HasCallStack => M.Var -> Maybe M.Ty -> MirExp s -> MirGenerator h s ret ()

-- Implement implict coercion from mutable reference to immutable reference.  The major
-- invariant guarantee given by the borrow checker is that, so long as the immutable
-- reference is live, the value will not change.  This justifies immediately deferencing
-- the pointer to get out the value within.
assignVarExp v@(M.Var _vnamd _ (M.TyRef lhs_ty M.Immut) _ _pos) (Just (M.TyRef _rhs_ty M.Mut)) (MirExp (MirReferenceRepr e_ty) e) =
  case lhs_ty of
    M.TySlice _ ->
         do fail "FIXME! implement implict cast from mutable slice to immutable slice"
    _ ->
         do r <- readMirRef e_ty e
            assignVarExp v Nothing (MirExp e_ty r)

assignVarExp (M.Var vname _ vty _ pos) _ (MirExp e_ty e) = do
    vm <- use varMap
    case (Map.lookup vname vm) of
      Just (Some varinfo)
        | Just CT.Refl <- testEquality e_ty (varInfoRepr varinfo) ->
            case varinfo of
              VarRegister reg ->
                do G.assignReg reg e
              VarReference reg ->
                do r <- G.readReg reg
                   writeMirRef r e
              VarAtom _ ->
                do fail ("Cannot assign to atom: " <> show vname <> " at " <> Text.unpack pos)
        | otherwise ->
            fail $ "type error in assignment: got " ++ (show (pretty e_ty)) ++ " but expected "
                     ++ (show (varInfoRepr varinfo)) ++ " in assignment of " ++ (show vname) ++ " which has type "
                     ++ (show (pretty vty)) ++ " with exp " ++ (show (pretty e)) ++ " at " ++ (Text.unpack pos)
      Nothing -> fail ("register not found: " ++ show vname ++ " at " ++ Text.unpack pos)

-- lv := mirexp

-- FIXME... this 'Maybe Ty' argument should really just by 'Ty', but
--  we need to reoganize call sites to pass this information through
assignLvExp :: HasCallStack => M.Lvalue -> Maybe M.Ty -> MirExp s -> MirGenerator h s ret ()
assignLvExp lv re_tp re = do
    case lv of
        M.Tagged lv _ -> assignLvExp lv re_tp re
        M.Local var -> assignVarExp var re_tp re
        M.Static -> fail "static"
        M.LProjection (M.LvalueProjection lv (M.PField field _ty)) -> do
            am <- use adtMap
            case M.typeOf lv of
              M.TyAdt nm args ->
                case Map.lookup nm am of
                  Nothing -> fail ("Unknown ADT: " ++ show nm)
                  Just [struct_variant] ->
                    do etu <- evalLvalue lv
                       e   <- accessAggregate etu 1 -- get the ANY data payload
                       Some ctx <- return $ variantToRepr struct_variant args
                       struct <- unpackAny (Some (CT.StructRepr ctx)) e
                       struct' <- modifyAggregateIdx struct re field
                       etu' <- modifyAggregateIdx etu (packAny struct') 1
                       assignLvExp lv (Just (M.TyAdt nm args)) etu'
                  Just _ -> fail ("Expected ADT with exactly one variant: " ++ show nm)

              M.TyClosure _ _ -> fail "assign to closure unimp"

              _ -> do
                ag <- evalLvalue lv
                new_ag <- modifyAggregateIdx ag re field
                assignLvExp lv Nothing new_ag

        M.LProjection (M.LvalueProjection (M.LProjection (M.LvalueProjection lv' M.Deref)) (M.Index op))
          | M.TyRef (M.TySlice _) M.Mut <- M.typeOf lv' ->
            do MirExp slice_tp slice <- evalLvalue lv'

               MirExp ind_tp ind     <- evalOperand op
               MirExp r_tp r         <- return re
               case (slice_tp, ind_tp) of
                 (MirSliceRepr el_tp, CT.NatRepr)
                   | Just Refl <- testEquality r_tp el_tp
                   -> do let _ctx   = Ctx.Empty Ctx.:> MirReferenceRepr (CT.VectorRepr el_tp) Ctx.:> CT.NatRepr Ctx.:> CT.NatRepr
                         let ref   = S.getStruct (Ctx.natIndex @0) slice
                         let start = S.getStruct (Ctx.natIndex @1) slice
                         let len   = S.getStruct (Ctx.natIndex @2) slice
                         G.assertExpr (ind S..< len) (S.litExpr "Index out of range")
                         let ind'  = start S..+ ind
                         arr <- readMirRef (CT.VectorRepr el_tp) ref
                         let arr' = S.app $ E.VectorSetEntry el_tp arr ind' r
                         writeMirRef ref arr'

                 _ -> fail $ "bad type in slice assignment"

        M.LProjection (M.LvalueProjection lv (M.Index op)) -> do
            (MirExp arr_tp arr) <- evalLvalue lv
            (MirExp ind_tp ind) <- evalOperand op
            case re of
              MirExp r_tp r ->
                case (arr_tp, ind_tp) of
                  (CT.VectorRepr x, CT.NatRepr) ->
                      case (testEquality x r_tp) of
                        Just Refl -> do
                          G.assertExpr (ind S..< (S.app (E.VectorSize arr)))
                                       (S.litExpr "Index out of range")
                          let arr' = MirExp arr_tp (S.app $ E.VectorSetEntry r_tp arr ind r)
                          assignLvExp lv (Just (M.typeOf lv)) arr'
                        Nothing -> fail "bad type in assign"
                  _ -> fail $ "bad type in assign"
        M.LProjection (M.LvalueProjection lv M.Deref) ->
            do MirExp ref_tp ref <- evalLvalue lv
               case (ref_tp, re) of
                 (MirReferenceRepr tp, MirExp tp' e)
                   | Just CT.Refl <- testEquality tp tp' -> writeMirRef ref e
                 _ -> fail $ unwords ["Type mismatch when assigning through a reference", show lv, ":=", show re]

        _ -> fail $ "rest assign unimp: " ++ (show lv) ++ ", " ++ (show re)

storageLive :: M.Lvalue -> MirGenerator h s ret ()
storageLive (M.Local (M.Var nm _ _ _ _)) =
  do vm <- use varMap
     case Map.lookup nm vm of
       Just (Some varinfo@(VarReference reg)) ->
         do r <- newMirRef (varInfoRepr varinfo)
            G.assignReg reg r
       _ -> return ()

storageLive lv =
 do fail ("FIXME: unimplemented 'storageLive': " ++ M.pprint lv)

storageDead :: M.Lvalue -> MirGenerator h s ret ()
storageDead (M.Local (M.Var nm _ _ _ _)) =
  do vm <- use varMap
     case Map.lookup nm vm of
       Just (Some _varinfo@(VarReference reg)) ->
         do dropMirRef =<< G.readReg reg
       _ -> return ()
storageDead lv =
  do fail ("FIXME: unimplement 'storageDead': " ++ M.pprint lv)


transStatement :: HasCallStack => M.Statement -> MirGenerator h s ret ()
transStatement (M.Assign lv rv pos) =
  do setPosition pos
     re <- evalRval rv
     assignLvExp lv (Just (M.typeOf rv)) re
transStatement (M.StorageLive lv) =
  do storageLive lv
transStatement (M.StorageDead lv) =
  do storageDead lv
transStatement (M.SetDiscriminant _lv _i) = fail "setdiscriminant unimp" -- this should just change the first component of the adt
transStatement M.Nop = return ()

ifteAny :: R.Expr MIR s CT.BoolType
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
transSwitch (MirExp (CT.BoolRepr) e) [v] [t1,t2] =
    if v == 1 then
              doBoolBranch e t1 t2
    else
              doBoolBranch e t2 t1
transSwitch (MirExp (CT.IntegerRepr) e) vs ts =
    doIntBranch e vs ts

transSwitch (MirExp f _e) _ _  = error $ "bad switch: " ++ show f

doBoolBranch :: R.Expr MIR s CT.BoolType -> M.BasicBlockInfo -> M.BasicBlockInfo -> MirGenerator h s ret a
doBoolBranch e t f = do
    lm <- use labelMap
    case (Map.lookup t lm, Map.lookup f lm) of
      (Just tb, Just fb) -> G.branch e tb fb
      _ -> error "bad lookup on boolbranch"

-- nat branch: branch by iterating through list
doIntBranch :: R.Expr MIR s CT.IntegerType -> [Integer] -> [M.BasicBlockInfo] -> MirGenerator h s ret a
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

jumpToBlock' :: M.BasicBlockInfo -> MirGenerator h s ret a
jumpToBlock' bbi = do
    lm <- use labelMap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"

doReturn :: HasCallStack => CT.TypeRepr ret -> MirGenerator h s ret a
doReturn tr = do
    e <- lookupRetVar tr
    G.returnFromFunction e

-- If you can't find the handle with its original name
--   1. try adding the "stdlib" prefix
--   2. try looking up a static trait method
--   3. try both
lookupHandle :: MethName -> HandleMap -> Maybe MirHandle
lookupHandle funid hmap
   | Just mh <- Map.lookup funid hmap = Just mh
   | Just mh <- Map.lookup (M.relocateDefId funid) hmap = Just mh
   | Just mh <- Map.lookup (M.mangleTraitId funid) hmap = Just mh
   | Just mh <- Map.lookup (M.relocateDefId (M.mangleTraitId funid)) hmap = Just mh
   | otherwise = Nothing

-- Coerce an Adt value with parameters in 'subst' to an adt value with parameters in 'asubsts'
-- The ADT is a tagged union, so to do the coercion, we need to switch through the potential
-- variants, and when we find that one, coerce the fields of that variant.
-- For simplicity, this function only works for Adts with variants that have <= 2 fields.

type Coercion = forall h s ret. HasCallStack => M.Ty -> (M.Ty, MirExp s) -> MirGenerator h s ret (MirExp s)

coerceAdt :: forall h s ret. HasCallStack => Bool ->
      M.DefId
   -> [Maybe M.Ty]
   -> [Maybe M.Ty]
   -> R.Expr MIR s TaggedUnion
   -> MirGenerator h s ret (R.Expr MIR s TaggedUnion)
coerceAdt dir adt substs asubsts e0 = do
  let f :: Coercion
      f = if dir then coerceArg else coerceRet

  am <- use adtMap
  let variants = case am Map.!? adt of
                    Just vs -> vs
                    Nothing -> fail $ "Cannot find declaration for adt: " ++ show adt

  let idx :: R.Expr MIR s CT.NatType
      idx = (S.getStruct Ctx.i1of2 e0)
  let dat :: R.Expr MIR s CT.AnyType
      dat = (S.getStruct Ctx.i2of2 e0)

  let loop :: Natural -> [M.Variant] -> R.Expr MIR s CT.AnyType
           -> MirGenerator h s ret (R.Expr MIR s CT.AnyType)
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
                     let atyp = fieldToRepr (substField asubsts (List.head fields))
                     let typ  = fieldToRepr (substField substs  (List.head fields))
                     let sr = CT.StructRepr cr
                     let unp = (S.app $ E.FromJustValue sr (S.app $ E.UnpackAny sr e)
                                       ("not the expected type"))
                     (MirExp tr' e') <- f typ (atyp, MirExp tr (S.getStruct Ctx.baseIndex unp))
                     let updated = S.mkStruct (Ctx.Empty Ctx.:> tr') (Ctx.empty `Ctx.extend` e')
                     let packed  = R.App (E.PackAny (CT.StructRepr (Ctx.Empty Ctx.:> tr'))
                                         updated)
                     return $ packed
                   -- i.e. cons
                   Some cr@(Ctx.Empty Ctx.:> tr1 Ctx.:> tr2) -> do
                     let aty1:aty2:[] = map (fieldToRepr . substField asubsts) fields
                     let typ1:typ2:[] = map (fieldToRepr . substField substs) fields
                     let sr = CT.StructRepr cr
                     let unpacked = (S.app $ E.FromJustValue sr (S.app $ E.UnpackAny sr e)
                                       ("not the expected type"))
                     (MirExp tr1' e1') <- f typ1 (aty1, MirExp tr1 (S.getStruct Ctx.i1of2 unpacked))
                     (MirExp tr2' e2') <- f typ2 (aty2, MirExp tr2 (S.getStruct Ctx.i2of2 unpacked))
                     let cr' = (Ctx.Empty Ctx.:> tr1' Ctx.:> tr2')
                     let updated = S.mkStruct cr' (Ctx.empty Ctx.:> e1' Ctx.:> e2' )
                     let packed  = R.App (E.PackAny (CT.StructRepr cr') updated)
                     return $ packed

                   _ -> fail "unhandled coerceArg, variant with more than 1 field")
            (loop (n+1) variants e)
  res <- loop 0 variants dat
  return $ S.mkStruct (Ctx.empty Ctx.:> CT.NatRepr Ctx.:> CT.AnyRepr)
                      (Ctx.empty Ctx.:> idx Ctx.:> res)



-- If we are calling a polymorphic function, we may need to coerce the type of the argument
-- so that it has the right type.
coerceArg :: forall h s ret. HasCallStack => M.Ty -> (M.Ty, MirExp s) -> MirGenerator h s ret (MirExp s)
coerceArg ty (aty, e@(MirExp tr e0)) | M.isPoly ty = do
  case (ty,aty,tr) of
     (M.TyParam _,_, _) -> return $ packAny e
     (M.TyRef ty1 _mut, M.TyRef aty1 _, _) -> coerceArg ty1 (aty1, e)
     (M.TyAdt adt substs,   -- polymorphic type of the parameter
      M.TyAdt _   asubsts,  -- actual Mir type of the argument, including actual substitution
      CT.StructRepr (Ctx.Empty Ctx.:> CT.NatRepr Ctx.:> CT.AnyRepr)) -> do
        tagged <- coerceAdt True adt substs asubsts e0
        return (MirExp taggedUnionType tagged)

     _ -> fail $ "poly type " ++ show (pretty ty) ++ " unsupported in fcn call for " ++ show tr

-- leave all others alone
               | otherwise = return e

-- Coerce the return type of a polymorphic function 
coerceRet :: forall h s ret. HasCallStack =>
            M.Ty             -- ^ declared return type of the fcn
         -> (M.Ty, MirExp s) -- ^ expected return type by the context, expression to coerce
         -> MirGenerator h s ret (MirExp s)
coerceRet ty (aty, e@(MirExp tr e0)) | M.isPoly ty = do
   case (ty,aty,tr) of 
     (M.TyParam _,_,CT.AnyRepr) -> do
        unpackAny (tyToRepr aty) e
     (M.TyRef ty1 _mut, M.TyRef aty2 _,_) -> coerceRet ty1 (aty2,e)
     (M.TyAdt adt substs,   -- polymorphic type of the parameter
      M.TyAdt _   asubsts,  -- actual Mir type of the argument, including actual substitution
      CT.StructRepr (Ctx.Empty Ctx.:> CT.NatRepr Ctx.:> CT.AnyRepr)) -> do
        tagged <- coerceAdt False adt substs asubsts e0
        return (MirExp taggedUnionType tagged)
     _ -> fail $ "poly type " ++ show (pretty ty) ++
                 " unsupported in fcn return for " ++ show tr
-- leave all others alone
                   | otherwise = return e


-- regular function calls: closure calls & dynamic trait method calls handled later
doCall :: HasCallStack => M.DefId -> [M.Operand] -> Maybe (M.Lvalue, M.BasicBlockInfo) -> MirGenerator h s ret a
doCall funid cargs cdest = do
    hmap <- use handleMap
    _tmap <- use traitMap
    case cdest of 
      (Just (dest_lv, jdest))

        | Just (MirHandle _ (M.FnSig args ret) fhandle) <- lookupHandle funid hmap -> do
            exps <- mapM evalOperand cargs
            let fargctx = FH.handleArgTypes fhandle
            let fret    = FH.handleReturnType fhandle
            cexps <- zipWithM coerceArg args (zip (map M.typeOf cargs) exps)
            exp_to_assgn cexps $ \ctx asgn -> do
              case (testEquality ctx fargctx) of
                Just Refl -> do
                  ret_e <- G.call (S.app $ E.HandleLit fhandle) asgn
                  cret_e <- coerceRet ret ((M.typeOf dest_lv), MirExp fret ret_e)
                  assignLvExp dest_lv Nothing cret_e
                  jumpToBlock jdest
                _ -> fail $ "type error in call: args " ++ (show ctx) ++ " vs function params "
                                 ++ show fargctx ++ " while calling " ++ show funid

         | Just _fname <- M.isCustomFunc funid -> do
            doCustomCall funid cargs dest_lv jdest


         | otherwise -> fail $ "Don't know how to call " ++ show funid

      Nothing -> fail "bad dest in doCall"

-- Method/trait calls
      -- 1. translate `traitObject` -- should be a Ref to a tuple
      -- 2. the first element should be Ref Any. This is the base value. Unpack the Any behind the Ref and stick it back into a Ref.
      -- 3. the second element should be a Struct that matches the context repr in `tis^.vtableTyRepr`.
      -- 4. index into that struct with `midx` and retrieve a FunctionHandle value
      -- 5. Call the FunctionHandle passing the reference to the base value (step 2), and the rest of the arguments (translated)

methodCall :: HasCallStack => TraitName -> MethName -> M.Operand -> [M.Operand] -> Maybe (M.Lvalue, M.BasicBlockInfo) -> MirGenerator h s ret a
methodCall traitName methodName traitObject args (Just (dest_lv,jdest)) = do
  (Some tis) <- traitImplsLookup traitName
  case Map.lookup methodName $ tis^.methodIndex of
    Nothing -> fail $ Text.unpack $ Text.unwords $ ["Error while translating a method call: no such method ",
                                                    M.idText methodName, " in trait ", M.idText traitName]
    Just (Some midx) -> do
      let vtableRepr = tis^.vtableTyRepr
      let fnRepr     = vtableRepr Ctx.! midx
      (MirExp tp e) <- evalOperand traitObject
      exps          <- mapM evalOperand args
      case testEquality tp CT.AnyRepr of 
        Just Refl -> do
          let objTy     = CT.StructRepr (Ctx.Empty Ctx.:> CT.AnyRepr Ctx.:> CT.StructRepr vtableRepr)
          let e1        = R.App $ E.UnpackAny objTy e
          let e2        = R.App $ E.FromJustValue objTy e1 (R.App (E.TextLit (fromString "unpack to struct")))
          let _baseValue = R.App $ E.GetStruct e2 Ctx.i1of2 CT.AnyRepr 
          let vtable    = R.App $ E.GetStruct e2 Ctx.i2of2 (CT.StructRepr vtableRepr)
          let fn        = R.App $ E.GetStruct vtable midx fnRepr
          case fnRepr of
             CT.FunctionHandleRepr fargctx fret ->
                exp_to_assgn exps $ \ctx asgn -> do
                  case (testEquality ctx fargctx ) of
                     Just Refl -> do
                       ret_e <- G.call fn asgn
                       assignLvExp dest_lv Nothing (MirExp fret ret_e)
                       jumpToBlock jdest
                     Nothing -> fail $ "type error in call: args " ++ (show ctx) ++ " vs function params "
                                 ++ show fargctx ++ " while calling " ++ show fn
             _ -> fail $ "type error in call: " ++ show fnRepr ++ " while calling " ++ show fn
                        
        Nothing -> fail $ unwords $ ["Type error when calling ", show methodName, " type is ", show tp]
methodCall _ _ _ _ _ = fail "No destination for method call"


transTerminator :: HasCallStack => M.Terminator -> CT.TypeRepr ret -> MirGenerator h s ret a
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

transTerminator (M.Call (M.OpConstant (M.Constant _ (M.Value (M.ConstFunction funid funsubsts)))) cargs cretdest _) _ = do
    traceM $ show (vcat [text "At function call of ", pretty funid, text " with arguments ", pretty cargs, 
                   text "with type parameters: ", pretty funsubsts])
             
    case (funsubsts, cargs) of
      (Just (M.TyDynamic traitName) : _, tobj:_args) -> -- this is a method call on a trait object
        methodCall traitName funid tobj cargs cretdest
      _ -> -- this is a normal function call
        doCall funid cargs cretdest  -- cleanup ignored
        
transTerminator (M.Assert _cond _expected _msg target _cleanup) _ =
    jumpToBlock target -- FIXME! asserts are ignored; is this the right thing to do? NO!
transTerminator (M.Resume) tr =
    doReturn tr -- resume happens when unwinding
transTerminator (M.Drop _dl dt _dunwind) _ =
    jumpToBlock dt -- FIXME! drop: just keep going
transTerminator t _tr =
    fail $ "unknown terminator: " ++ (show t)


--- translation of toplevel glue ---

tyToFreshReg :: HasCallStack => M.Ty -> MirGenerator h s ret (Some (R.Reg s))
tyToFreshReg t = do
    tyToReprCont t $ \tp ->
        Some <$> G.newUnassignedReg tp

buildIdentMapRegs_ :: HasCallStack => Set Text.Text -> [(Text.Text, M.Ty)] -> MirGenerator h s ret (VarMap s)
buildIdentMapRegs_ addressTakenVars pairs = foldM f Map.empty pairs
  where
  f map_ (varname, varty)
    | varname `Set.member` addressTakenVars =
        tyToReprCont varty $ \tp ->
           do reg <- G.newUnassignedReg (MirReferenceRepr tp)
              return $ Map.insert varname (Some (VarReference reg)) map_
    | otherwise =
        do Some r <- tyToFreshReg varty
           return $ Map.insert varname (Some (VarRegister r)) map_

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
buildIdentMapRegs (M.MirBody vars blocks) _argvars =
    buildIdentMapRegs_ addressTakenVars (map (\(M.Var name _ ty _ _) -> (name,ty)) vars) -- (vars ++ argvars))
 where
   addressTakenVars = mconcat (map addrTakenVars blocks)

buildLabelMap :: forall h s ret. M.MirBody -> MirGenerator h s ret (LabelMap s)
buildLabelMap (M.MirBody _ blocks) = Map.fromList <$> mapM buildLabel blocks

buildLabel :: forall h s ret. M.BasicBlock -> MirGenerator h s ret (M.BasicBlockInfo, R.Label s)
buildLabel (M.BasicBlock bi _) = do
    lab <- G.newLabel
    return (bi, lab)

initFnState :: AdtMap
            -> TraitMap 
            -> [(Text.Text, M.Ty)]
            -> CT.CtxRepr args 
            -> Ctx.Assignment (R.Atom s) args
            -> HandleMap
            -> FnState s
initFnState am tm vars argsrepr args hmap =
    FnState (go (reverse vars) argsrepr args Map.empty) (Map.empty) hmap am tm
    where go :: [(Text.Text, M.Ty)] -> CT.CtxRepr args -> Ctx.Assignment (R.Atom s) args -> VarMap s -> VarMap s
          go [] ctx _ m
            | Ctx.null ctx = m
            | otherwise = error "wrong number of args"
          go ((name,ti):ts) ctx asgn m =
            unfold_ctx_assgn ti ctx asgn $ \(Some atom) ctx' asgn' ->
                 go ts ctx' asgn' (Map.insert name (Some (VarAtom atom)) m)


-- do the statements and then the terminator
translateBlockBody :: HasCallStack => CT.TypeRepr ret -> M.BasicBlockData -> MirGenerator h s ret a
translateBlockBody tr (M.BasicBlockData stmts terminator) = (mapM_ transStatement stmts) >> (transTerminator terminator tr)

--
registerBlock :: CT.TypeRepr ret -> M.BasicBlock -> MirGenerator h s ret ()
registerBlock tr (M.BasicBlock bbinfo bbdata)  = do
    lm <- use labelMap
    case (Map.lookup bbinfo lm) of
      Just lab -> G.defineBlock lab (translateBlockBody tr bbdata)
      _ -> fail "bad label"


-- | Translate a MIR function, returning a jump expression to its entry block
-- argvars are registers
-- The first block in the list is the entrance block
genFn :: HasCallStack => M.Fn -> CT.TypeRepr ret -> MirGenerator h s ret (R.Expr MIR s ret)
genFn (M.Fn _fname argvars _fretty body) rettype = do
  lm <- buildLabelMap body
  labelMap .= lm
  vm' <- buildIdentMapRegs body argvars
  varMap %= Map.union vm'
  let (M.MirBody _vars blocks@(enter : _)) = body 
  mapM_ (registerBlock rettype) blocks
  let (M.BasicBlock bbi _) = enter
  lm <- use labelMap
  case (Map.lookup bbi lm) of
    Just lbl -> G.jump lbl
    _ -> fail "bad thing happened"

transDefine :: forall h. HasCallStack =>
  AdtMap ->
  TraitMap ->
  HandleMap ->
  M.Fn ->
  ST h (Text, Core.AnyCFG MIR)
transDefine am tm hmap fn@(M.Fn fname fargs _ _) =
  case (Map.lookup fname hmap) of
    Nothing -> fail "bad handle!!"
    Just (MirHandle _ _ (handle :: FH.FnHandle args ret)) -> do
      let argtups  = map (\(M.Var n _ t _ _) -> (n,t)) fargs
      let argtypes = FH.handleArgTypes handle
      let rettype  = FH.handleReturnType handle
      let def :: G.FunctionDef MIR handle FnState args ret
          def inputs = (s,f) where
            s = initFnState am tm argtups argtypes inputs hmap
            f = genFn fn rettype
      (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos handle def
      case SSA.toSSA g of
        Core.SomeCFG g_ssa -> return (M.idText fname, Core.AnyCFG g_ssa)


-- | Allocate method handles for each of the functions in the Collection
mkHandleMap :: HasCallStack => FH.HandleAllocator s -> [M.Fn] -> ST s HandleMap
mkHandleMap halloc fns = Map.fromList <$> mapM (mkHandle halloc) fns where
    mkHandle :: FH.HandleAllocator s -> M.Fn -> ST s (MethName, MirHandle)
    mkHandle halloc (M.Fn fname fargs fretty _fbody) =
        tyListToCtx (map M.typeOf fargs) $ \argctx ->  tyToReprCont fretty $ \retrepr -> do
            h <- FH.mkHandle' halloc (FN.functionNameFromText (M.idText fname)) argctx retrepr
            let mh = MirHandle fname (M.FnSig (map M.typeOf fargs) fretty) h
            return (fname, mh)


-- | transCollection: translate all functions
transCollection :: HasCallStack => M.Collection -> FH.HandleAllocator s -> ST s (Map Text (Core.AnyCFG MIR))
transCollection col halloc = do
    let cstyleAdts = List.map _adtname (List.filter isCStyle (col^.M.adts))
    let col1 = markCStyle cstyleAdts col 
    let am = Map.fromList [ (nm, vs) | M.Adt nm vs <- col1^.M.adts ]
    hmap <- mkHandleMap halloc (col1^.M.functions)
    (tm, morePairs) <- buildTraitMap col1 halloc hmap
    pairs <- mapM (transDefine am tm hmap) (col1^.M.functions)
    return $ Map.fromList (pairs ++ morePairs)

----------------------------------------------------------------------------------------------------------
-- * Traits

-- | Build the mapping from traits and types that implement them to VTables
-- This involves defining new functions that "wrap" (and potentially unwrap) the specific implementations,
-- providing a uniform type for the trait methods. 
buildTraitMap :: M.Collection -> FH.HandleAllocator s -> HandleMap -> ST s (TraitMap, [(Text, Core.AnyCFG MIR)])
buildTraitMap col halloc hmap = do

    -- find the crucible types of all of the methods for each trait
    -- looking at the generic trait declarations
    let decls :: Map TraitName (Some TraitDecl)
        decls = foldr (\ trait@(M.Trait tname _) m ->
                            Map.insert tname (mkTraitDecl trait) m)
                 Map.empty (col^.M.traits)

    -- find all methods that are the implementations of traits
    let impls :: [(MethName, TraitName, MirHandle)]
        impls = Maybe.mapMaybe (getTraitImplementation (col^.M.traits)) (Map.assocs hmap)

    --traceM $ ("\ndecls dom: " ++ show decls)
    --traceM $ ("\nimpls are:" ++ show impls)

    -- wrap the implementations to make the vtable
    pairs <- forM (Map.assocs decls) $ \(trait, Some decl@(TraitDecl ctx methodIndex)) -> do
                     let implHandles = [(methName,mirHandle) | (methName, tn, mirHandle) <- impls, trait == tn]
                     pairs <- forM (groupByType implHandles) $ \(typeName, implHandlesByType) -> do
                                    (vtable, cfgs) <- buildWrappedTraitMethods halloc trait decl implHandlesByType
                                    return (Map.singleton typeName vtable, cfgs)
                     let vtables = mconcat (map fst pairs)
                     let cfgs    = mconcat (map snd pairs)
                     return ((trait, Some (TraitImpls ctx methodIndex vtables)), cfgs)

    let traitMap = TraitMap $ Map.fromList (map fst pairs)

    return (traitMap, concat $ map snd pairs)

groupByType :: [(MethName, MirHandle)] -> [(TypeName, [(MethName,MirHandle)])]
groupByType meths = 
     let thisType (M.FnSig (M.TyRef ty _:_) _ret) = typeName ty
         thisType (M.FnSig (ty:_) _ret) = typeName ty
         thisType (M.FnSig []     _ret) = error "traits must have an arg type"

         impls = map (\(methName, mh@(MirHandle _ sig _)) -> (thisType sig, (methName,mh))) meths

     in
    
      -- convert double association list to double map
     let grouped = Map.assocs $ foldr (\(ty,(mn,h)) -> Map.insertWith (++) ty [(mn,h)]) Map.empty impls

     in

       --trace ("\nimpls:" ++ show impls)
       --trace ("\ngrouped:"++ show grouped)
       grouped



-- Part of the information we need for a trait implementation
data TraitDecl ctx =
   TraitDecl (CT.CtxRepr ctx)                       -- vtable type 
             (Map MethName (Some (Ctx.Index ctx)))  -- indices into the vtable


instance Show (TraitDecl ctx) where
  show (TraitDecl _vtable mm) =
    "TraitDecl(" ++ show (Map.keys mm) ++ ")"
instance ShowF TraitDecl

-- Aux data structure for `mkTraitDecl`
data MethRepr ty where
  MethRepr :: MethName -> CT.TypeRepr ty -> MethRepr ty
getReprName :: MethRepr ty -> MethName
getReprName (MethRepr name _) = name
getReprTy :: MethRepr ty -> CT.TypeRepr ty
getReprTy (MethRepr _ ty) = ty



-- | Construct 'TraitDecl' for each trait. Involves finding data
-- types that implement a given trait and functions that implement
-- each method for a data type and building VTables for each
-- data-type/trait pair.
mkTraitDecl :: M.Trait -> Some TraitDecl
mkTraitDecl (M.Trait _tname titems) = do
  let meths = [(mname, tsig) |(M.TraitMethod mname tsig) <- titems]

  let go :: Some (Ctx.Assignment MethRepr)
         -> (MethName, M.FnSig)
         -> Some (Ctx.Assignment MethRepr)
      go (Some tr) (mname, M.FnSig argtys retty) =
          case (tyToRepr retty, tyListToCtx argtys Some) of
                (Some retrepr, Some argsrepr) ->
                   Some (tr `Ctx.extend` MethRepr mname (CT.FunctionHandleRepr argsrepr retrepr))

  case foldl go (Some Ctx.empty) meths of
    Some (mctxr :: Ctx.Assignment MethRepr ctx) ->
        let
            ctxr    :: Ctx.Assignment CT.TypeRepr ctx
            ctxr    = Ctx.fmapFC getReprTy mctxr
            --
            midx    :: Map MethName (Some (Ctx.Index ctx))
            midx    = Ctx.forIndex
                          (Ctx.size mctxr)
                          (\mp idx -> Map.insert (getReprName (mctxr Ctx.! idx)) (Some idx) mp)
                          Map.empty

        in Some (TraitDecl ctxr midx) 


lookupMethodType :: Map TraitName (Some TraitDecl) -> TraitName -> MethName ->
    (forall ctx args ret. CT.CtxRepr ctx -> CT.CtxRepr args -> CT.TypeRepr ret -> a) -> a
lookupMethodType traitDecls traitName implName k =
    case Map.lookup traitName traitDecls  of
      Nothing -> error "Internal error"
      Just (Some (TraitDecl vreprs meths)) -> case Map.lookup implName meths of
         Nothing -> error "Internal error"
         Just (Some idx) -> case (vreprs Ctx.! idx) of
           (CT.FunctionHandleRepr (argsr Ctx.:> CT.AnyRepr) retr) -> k vreprs argsr retr
           _ -> error "Internal error"
  

{-  Example of WRAPPING METHODS

    trait Foo {
       f (&self) -> u32     <-  wrapperName == "wrapped_f"
       g (&self) -> u32
    } 

    impl A {
       fn f (&self) { 3 }    <- implName == "f"
       fn g (&self) { 4 }
    }

    f (x : A) { 3 }

    wrapped_f (Dyn x) -> u32 = 
       unPack x as (  y :: A ,  { wrapped_f :: Dyn -> u32,  wrapped_g :: Dyn -> u 32 } )
       f y

    wrapped_g (Dyn x) -> u32 = 
       unPack x as (  y :: A ,  { wrapped_f :: Dyn -> u32,  wrapped_g :: A -> u 32 } )
       g y

-}


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
buildWrappedTraitMethods halloc traitName (TraitDecl ctxr _idxs) meths = do
 
   -- allocate new function handles for the trait with the generic type
   let go :: forall ty. Ctx.Index ctx ty -> CT.TypeRepr ty -> ST s (WrappedMethod ty)
       go idx (CT.FunctionHandleRepr argsr retr) = do
          let i = Ctx.indexVal idx
          let (implName, implHandle) = if i < length meths then meths !! i else error "buildWrappedTraitMethods"
          let wrappedName = Text.pack "wrapped" <> (M.idText traitName) <> "::" <> M.idText implName
          nhandle <- FH.mkHandle' halloc (FN.functionNameFromText wrappedName) argsr retr
          return $ WrappedMethod implName implHandle wrappedName (FnValue nhandle)
       go _ _ = error "No MirValue for nonfunctions"

   full_vtable <- Ctx.traverseWithIndex go ctxr

   -- bind functions to go with those handles
   let defineCFG :: forall ty. WrappedMethod ty -> ST s (Text,Core.AnyCFG MIR)
       defineCFG (WrappedMethod _implName   (MirHandle _ _sig (implHandle :: FH.FnHandle implArgs implRet))
                                wrappedName (FnValue (handle :: FH.FnHandle args ret))) = do

         --traceM ("\n wrapping " ++ Text.unpack implName ++ show (FH.handleArgTypes implHandle))
         let argsr = FH.handleArgTypes   handle
         let retr  = FH.handleReturnType handle
         -- make sure that there is at least one argument to the function
         -- and that the wrapped function is almost the same type as the impl function
         case (FH.handleArgTypes implHandle :: CT.CtxRepr implArgs) of
           Ctx.Empty -> error "methods must take self"
           (rest Ctx.:> argr) -> case testEquality (CT.FunctionHandleRepr (rest Ctx.:> CT.AnyRepr) (FH.handleReturnType implHandle))
                                                   (CT.FunctionHandleRepr argsr retr) of
              Nothing   -> error "types don't match"
              Just Refl -> do

                 -- type of trait implementation
                   let objTyRepr = CT.StructRepr (Ctx.Empty Ctx.:> CT.AnyRepr Ctx.:> CT.StructRepr ctxr)

                   let fnDef :: G.FunctionDef MIR h FnState args ret
                       fnDef (xs Ctx.:> x) = (res, body) where
                          res  = FnState Map.empty Map.empty Map.empty Map.empty (TraitMap Map.empty)   -- CHECK THIS
                          body =
                            let yo = R.App $ E.FromJustValue objTyRepr (R.App (E.UnpackAny objTyRepr (R.AtomExpr x)))
                                            (R.App (E.TextLit (Text.pack ("bad wrapper :" <> (show objTyRepr)))))
                                y1  = R.App $ E.GetStruct yo Ctx.i1of2 CT.AnyRepr
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

   


-- | Construct 'TraitImpls' for each trait. Involves finding data
-- types that implement a given trait and functions that implement
-- each method for a data type and building VTables for each
-- data-type/trait pair.
mkTraitImplementations ::
         M.Collection
      -> [(MethName, TraitName, TypeName, MirHandle)]
      -> M.Trait
      -> Some TraitImpls
mkTraitImplementations _col trs trait@(M.Trait tname titems) =
  let impls :: Map TypeName (Map MethName MirHandle)
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
            ctxr    :: Ctx.Assignment CT.TypeRepr ctx
            ctxr    = Ctx.fmapFC getReprTy mctxr
            --
            midx    :: Map MethName (Some (Ctx.Index ctx))
            midx    = Ctx.forIndex
                          (Ctx.size mctxr)
                          (\mp idx -> Map.insert (getReprName (mctxr Ctx.! idx)) (Some idx) mp)
                          Map.empty

            -- replace the (Map MethName MirHandle) with a
            -- an assignment from the method name to the appropriate function value
            vtables :: Map TypeName (Ctx.Assignment MirValue ctx)
            vtables = Map.mapWithKey 
                        (\ ty (mmap :: Map MethName MirHandle) ->
                           Ctx.generate (Ctx.size mctxr)
                                        (\idx ->
                                            let (MethRepr name cty) = mctxr Ctx.! idx in
                                            case Map.lookup name mmap of
                                                    Just (MirHandle _ _ fh) -> case testEquality cty (FH.handleType fh) of
                                                        Just Refl -> FnValue fh 
                                                        Nothing -> error $ "type mismatch between trait declr " ++ show (pretty cty)
                                                                   ++  " and instance type " ++ show (pretty (FH.handleType fh))
                                                    Nothing -> error $ "Cannot find method " ++ show name ++ " for type " ++ show ty
                                                                       ++ " in trait " ++ show tname)) impls
        in Some (TraitImpls ctxr midx vtables) 

  where 
        go :: Some (Ctx.Assignment MethRepr) -> (MethName, M.FnSig) -> Some (Ctx.Assignment MethRepr)
        go (Some tr) (mname, M.FnSig argtys retty) =
          case (tyToRepr retty, tyListToCtx argtys Some) of
                (Some retrepr, Some argsrepr) ->
                   Some (tr `Ctx.extend` MethRepr mname (CT.FunctionHandleRepr argsrepr retrepr))






 
-- | Find the mapping from types to method handles for *this* trait
thisTraitImpls :: M.Trait -> [(MethName,TraitName,TypeName,MirHandle)] -> Map TypeName (Map MethName MirHandle)
thisTraitImpls (M.Trait trait _) trs = do
  -- pull out method handles just for this trait
  let impls = [ (typeName, (methName, handle)) | (methName, traitName, typeName, handle) <- trs, traitName == trait ]
  -- convert double association list to double map
  foldr (\(ty,(mn,h)) -> Map.insertWith Map.union ty (Map.singleton mn h)) Map.empty impls




--------------------------------------------------------------------------------------------------------------------------
--- Custom stuff
--

-- if we want to be able to insert custom information just before runtime, the below can be dynamic, and baked into the Override monad.

customtyToRepr :: M.CustomTy -> Some CT.TypeRepr
customtyToRepr (M.BoxTy t) = tyToRepr t -- Box<T> is the same as T
--customtyToRepr (M.VecTy t) = tyToRepr $ M.TySlice t -- Vec<T> is the same as [T]
customtyToRepr (M.IterTy t) = tyToRepr $ M.TyTuple [M.TySlice t, M.TyUint M.USize]
      -- Iter<T> => ([T], nat). The second component is the current index into the array, beginning at zero.
-- Implement C-style enums as single integers
customtyToRepr (CEnum _adt) = Some CT.IntegerRepr
customtyToRepr ty = error ("FIXME: unimplement custom type: " ++ M.pprint ty)

mkNone :: MirExp s
mkNone =
    buildTuple [MirExp CT.NatRepr (S.app $ E.NatLit 0), packAny $ buildTuple []]

mkSome :: MirExp s -> MirExp s
mkSome a = buildTuple [MirExp CT.NatRepr (S.app $ E.NatLit 1), packAny $ buildTuple [a]]

extractVecTy :: forall a t. CT.TypeRepr t -> (forall t2. CT.TypeRepr t2 -> a) -> a
extractVecTy (CT.VectorRepr a) f = f a
extractVecTy _ _ = error "Expected vector type in extraction"

doCustomCall :: HasCallStack => M.DefId -> [M.Operand] -> M.Lvalue -> M.BasicBlockInfo -> MirGenerator h s ret a
doCustomCall fname ops lv dest
  | Just "boxnew" <- M.isCustomFunc fname,
  [op] <- ops =  do
        e <- evalOperand op
        assignLvExp lv Nothing e
        jumpToBlock dest

  | Just "slice_tovec" <- M.isCustomFunc fname,
  [op] <- ops = do
        e <- evalOperand op
        assignLvExp lv Nothing e
        jumpToBlock dest

  | Just "vec_asmutslice" <- M.isCustomFunc fname,
  [op] <- ops = do
        ans <- evalOperand op
        assignLvExp lv Nothing ans
        jumpToBlock dest

 | Just "index" <- M.isCustomFunc fname,
    [op1, op2] <- ops = do
        ans <- evalLvalue (M.LProjection (M.LvalueProjection (M.lValueofOp op1) (M.Index op2)))
        assignLvExp lv Nothing ans
        jumpToBlock dest

 | Just "vec_fromelem" <- M.isCustomFunc fname,
    [elem, u] <- ops = do
        ans <- buildRepeat_ elem u
        assignLvExp lv Nothing ans
        jumpToBlock dest

 | Just "into_iter" <- M.isCustomFunc fname, -- vec -> (vec, 0)
    [v] <- ops = do
        vec <- evalOperand v
        let t = buildTuple [vec, MirExp (CT.NatRepr) (S.app $ E.NatLit 0)]
        assignLvExp lv Nothing t
        jumpToBlock dest

 | Just "iter_next" <- M.isCustomFunc fname, [o] <- ops = do
     iter <- evalOperand o -- iter = struct (vec, pos of nat). if pos < size of vec, return (Some(vec[pos]), (vec, pos+1)). otherwise return (None, (vec, pos))
     (MirExp (CT.VectorRepr elemty) iter_vec) <- accessAggregate iter 0
     (MirExp CT.NatRepr iter_pos) <- accessAggregate iter 1
     let is_good = S.app $ E.NatLt iter_pos (S.app $ E.VectorSize iter_vec)
         good_ret_1 = mkSome $ MirExp elemty $ S.app $ E.VectorGetEntry elemty iter_vec iter_pos
         good_ret_2 = buildTuple [MirExp (CT.VectorRepr elemty) iter_vec, MirExp CT.NatRepr (S.app $ E.NatAdd iter_pos (S.app $ E.NatLit 1))]
         good_ret = buildTuple [good_ret_1, good_ret_2]

         bad_ret_1 = mkNone
         bad_ret_2 = buildTuple [MirExp (CT.VectorRepr elemty) iter_vec, MirExp CT.NatRepr iter_pos]
         bad_ret = buildTuple [bad_ret_1, bad_ret_2]

     ifteAny is_good
             (assignLvExp lv Nothing good_ret >> jumpToBlock' dest)
             (assignLvExp lv Nothing bad_ret >> jumpToBlock' dest)

 | Just "iter_map" <- M.isCustomFunc fname, [iter, closure] <- ops = do
     iter_e <- evalOperand iter
     closure_e <- evalOperand closure
     iter2 <- performMap (M.typeOf iter) iter_e (M.typeOf closure) closure_e
     assignLvExp lv Nothing iter2
     jumpToBlock dest

 | Just "iter_collect" <- M.isCustomFunc fname, [o] <- ops = do
     iter <- evalOperand o
     v <- accessAggregate iter 0
     assignLvExp lv Nothing v
     jumpToBlock dest


 | Just "call" <- M.isCustomFunc fname, -- perform call of closure
 [o1, o2] <- ops = do

     argtuple <- evalOperand o2
     case (M.typeOf o1, M.typeOf o2) of
       (M.TyClosure defid clargsm, M.TyTuple _args) -> do
         closure_pack <- evalOperand o1
         let clargs = filterMaybes clargsm
         clty <- buildClosureType defid clargs
         unpack_closure <- unpackAny clty closure_pack
         handle <- accessAggregate unpack_closure 0
         extra_args <- getAllFields argtuple
         case handle of
           MirExp hand_ty handl ->
               case hand_ty of
                   CT.FunctionHandleRepr fargctx fretrepr ->
                    exp_to_assgn (closure_pack : extra_args) $ \ctx asgn ->
                        case (testEquality ctx fargctx) of
                          Just Refl -> do
                            ret_e <- G.call handl asgn
                            assignLvExp lv Nothing (MirExp fretrepr ret_e)
                            jumpToBlock dest
                          Nothing ->
                            fail "type mismatch in call"
                   _ -> fail $ "bad handle type"

       _ -> fail $ "unexpected type in Fn::call!" ++ show (pretty (M.typeOf o1)) ++ " " ++  show (pretty (M.typeOf o2))

 | Just cf <- M.isCustomFunc fname = fail $ "custom function not handled: " ++ (show cf)

 | otherwise =  fail $ "doCustomCall unhandled: " ++ (show $ fname)

transCustomAgg :: M.CustomAggregate -> MirGenerator h s ret (MirExp s) -- depreciated
transCustomAgg (M.CARange _ty f1 f2) = evalRval (M.Aggregate M.AKTuple [f1,f2])

performUntil :: R.Expr MIR s CT.NatType -> (R.Reg s CT.NatType -> MirGenerator h s ret ()) -> MirGenerator h s ret ()
performUntil n f = do -- perform (f i) for i = 0..n (not inclusive). f takes as input a nat register (but shouldn't increment it)
    ind <- G.newReg $ S.app $ E.NatLit 0
    G.while (PL.InternalPos, test n ind) (PL.InternalPos, (run_incr f) ind)

   where test :: R.Expr MIR s CT.NatType -> R.Reg s CT.NatType -> MirGenerator h s ret (R.Expr MIR s CT.BoolType)
         test n r = do
             i <- G.readReg r
             return $ S.app $ E.NatLt i n

         run_incr :: (R.Reg s CT.NatType -> MirGenerator h s ret ()) -> (R.Reg s CT.NatType -> MirGenerator h s ret ())
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
            CT.FunctionHandleRepr fargctx fretrepr ->
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
      (M.TyCustom (M.IterTy _t), M.TyClosure defid clargsm) -> do
          let clargs = filterMaybes clargsm
          clty <- buildClosureType defid clargs
          unpack_closure <- unpackAny clty closure
          handle <- accessAggregate unpack_closure 0
          (MirExp (CT.VectorRepr elemty) iter_vec) <- accessAggregate iter 0
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
              return $ buildTuple [MirExp (CT.VectorRepr elemty) new_vec, iter_pos] -- we keep iter_pos the same as before. so if I called next() on an iterator and then map(), I'm where I left off. I assume this is right

      _ -> fail "bad type"

------------------------------------------------------------------------------------------------
