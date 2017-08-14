{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Mir.Trans where
import qualified Mir.Mir as M
import Control.Monad
import Control.Monad.ST
import Control.Lens hiding (op)
import System.IO.Unsafe
import qualified Data.Text as Text
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.FunctionHandle as FH
import qualified Lang.Crucible.ProgramLoc as PL
import qualified Lang.Crucible.FunctionName as FN
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.SSAConversion as SSA
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Syntax as S
import qualified Data.Map.Strict as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Lang.Crucible.Types as CT
import qualified Numeric.Natural as Nat
import qualified Data.Vector as V
import qualified Data.Parameterized.Context as Ctx 
import qualified Text.Regex as Regex
import qualified Text.Regex.Base as Regex
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import GHC.TypeLits



-- Basic definitions. 
--
--  Varmap maps identifiers to registers (if the id corresponds to a local variable), or an atom (if the id corresponds to a function argument)
--  LabelMap maps identifiers to labels of their corresponding basicblock
--  HandleMap maps identifiers to their corresponding function handle
--


type VarMap s = Map.Map Text.Text (Either (Some (R.Reg s)) (Some (R.Atom s)))
type LabelMap s = Map.Map M.BasicBlockInfo (R.Label s)
data FnState s = FnState { _varmap :: !(VarMap s),
                           _labelmap :: !(LabelMap s),   
                           _handlemap :: !(Map.Map Text.Text MirHandle) }

varmap :: Simple Lens (FnState s) (VarMap s)
varmap = lens _varmap (\s v -> s { _varmap = v})

labelmap :: Simple Lens (FnState s) (LabelMap s)
labelmap = lens _labelmap (\s v -> s { _labelmap = v})

handlemap :: Simple Lens (FnState s) (Map.Map Text.Text MirHandle)
handlemap = lens _handlemap (\s v -> s { _handlemap = v})


type MirGenerator h s ret = G.Generator h s (FnState) ret
type MirEnd h s ret = G.End h s (FnState) ret

-- The main data type for values, bundling the term-lvel type tp along with a crucible expression of type tp.
data MirExp s where
    MirExp :: CT.TypeRepr tp -> R.Expr s tp -> MirExp s

instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)

data MirHandle where
    MirHandle :: CT.CtxRepr init -> CT.TypeRepr ret -> FH.FnHandle init ret -> MirHandle

instance Show MirHandle where
    show (MirHandle a b c) = unwords [show a, show b, show c]



-----------
   
fieldToRepr :: M.Field -> M.Ty -- convert field to type. Perform the corresponding subtitution if field is a type param.
fieldToRepr (M.Field _ t substs) = 
    case t of
      M.TyParam i -> case substs !! (fromInteger i) of
                        Nothing -> error "bad subst"
                        Just ty -> ty
      ty -> ty

variantToRepr :: M.Variant -> Some CT.TypeRepr
variantToRepr (M.Variant vn vd vfs vct) =
    tyListToCtx (map fieldToRepr vfs) $ \repr -> Some (CT.StructRepr repr) 

adtToRepr :: M.Adt -> Some CT.TypeRepr
adtToRepr (M.Adt adtname variants) = Some $ taggedUnionType

taggedUnionType :: CT.TypeRepr (CT.StructType (Ctx.EmptyCtx Ctx.::> CT.NatType Ctx.::> CT.AnyType))
taggedUnionType = CT.StructRepr $ Ctx.empty Ctx.%> CT.NatRepr Ctx.%> CT.AnyRepr

-- Type translation and type-level list utilities.
-- Base types are encoded straightforwardly (except for Usize, which is a crucible nat).
-- References have the exact same semantics as their referent type.
-- Arrays and slices are both crucible vectors; no difference between them.
-- Tuples are crucible structs.
-- Non-custom ADTs are encoded as a tagged union [Nat, Any]. The first component records which injection is currently being stored; the second component is the injection. Structs and enums are encoded the same -- the only difference is that structs have only one summand. (Note that this means that symbolic ADTs don't work yet, since we are working with Anys.)
--
-- Closures are encoded as Any, but are internally encoded as [Handle, arguments], where arguments is itself a tuple.
--
-- Custom type translation is on the bottom of this file.

tyToRepr :: M.Ty -> Some CT.TypeRepr
tyToRepr t = case t of
                        M.TyBool -> Some CT.BoolRepr
                        M.TyTuple ts -> tyListToCtx ts $ \repr -> Some (CT.StructRepr repr)
                        M.TySlice t ->  tyToReprCont t $ \repr -> Some (CT.VectorRepr repr)
                        M.TyArray t _ ->tyToReprCont t $ \repr -> Some (CT.VectorRepr repr)
                        M.TyAdt a -> adtToRepr a
                        M.TyInt M.USize -> Some $ CT.NatRepr
                        M.TyInt M.B8 -> Some $ CT.BVRepr (knownNat :: NatRepr 8)
                        M.TyInt M.B16 -> Some $ CT.BVRepr (knownNat :: NatRepr 16)
                        M.TyInt M.B32 -> Some $ CT.BVRepr (knownNat :: NatRepr 32)
                        M.TyInt M.B64 -> Some $ CT.BVRepr (knownNat :: NatRepr 64)
                        M.TyInt M.B128 -> Some $ CT.BVRepr (knownNat :: NatRepr 128)
                        M.TyUint M.USize -> Some $ CT.NatRepr
                        M.TyUint M.B8 -> Some $ CT.BVRepr (knownNat :: NatRepr 8)
                        M.TyUint M.B16 -> Some $ CT.BVRepr (knownNat :: NatRepr 16)
                        M.TyUint M.B32 -> Some $ CT.BVRepr (knownNat :: NatRepr 32)
                        M.TyUint M.B64 -> Some $ CT.BVRepr (knownNat :: NatRepr 64)
                        M.TyUint M.B128 -> Some $ CT.BVRepr (knownNat :: NatRepr 128)
                        M.TyRef t _ -> tyToRepr t -- references are erased! 
                        M.TyChar -> Some $ CT.BVRepr (knownNat :: NatRepr 32) -- rust chars are four bytes
                        M.TyCustom custom_t -> customtyToRepr custom_t 
                        M.TyClosure def_id substs -> Some $ CT.AnyRepr 
                        _ -> error "unknown type?"

-- As in the CPS translation, functions which manipulate types must be in CPS form, since type tags are generally hidden underneath an existential.

tyToReprCont :: forall a. M.Ty -> (forall tp. CT.TypeRepr tp -> a) -> a
tyToReprCont t f = case (tyToRepr t) of
                 Some x -> f x


tyListToCtx :: forall a.
                [M.Ty]
               -> (forall ctx. CT.CtxRepr ctx -> a)
               -> a
tyListToCtx ts f =  go (map tyToRepr ts) Ctx.empty
 where go :: forall ctx. [Some CT.TypeRepr] -> CT.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.%> tp)

reprsToCtx :: forall a. [Some CT.TypeRepr] -> (forall ctx. CT.CtxRepr ctx -> a) -> a
reprsToCtx rs f = go rs Ctx.empty
 where go :: forall ctx. [Some CT.TypeRepr] -> CT.CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.%> tp)

packBase
    :: CT.TypeRepr tp
    -> CT.CtxRepr ctx
    -> Ctx.Assignment (R.Atom s) ctx
    -> (forall ctx'. Some (R.Atom s) -> CT.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a)
    -> a
packBase ctp ctx0 asgn k =
  case Ctx.view ctx0 of
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
    :: M.Ty 
    -> CT.CtxRepr ctx 
    -> Ctx.Assignment (R.Atom s) ctx 
    -> (forall ctx'. Some (R.Atom s) -> CT.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a) 
    -> a
unfold_ctx_assgn tp ctx asgn k =
    tyToReprCont tp $ \repr ->  
        packBase repr ctx asgn k

exp_to_assgn :: [MirExp s] -> (forall ctx. CT.CtxRepr ctx -> Ctx.Assignment (R.Expr s) ctx -> a) -> a
exp_to_assgn xs = 
    go Ctx.empty Ctx.empty xs
        where go :: CT.CtxRepr ctx -> Ctx.Assignment (R.Expr s) ctx -> [MirExp s] -> (forall ctx'. CT.CtxRepr ctx' -> Ctx.Assignment (R.Expr s) ctx' -> a) -> a
              go ctx asgn [] k = k ctx asgn
              go ctx asgn ((MirExp tyr ex):vs) k = go (ctx Ctx.%> tyr) (asgn Ctx.%> ex) vs k


-- Expressions


-- Expressions: variables and constants
--

transConstVal :: Some CT.TypeRepr -> M.ConstVal -> MirGenerator h s ret (MirExp s)
transConstVal (Some (CT.BVRepr w)) (M.ConstInt i) = return $ MirExp (CT.BVRepr w) (S.app $ E.BVLit w (fromIntegral i))
transConstVal (Some (CT.BoolRepr)) (M.ConstBool b) = return $ MirExp (CT.BoolRepr) (S.litExpr b)
transConstVal (Some (CT.NatRepr)) (M.ConstInt i) = do
    let n = fromInteger i
    return $ MirExp CT.NatRepr (S.app $ E.NatLit n)
transConstVal tp cv = fail $ "fail or unimp constant: " ++ (show tp) ++ " " ++ (show cv)


lookupVar :: M.Var -> MirGenerator h s ret (MirExp s)
lookupVar (M.Var vname _ vty _) = do
    vm <- use varmap
    case (Map.lookup vname vm, tyToRepr vty) of
      (Just (Left (Some reg)), Some vtr) -> case (CT.testEquality vtr (R.typeOfReg reg)) of
                                       Just CT.Refl -> do {r <- G.readReg reg; return $ MirExp (R.typeOfReg reg) r }
                                       _ -> fail "bad type"
      (Just (Right (Some atom)), Some vtr) -> return $ MirExp (R.typeOfAtom atom) (R.AtomExpr atom) 
      _ -> error "register not found"

-- The return var in the MIR output is always "_0"

lookupRetVar :: CT.TypeRepr ret -> MirGenerator h s ret (R.Expr s ret)
lookupRetVar tr = do
    vm <- use varmap
    case (Map.lookup "_0" vm) of
      Just (Left (Some reg)) -> case (CT.testEquality tr (R.typeOfReg reg)) of
                           Just CT.Refl -> do {r <- G.readReg reg; return r}
                           _ -> fail "bad type"
      _ -> fail "reg not found in retvar"


-- Expressions: Operations and Aggregates

evalOperand :: M.Operand -> MirGenerator h s ret (MirExp s)
evalOperand (M.Consume lv) = evalLvalue lv
evalOperand (M.OpConstant (M.Constant conty conlit)) = 
    case conlit of
       M.Value constval -> transConstVal (tyToRepr conty) constval
       _ -> fail "value / promoted unimp"   

transBinOp :: M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
transBinOp bop op1 op2 = do
    me1 <- evalOperand  op1
    me2 <- evalOperand  op2
    case (me1, me2) of
      (MirExp (CT.BVRepr n) e1, MirExp (CT.BVRepr m) e2) ->
          case (testEquality n m, bop, M.arithType op1) of 
            (Just Refl, M.Add, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVAdd n e1 e2)
            (Just Refl, M.Sub, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSub n e1 e2)
            (Just Refl, M.Mul, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVMul n e1 e2)
            (Just Refl, M.Div, Just M.Unsigned) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVUdiv n e1 e2)
            (Just Refl, M.Div, Just M.Signed) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSdiv n e1 e2)
            (Just Refl, M.Rem, Just M.Unsigned) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVUrem n e1 e2)
            (Just Refl, M.Rem, Just M.Signed) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSrem n e1 e2)
            (Just Refl, M.BitXor, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVXor n e1 e2)
            (Just Refl, M.BitAnd, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVAnd n e1 e2)
            (Just Refl, M.BitOr, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVOr n e1 e2)
            (Just Refl, M.Shl, _) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVShl n e1 e2)
            (Just Refl, M.Shr, Just M.Unsigned) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVLshr n e1 e2)
            (Just Refl, M.Shr, Nothing) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVLshr n e1 e2)
            (Just Refl, M.Shr, Just M.Signed) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVAshr n e1 e2)
            (Just Refl, M.Lt, Just M.Unsigned) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVUlt n e1 e2)
            (Just Refl, M.Lt, Just M.Signed) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVSlt n e1 e2)
            (Just Refl, M.Le, Just M.Unsigned) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVUle n e1 e2)
            (Just Refl, M.Le, Just M.Signed) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVSle n e1 e2)
            (Just Refl, M.Ne, _) -> return $ MirExp (CT.BoolRepr) (S.app $ E.Not $ S.app $ E.BVEq n e1 e2)
            (Just Refl, M.Beq, _) -> return $ MirExp (CT.BoolRepr) (S.app $ E.BVEq n e1 e2)
            _ -> fail "bad binop"
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
    buildRepeat op i


-- array in haskell -> crucible array
buildArrayLit :: forall h s tp ret.  CT.TypeRepr tp -> [MirExp s] -> MirGenerator h s ret (MirExp s) 
buildArrayLit trep exps = do
    vec <- go exps V.empty 
    return $ MirExp (CT.VectorRepr trep) $  S.app $ E.VectorLit trep vec
        where go :: [MirExp s] -> V.Vector (R.Expr s tp) -> MirGenerator h s ret (V.Vector (R.Expr s tp))
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
        buildTuple [MirExp (CT.NatRepr) (S.app $ E.NatLit (fromInteger i)), packAny v ]

buildTaggedUnion' :: Integer -> MirExp s -> MirExp s -- second argument is already a struct
buildTaggedUnion' i v = 
    buildTuple [MirExp (CT.NatRepr) (S.app $ E.NatLit (fromInteger i)), packAny v ]

getAllFields :: MirExp s -> MirGenerator h s ret ([MirExp s])
getAllFields e =
    case e of
      MirExp (CT.StructRepr ctx) _ -> do
        let s = Ctx.sizeInt (Ctx.size ctx)
        mapM (accessAggregate e) [0..(s-1)]
      _ -> fail "getallfields of non-struct"
        

accessAggregate :: MirExp s -> Int -> MirGenerator h s ret (MirExp s)
accessAggregate (MirExp (CT.StructRepr ctx) ag) i
 | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
     let tpr = ctx Ctx.! idx
     return $ MirExp tpr (S.getStruct idx ag tpr)     
accessAggregate a b = fail $ "invalid access: " ++ (show a) ++ ", " ++ (show b)

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


evalCast' :: M.CastKind -> M.Ty -> MirExp s -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast' ck ty1 e ty2  =
    case (ty1, ty2) of
      (M.TyUint _, M.TyUint s) -> extendUnsignedBV e s
      (M.TyInt _, M.TyInt s) -> extendSignedBV e s
      (a,b) | a == b -> return e
      (M.TyCustom (M.BoxTy tb1), M.TyCustom (M.BoxTy tb2)) -> evalCast' ck tb1 e tb2
      (M.TyArray _ _, M.TySlice _) -> return e -- arrays and slices have same denotation
      (x,y) -> fail $ "unimplemented cast: " ++ (show x) ++ " as " ++ (show y)

evalCast :: M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast ck op ty = do
    e <- evalOperand op
    evalCast' ck (M.typeOf op) e ty


-- Expressions: evaluation of Rvalues and Lvalues

evalRval :: M.Rvalue -> MirGenerator h s ret (MirExp s)
evalRval (M.Use op) = evalOperand op
evalRval (M.Repeat op size) = buildRepeat op size
evalRval (M.Ref bk lv _) = evalLvalue lv
evalRval (M.Len lv) = do
    (MirExp t e) <- evalLvalue lv
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
    accessAggregate e 0

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
                                       buildClosureHandle defid args
                                       
evalRval (M.RAdtAg (M.AdtAg adt agv ops)) = do
    es <- mapM evalOperand ops
    return $ buildTaggedUnion agv es

-- A closure is (packed into an any) of the form [handle, arguments] (arguments being those packed into the closure, not the function arguments)
buildClosureHandle :: Text.Text -> [MirExp s] -> MirGenerator h s ret (MirExp s)
buildClosureHandle funid args = do
    hmap <- use handlemap
    case (Map.lookup funid hmap) of
      (Just (MirHandle fargctx fretrepr fhandle)) -> do
          let closure_arg = buildTuple args
          let handle_cl = S.app $ E.HandleLit fhandle
              handle_cl_ty = CT.FunctionHandleRepr fargctx fretrepr
              handl = MirExp handle_cl_ty handle_cl
          let closure_unpack = buildTuple [handl, closure_arg]
          return $ packAny closure_unpack


buildClosureType :: Text.Text -> [M.Ty] -> MirGenerator h s ret (Some (CT.TypeRepr)) -- get type of closure, in order to unpack the any
buildClosureType defid args = do
    hmap <- use handlemap
    case (Map.lookup defid hmap) of
      (Just (MirHandle fargctx fretrepr fhandle)) -> do
          -- build type StructRepr [HandleRepr, StructRepr [args types]]
          tyListToCtx args $ \argsctx -> do
              let argstruct = CT.StructRepr argsctx
                  handlerepr = CT.FunctionHandleRepr fargctx fretrepr
              reprsToCtx [Some handlerepr, Some argstruct] $ \t ->
                  return $ Some (CT.StructRepr t)

unpackAny :: Some CT.TypeRepr -> MirExp s -> MirGenerator h s ret (MirExp s)
unpackAny tr (MirExp e_tp e) =
    case tr of
      Some tr | Just Refl <- testEquality e_tp (CT.AnyRepr) -> do
          return $ MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) ("Bad closure unpack"))
      _ -> fail $ "bad anytype"

packAny ::  MirExp s -> (MirExp s)
packAny (MirExp e_ty e) = MirExp (CT.AnyRepr) (S.app $ E.PackAny e_ty e)

filterMaybes :: [Maybe a] -> [a]
filterMaybes [] = []
filterMaybes ((Just a):as) = a : (filterMaybes as)
filterMaybes ((Nothing):as) = filterMaybes as

evalLvalue :: M.Lvalue -> MirGenerator h s ret (MirExp s)
evalLvalue (M.Tagged l _) = evalLvalue l
evalLvalue (M.Local var) = lookupVar var
evalLvalue (M.LProjection (M.LvalueProjection lv (M.PField field ty))) = do 
    case M.typeOf lv of
      M.TyAdt (M.Adt _ [struct_variant]) -> do -- if lv is a struct, extract the struct. 
        etu <- evalLvalue lv
        e <- accessAggregate etu 1
        let tr = variantToRepr struct_variant
        struct <- unpackAny tr e
        accessAggregate struct field

      M.TyClosure defid argsm -> do -- if lv is a closure, then accessing the ith component means accessing the ith arg in the struct
        e <- evalLvalue lv
        let args = filterMaybes argsm
        clty <- buildClosureType defid args
        unpack_closure <- unpackAny clty e
        clargs <- accessAggregate unpack_closure 1
        accessAggregate clargs field

      _ -> do -- otherwise, lv is a tuple
        ag <- evalLvalue lv
        accessAggregate ag field

evalLvalue (M.LProjection (M.LvalueProjection lv (M.Index i))) = do
    (MirExp arr_tp arr) <- evalLvalue lv
    (MirExp ind_tp ind) <- evalOperand i
    case (arr_tp, ind_tp) of
      (CT.VectorRepr elt_tp, CT.NatRepr) -> do
          return $ MirExp elt_tp $  S.app $ E.VectorGetEntry elt_tp arr ind
      _ -> fail "Bad index"

-- because references are the same as values, deref just passes through
evalLvalue (M.LProjection (M.LvalueProjection lv M.Deref)) = evalLvalue lv 

-- downcast: extracting the injection from an ADT. This is done in rust after switching on the discriminant.
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Downcast i))) = do
    etu <- evalLvalue lv
    (MirExp e_tp e) <- accessAggregate etu 1 
    let adt_typ = M.typeOf lv
    case adt_typ of
      M.TyAdt (M.Adt _ variants) -> do
          let tr = variantToRepr $ variants !! (fromInteger i)
          case tr of
            Some tr | Just Refl <- testEquality e_tp (CT.AnyRepr) -> 
                return $ MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) "bad anytype")
            _ -> fail $ "bad type: expected anyrepr but got " ++ (show e_tp)

      _ -> fail "expected adt type!"





evalLvalue lv = fail $ "unknown lvalue access: " ++ (show lv)





-- Statements
--

-- v := rvalue
--
assignVarRvalue :: M.Var -> M.Rvalue -> MirGenerator h s ret ()
assignVarRvalue (M.Var vname _ _ _) rv = do
    vm <- use varmap
    (MirExp rv_ty rv_exp) <- evalRval rv
    case (Map.lookup vname vm) of
      Just (Left (Some reg)) -> case (testEquality (R.typeOfReg reg) rv_ty) of
                           Just Refl -> G.assignReg reg rv_exp
                           _ -> fail $ "type error in assignment: got " ++ (show rv_ty) ++ " but expected " ++ (show (R.typeOfReg reg))
      Just (Right _) -> fail "cannot assign to atom"
      Nothing -> fail "register name not found"

-- v := mirexp

assignVarExp :: M.Var -> MirExp s -> MirGenerator h s ret ()
assignVarExp (M.Var vname _ vty _) (MirExp e_ty e) = do
    vm <- use varmap
    case (Map.lookup vname vm) of
      Just (Left (Some reg)) -> case (testEquality (R.typeOfReg reg) e_ty) of
                           Just Refl -> G.assignReg reg e
                           _ -> fail $ "type error in assignment: got " ++ (show e_ty) ++ " but expected " ++ (show (R.typeOfReg reg)) ++ " in assignment of " ++ (show vname) ++ "which has type " ++ (show vty) ++ " with exp " ++ (show e)
      Just (Right _) -> fail "cannot assign to atom"
      Nothing -> fail "register not found"

-- lv := mirexp

assignLvExp :: M.Lvalue -> MirExp s -> MirGenerator h s ret ()
assignLvExp lv re = do
    case lv of
        M.Tagged lv _ -> assignLvExp lv re
        M.Local var -> assignVarExp var re
        M.Static -> fail "static"
        M.LProjection (M.LvalueProjection lv (M.PField field ty)) -> do  
            case M.typeOf lv of
              M.TyAdt (M.Adt _ [struct_variant]) -> do 
                etu <- evalLvalue lv
                (MirExp e_tp e) <- accessAggregate etu 1
                let tr = variantToRepr struct_variant
                case tr of
                  Some tr | Just Refl <- testEquality e_tp (CT.AnyRepr) -> do
                      let struct = MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) "bad anytype")
                      new_st <- modifyAggregateIdx struct re field
                      let new_ag = buildTaggedUnion' 0 new_st -- 0 b/c this is a struct so has one variant
                      assignLvExp lv new_ag

              M.TyClosure _ _ -> fail "assign to closure unimp" 

              _ -> do
                ag <- evalLvalue lv 
                new_ag <- modifyAggregateIdx ag re field 
                assignLvExp lv new_ag
        M.LProjection (M.LvalueProjection lv (M.Index op)) -> do
            (MirExp arr_tp arr) <- evalLvalue lv
            (MirExp ind_tp ind) <- evalOperand op
            case re of
              MirExp r_tp r ->
                case (arr_tp, ind_tp) of
                  (CT.VectorRepr x, CT.NatRepr) -> 
                      case (testEquality x r_tp) of
                        Just Refl -> do
                          let arr' = MirExp arr_tp (S.app $ E.VectorSetEntry r_tp arr ind r)
                          assignLvExp lv arr'
                        Nothing -> fail "bad type in assign"
                  _ -> fail $ "bad type in assign"
        M.LProjection (M.LvalueProjection lv (M.Deref)) ->
            assignLvExp lv re
        _ -> fail $ "rest assign unimp: " ++ (show lv) ++ ", " ++ (show re) 

transStatement :: M.Statement -> MirGenerator h s ret ()
transStatement (M.Assign lv rv) = do
    re <- evalRval rv
    assignLvExp lv re
transStatement (M.SetDiscriminant lv i) = fail "setdiscriminant unimp" -- this should just change the first component of the adt
transStatement _ = return ()

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
transSwitch (MirExp (CT.NatRepr) e) vs ts =
    doNatBranch e vs ts

transSwitch (MirExp f e) _ _  = error $ "bad switch: " ++ (show f)

doBoolBranch :: R.Expr s CT.BoolType -> M.BasicBlockInfo -> M.BasicBlockInfo -> MirGenerator h s ret a
doBoolBranch e t f = do
    lm <- use labelmap
    case (Map.lookup t lm, Map.lookup f lm) of
      (Just tb, Just fb) -> G.branch e tb fb
      _ -> error "bad lookup on boolbranch"

-- nat branch: branch by iterating through list

doNatBranch :: R.Expr s CT.NatType -> [Integer] -> [M.BasicBlockInfo] -> MirGenerator h s ret a
doNatBranch _ _ [i] = do
    lm <- use labelmap
    case (Map.lookup i lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"
doNatBranch e (v:vs) (i:is) = do
    let test = S.app $ E.NatEq e $ S.app $ E.NatLit (fromInteger v)
    test_a <- G.mkAtom test
    G.endNow $ \_ -> do
        t_id <- G.newLabel
        f_id <- G.newLabel
        G.endCurrentBlock $! R.Br test_a t_id f_id
        G.defineBlock t_id (jumpToBlock i)
        G.defineBlock f_id (doNatBranch e vs is)
    
jumpToBlock :: M.BasicBlockInfo -> MirGenerator h s ret a
jumpToBlock bbi = do
    lm <- use labelmap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"

jumpToBlock' :: M.BasicBlockInfo -> MirGenerator h s ret () 
jumpToBlock' bbi = do
    lm <- use labelmap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> fail "bad jump"

doReturn :: CT.TypeRepr ret -> MirGenerator h s ret a 
doReturn tr = do
    e <- lookupRetVar tr
    G.returnFromFunction e

              
-- regular function calls: closure calls handled later
doCall :: Text.Text -> [M.Operand] -> Maybe (M.Lvalue, M.BasicBlockInfo) -> MirGenerator h s ret a
doCall funid cargs cdest = do
    hmap <- use handlemap
    case (Map.lookup funid hmap, cdest) of
      (Just (MirHandle fargctx fretrepr fhandle), Just (dest_lv, jdest)) -> do
          exps <- mapM evalOperand cargs
          exp_to_assgn exps $ \ctx asgn -> do
            case (testEquality ctx fargctx) of
              Just Refl -> do
                ret_e <- G.call (S.app $ E.HandleLit fhandle) asgn
                assignLvExp dest_lv (MirExp fretrepr ret_e)
                jumpToBlock jdest
              _ -> fail $ "type error in call: args " ++ (show ctx) ++ " vs function params " ++ (show fargctx) ++ " while calling " ++ (show funid)

      (_, Just (dest_lv, jdest)) -> doCustomCall funid cargs dest_lv jdest

      _ -> fail "bad dest"

transTerminator :: M.Terminator -> CT.TypeRepr ret -> MirGenerator h s ret a 
transTerminator (M.Goto bbi) _ = jumpToBlock bbi
transTerminator (M.SwitchInt swop swty svals stargs) _ = do
    s <- evalOperand swop
    transSwitch s svals stargs 
transTerminator (M.Return) tr = doReturn tr
transTerminator (M.DropAndReplace dlv dop dtarg _) _ = do
    transStatement (M.Assign dlv (M.Use dop))
    jumpToBlock dtarg
transTerminator (M.Call (M.OpConstant (M.Constant _ (M.Value (M.ConstFunction funid funsubsts))))  cargs cretdest _) _ = doCall funid cargs cretdest  -- cleanup ignored
transTerminator (M.Assert cond expected msg target cleanup) _ = jumpToBlock target -- asserts are ignored; is this the right thing to do? in a sense it is
transTerminator (M.Resume) tr = doReturn tr -- resume happens when unwinding
transTerminator (M.Drop dl dt dunwind) _ = jumpToBlock dt -- drop: just keep going
transTerminator t tr = fail $ "unknown terminator: " ++ (show t)


--- translation of toplevel glue --- 

tyToFreshReg :: M.Ty -> MirEnd h s ret (Some (R.Reg s))
tyToFreshReg t = do
    tyToReprCont t $ \tp ->
        Some <$> G.newUnassignedReg' tp
        
buildIdentMapRegs_ :: [(Text.Text, M.Ty)] -> MirEnd h s ret (VarMap s)
buildIdentMapRegs_ pairs = foldM f Map.empty pairs
    where f map_ (varname, varty) = do
            r <- tyToFreshReg varty
            return $ Map.insert varname (Left r) map_

buildIdentMapRegs :: forall h s ret. M.MirBody -> [M.Var] -> MirEnd h s ret (VarMap s)
buildIdentMapRegs (M.MirBody vars _) argvars = 
    buildIdentMapRegs_ (map (\(M.Var name _ ty _) -> (name,ty)) (vars ++ argvars))

buildLabelMap :: forall h s ret. M.MirBody -> MirEnd h s ret (LabelMap s)
buildLabelMap (M.MirBody _ blocks) = Map.fromList <$> (mapM buildLabel blocks)

buildLabel :: forall h s ret. M.BasicBlock -> MirEnd h s ret (M.BasicBlockInfo, R.Label s)
buildLabel (M.BasicBlock bi _) = do
    lab <- G.newLabel
    return (bi, lab)

buildFnState :: M.MirBody -> [M.Var] -> MirEnd h s ret (FnState s)
buildFnState body argvars = do
    lm <- buildLabelMap body 
    hm <- use handlemap
    vm' <- buildIdentMapRegs body argvars
    vm <- use varmap
    return $ FnState (Map.union vm vm') lm hm

initFnState ::  [(Text.Text, M.Ty)] -> CT.CtxRepr args -> Ctx.Assignment (R.Atom s) args -> Map.Map Text.Text MirHandle -> FnState s 
initFnState vars argsrepr args hmap = 
    FnState (go (reverse vars) argsrepr args Map.empty) (Map.empty) hmap
    where go :: [(Text.Text, M.Ty)] -> CT.CtxRepr args -> Ctx.Assignment (R.Atom s) args -> VarMap s -> VarMap s
          go [] ctx _ m
            | Ctx.null ctx = m
            | otherwise = error "wrong number of args"
          go ((name,ti):ts) ctx asgn m =
            unfold_ctx_assgn ti ctx asgn $ \atom ctx' asgn' ->
                 go ts ctx' asgn' (Map.insert name (Right atom) m)




-- do the statements and then the terminator
translateBlockBody :: CT.TypeRepr ret -> M.BasicBlockData -> MirGenerator h s ret ()
translateBlockBody tr (M.BasicBlockData stmts terminator) = (mapM_ transStatement stmts) >> (transTerminator terminator tr) 

-- 
registerBlock :: CT.TypeRepr ret -> M.BasicBlock -> MirEnd h s ret ()
registerBlock tr (M.BasicBlock bbinfo bbdata)  = do
    lm <- use labelmap
    case (Map.lookup bbinfo lm) of
      Just lab -> G.defineBlock lab (translateBlockBody tr bbdata)
      _ -> fail "bad label"


-- processing of function body. here each argument is assumed to already be in the varmap
genDefn' :: M.MirBody -> [M.Var] -> CT.TypeRepr ret -> MirGenerator h s ret (R.Expr s ret) 
genDefn' body argvars rettype = do
    G.endNow $ \_ -> do
        (FnState a b c) <- buildFnState body argvars -- argvars are registers
        varmap .= a
        labelmap .= b
        lm <- use labelmap
        let (M.MirBody vars (enter : blocks)) = body -- The first block in the list is the entrance block
        let (M.BasicBlock bbi _) = enter
        case (Map.lookup bbi lm ) of
            Just lbl -> G.endCurrentBlock (R.Jump lbl) 
            _ -> fail "bad thing happened"
        mapM_ (registerBlock rettype) (enter : blocks)


genDefn :: M.Fn -> CT.TypeRepr ret -> MirGenerator h s ret (R.Expr s ret)
genDefn (M.Fn fname fargs fretty fbody) retrepr = genDefn' fbody fargs retrepr


mkHandleMap :: FH.HandleAllocator s -> [M.Fn] -> ST s (Map.Map Text.Text MirHandle)
mkHandleMap halloc fns = Map.fromList <$> (mapM (mkHandle halloc) fns) where
    mkHandle :: FH.HandleAllocator s -> M.Fn -> ST s (Text.Text, MirHandle)
    mkHandle halloc (M.Fn fname fargs fretty fbody) = 
        fnInfoToReprs (map (\(M.Var _ _ t _) -> t) fargs) fretty $ \argctx retrepr -> do
            h <- FH.mkHandle' halloc (FN.functionNameFromText fname) argctx retrepr
            let mh = MirHandle argctx retrepr h
            return (fname, mh)
    
    fnInfoToReprs :: forall a. [M.Ty] -> M.Ty -> (forall argctx ret. CT.CtxRepr argctx -> CT.TypeRepr ret -> a) -> a
    fnInfoToReprs args retp f = 
        tyListToCtx args $ \argrepr ->
            tyToReprCont retp $ \retrepr ->
                 f argrepr retrepr

-- transDefine: make CFG using genDefn (with type info coming from above), using initial state from initState; return (fname, CFG)


transDefine :: Map.Map Text.Text MirHandle -> M.Fn -> ST h (Text.Text, Core.AnyCFG)
transDefine hmap fn =
    let (M.Fn fname fargs _ _) = fn in
        case (Map.lookup fname hmap) of
          Nothing -> fail "bad handle!!"
          Just (MirHandle argctx retrepr (handle :: FH.FnHandle args ret)) -> do
              let argtups = map (\(M.Var n _ t _) -> (n,t)) fargs
              let argtypes = FH.handleArgTypes handle
              let rettype = FH.handleReturnType handle
              let def :: G.FunctionDef handle FnState args ret
                  def inputs = (s,f) where
                      s = initFnState argtups argtypes inputs hmap
                      f = genDefn fn rettype
              (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos handle def
              case SSA.toSSA g of
                Core.SomeCFG g_ssa -> return (fname, Core.AnyCFG g_ssa)




-- transCollection: initialize map of fn names to FnHandles. 
transCollection :: [M.Fn] -> FH.HandleAllocator s -> ST s (Map.Map Text.Text Core.AnyCFG)
transCollection fns halloc = do
    hmap <- mkHandleMap halloc fns
    pairs <- mapM (transDefine hmap) fns
    return $ Map.fromList pairs




--- Custom stuff
--

-- if we want to be able to insert custom information just before runtime, the below can be dynamic, and baked into the Override monad.

customtyToRepr :: M.CustomTy -> Some CT.TypeRepr
customtyToRepr (M.BoxTy t) = tyToRepr t -- Box<T> is the same as T
customtyToRepr (M.VecTy t) = tyToRepr $ M.TySlice t -- Vec<T> is the same as [T]
customtyToRepr (M.IterTy t) = tyToRepr $ M.TyTuple [M.TySlice t, M.TyUint M.USize] -- Iter<T> => ([T], nat). The second component is the current index into the array, beginning at zero.
 
mkNone :: MirExp s
mkNone = 
    buildTuple [MirExp CT.NatRepr (S.app $ E.NatLit 0), packAny $ buildTuple []]

mkSome :: MirExp s -> MirExp s
mkSome a = buildTuple [MirExp CT.NatRepr (S.app $ E.NatLit 1), packAny $ buildTuple [a]]

extractVecTy :: forall a t. CT.TypeRepr t -> (forall t2. CT.TypeRepr t2 -> a) -> a 
extractVecTy (CT.VectorRepr a) f = f a
extractVecTy _ _ = error "Expected vector type in extraction"


-- ripped from the generator but with amended types
myIfte :: 
      R.Expr s CT.BoolType
     -> MirGenerator h s ret ()
     -> MirGenerator h s ret ()
     -> MirGenerator h s ret a
myIfte e x y = do
  test_a <- G.mkAtom e
  G.endNow $ \c -> do
    t_id <- G.newLabel
    f_id <- G.newLabel

    G.endCurrentBlock $! R.Br test_a t_id f_id
    G.defineBlock t_id x
    G.defineBlock f_id y

doCustomCall :: Text.Text -> [M.Operand] -> M.Lvalue -> M.BasicBlockInfo -> MirGenerator h s ret a
doCustomCall fname ops lv dest  
  | Just "boxnew" <- M.isCustomFunc fname,
  [op] <- ops =  do 
        e <- evalOperand op
        assignLvExp lv e
        jumpToBlock dest

  | Just "slice_tovec" <- M.isCustomFunc fname, 
  [op] <- ops = do 
        e <- evalOperand op
        assignLvExp lv e
        jumpToBlock dest

  | Just "vec_asmutslice" <- M.isCustomFunc fname,
  [op] <- ops = do 
        ans <- evalOperand op
        assignLvExp lv ans
        jumpToBlock dest
        
 | Just "index" <- M.isCustomFunc fname,
    [op1, op2] <- ops = do
        ans <- evalLvalue (M.LProjection (M.LvalueProjection (M.lValueofOp op1) (M.Index op2)))
        assignLvExp lv ans
        jumpToBlock dest

 | Just "vec_fromelem" <- M.isCustomFunc fname,
    [elem, u] <- ops = do
        ans <- buildRepeat_ elem u
        assignLvExp lv ans
        jumpToBlock dest

 | Just "into_iter" <- M.isCustomFunc fname, -- vec -> (vec, 0)
    [v] <- ops = do
        vec <- evalOperand v
        let t = buildTuple [vec, MirExp (CT.NatRepr) (S.app $ E.NatLit 0)]
        assignLvExp lv t
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

         good_branch = do
             assignLvExp lv good_ret
             jumpToBlock' dest

         bad_branch = do
             assignLvExp lv bad_ret
             jumpToBlock' dest

     myIfte is_good good_branch bad_branch
     
 | Just "iter_map" <- M.isCustomFunc fname, [iter, closure] <- ops = do
     iter_e <- evalOperand iter
     closure_e <- evalOperand closure
     iter2 <- performMap (M.typeOf iter) iter_e (M.typeOf closure) closure_e
     assignLvExp lv iter2
     jumpToBlock dest

 | Just "iter_collect" <- M.isCustomFunc fname, [o] <- ops = do
     iter <- evalOperand o
     v <- accessAggregate iter 0
     assignLvExp lv v
     jumpToBlock dest
     

 | Just "call" <- M.isCustomFunc fname, -- perform call of closure
 [o1, o2] <- ops = do

     argtuple <- evalOperand o2
     case (M.typeOf o1, M.typeOf o2) of
       (M.TyClosure defid clargsm, M.TyTuple args) -> do
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
                             assignLvExp lv (MirExp fretrepr ret_e)
                             jumpToBlock dest
                   _ -> fail $ "bad handle type"

       _ -> fail "unexpected type in Fn::call!"

 | Just cf <- M.isCustomFunc fname = fail $ "custom function not handled: " ++ (show cf)

 | otherwise =  fail $ "not found: " ++ (show $ M.isCustomFunc fname)

transCustomAgg :: M.CustomAggregate -> MirGenerator h s ret (MirExp s) -- depreciated
transCustomAgg (M.CARange ty f1 f2) = evalRval (M.Aggregate M.AKTuple [f1,f2])

performUntil :: R.Expr s CT.NatType -> (R.Reg s CT.NatType -> MirGenerator h s ret ()) -> MirGenerator h s ret ()
performUntil n f = do -- perform (f i) for i = 0..n (not inclusive). f takes as input a nat register (but shouldn't increment it)
    ind <- G.newReg $ S.app $ E.NatLit 0
    G.while (PL.InternalPos, test n ind) (PL.InternalPos, (run_incr f) ind)
            
   where test :: R.Expr s CT.NatType -> R.Reg s CT.NatType -> MirGenerator h s ret (R.Expr s CT.BoolType)
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
      (M.TyCustom (M.IterTy t), M.TyClosure defid clargsm) -> do
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
