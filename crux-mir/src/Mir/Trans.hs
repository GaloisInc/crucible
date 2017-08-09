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


data MirExp s where
    MirExp :: CT.TypeRepr tp -> R.Expr s tp -> MirExp s

instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)

type CollectionTranslation = Map.Map Text.Text Core.AnyCFG

taggedUnionType :: Some (CT.TypeRepr)
taggedUnionType = Some $ CT.StructRepr $ Ctx.empty Ctx.%> CT.NatRepr Ctx.%> CT.AnyRepr


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
adtToRepr (M.Adt adtname variants) = taggedUnionType


-- Type translation and type-level list utilities

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
                        M.TyChar -> Some $ CT.BVRepr (knownNat :: NatRepr 8) 
                        M.TyCustom custom_t -> customtyToRepr custom_t 
                        _ -> error "unknown type?"

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

unfold_ctx_assgn :: M.Ty -> CT.CtxRepr ctx -> Ctx.Assignment (R.Atom s) ctx -> (forall ctx'. Some (R.Atom s) -> CT.CtxRepr ctx' -> Ctx.Assignment (R.Atom s) ctx' -> a) -> a
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
      (Just (Right (Some atom)), Some vtr) -> do { return $ MirExp (R.typeOfAtom atom) (R.AtomExpr atom) }
      _ -> error "register not found"

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
    return $ buildTuple [res, MirExp (CT.BoolRepr) (S.litExpr False)] -- TODO always succeeds. we could implement this using BVCarry for addition, and a special procedure for multiplication

transNullaryOp ::  M.NullOp -> M.Ty -> MirGenerator h s ret (MirExp s)
transNullaryOp _ _ = fail "nullop"

transUnaryOp :: M.UnOp -> M.Operand -> MirGenerator h s ret (MirExp s)
transUnaryOp uop op = do
    mop <- evalOperand op
    case (uop, mop) of
      (M.Not, MirExp CT.BoolRepr e) -> return $ MirExp CT.BoolRepr $ S.app $ E.Not e
      (M.Neg, MirExp (CT.BVRepr n) e) -> return $ MirExp (CT.BVRepr n) (S.app $ E.BVSub n (S.app $ E.BVLit n 0) e)
      _ -> fail "bad op or type for unary"



buildRepeat :: M.Operand -> M.ConstUsize -> MirGenerator h s ret (MirExp s)
buildRepeat op size = do
    (MirExp tp e) <- evalOperand op
    let n = fromInteger size
    return $ MirExp (CT.VectorRepr tp) (S.app $ E.VectorReplicate tp (S.app $ E.NatLit n) e)

buildRepeat_ :: M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
buildRepeat_ op size = do
    let (M.OpConstant (M.Constant _ (M.Value (M.ConstInt i)))) = size
    buildRepeat op i

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
    case v of
      MirExp vt ve ->
        buildTuple [MirExp (CT.NatRepr) (S.app $ E.NatLit (fromInteger i)), MirExp (CT.AnyRepr) (S.app $ E.PackAny vt ve) ]


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

evalCast :: M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast ck op ty = do
    e <- evalOperand op
    
    case (M.typeOf op, ty) of
      (M.TyUint _, M.TyUint s) -> extendUnsignedBV e s
      (M.TyInt _, M.TyInt s) -> extendSignedBV e s
      _ -> fail "unimplemented cast"


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
                                       
                                   _ -> fail "other aggregate build unimp"
evalRval (M.RAdtAg (M.AdtAg adt agv ops)) = do
    es <- mapM evalOperand ops
    return $ buildTaggedUnion agv es


                       
evalLvalue :: M.Lvalue -> MirGenerator h s ret (MirExp s)
evalLvalue (M.Tagged l _) = evalLvalue l
evalLvalue (M.Local var) = lookupVar var
evalLvalue (M.LProjection (M.LvalueProjection lv (M.PField field ty))) = do
    case M.typeOf lv of
      M.TyAdt (M.Adt _ [struct_variant]) -> -- if lv is a struct, extract the struct
        etu <- evalLvalue lv
        (MirExp e_tp e) <- accessAggregate etu 1
        let tr = variantToRepr struct_variant
        case tr of
          Some tr | Just Refl <- testEquality e_tp (CT.AnyRepr) ->
              let struct = MirExp tr (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr e) "bad anytype")
              accessAggregate struct field
      _ -> -- otherwise, lv is a tuple
        ag <- evalLvalue lv
        accessAggregate ag field
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Index i))) = do
    (MirExp arr_tp arr) <- evalLvalue lv
    (MirExp ind_tp ind) <- evalOperand i
    case (arr_tp, ind_tp) of
      (CT.VectorRepr elt_tp, CT.NatRepr) -> do
          return $ MirExp elt_tp $  S.app $ E.VectorGetEntry elt_tp arr ind
evalLvalue (M.LProjection (M.LvalueProjection lv M.Deref)) = evalLvalue lv
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

assignVarExp :: M.Var -> MirExp s -> MirGenerator h s ret ()
assignVarExp (M.Var vname _ _ _) (MirExp e_ty e) = do
    vm <- use varmap
    case (Map.lookup vname vm) of
      Just (Left (Some reg)) -> case (testEquality (R.typeOfReg reg) e_ty) of
                           Just Refl -> G.assignReg reg e
                           _ -> fail $ "type error in assignment: got " ++ (show e_ty) ++ " but expected " ++ (show (R.typeOfReg reg)) ++ " in assignment of " ++ (show vname) ++ " with exp " ++ (show e)
      Just (Right _) -> fail "cannot assign to atom"
      Nothing -> fail "register not found"

assignLvExp :: M.Lvalue -> MirExp s -> MirGenerator h s ret ()
assignLvExp lv re = do
    case lv of
        M.Tagged lv _ -> assignLvExp lv re
        M.Local var -> assignVarExp var re
        M.Static -> fail "static"
        M.LProjection (M.LvalueProjection lv (M.PField field ty)) -> do  
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
transStatement (M.SetDiscriminant lv i) = fail "setdiscriminant unimp"
transStatement _ = return ()

-- only works for booleans for now
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

doReturn :: CT.TypeRepr ret -> MirGenerator h s ret a 
doReturn tr = do
    e <- lookupRetVar tr
    G.returnFromFunction e




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

-- rettype is threaded through genDefn in LLVM
-- gsState (ie, my Fnstate) is modified in End, and THEN afterwards each block is defined.

-- processing of function body. here each argument is assumed to already be in the varmap
genDefn' :: M.MirBody -> [M.Var] -> CT.TypeRepr ret -> MirGenerator h s ret (R.Expr s ret) 
genDefn' body argvars rettype = do
    G.endNow $ \_ -> do
        (FnState a b c) <- buildFnState body argvars -- argvars are registers
        varmap .= a
        labelmap .= b
        lm <- use labelmap
        let (M.MirBody vars (enter : blocks)) = body 
        let (M.BasicBlock bbi _) = enter
        case (Map.lookup bbi lm ) of
            Just lbl -> G.endCurrentBlock (R.Jump lbl) 
            _ -> fail "bad thing happened"
        mapM_ (registerBlock rettype) (enter : blocks)


genDefn :: M.Fn -> CT.TypeRepr ret -> MirGenerator h s ret (R.Expr s ret)
genDefn (M.Fn fname fargs fretty fbody) retrepr = genDefn' fbody fargs retrepr

data MirHandle where
    MirHandle :: CT.CtxRepr init -> CT.TypeRepr ret -> FH.FnHandle init ret -> MirHandle

instance Show MirHandle where
    show (MirHandle a b c) = unwords [show a, show b, show c]

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

-- if we want to be able to insert custom information just before runtime, the below can be dynamic and baked into FnState

customtyToRepr :: M.CustomTy -> Some CT.TypeRepr
customtyToRepr (M.RangeTy t) = tyToRepr $ M.TyTuple [t, t] -- range is turned into its tuple
customtyToRepr (M.BoxTy t) = tyToRepr t
customtyToRepr (M.VecTy t) = tyToRepr $ M.TySlice t



doCustomCall :: Text.Text -> [M.Operand] -> M.Lvalue -> M.BasicBlockInfo -> MirGenerator h s ret a
doCustomCall fname ops lv dest  
  | Just "boxnew" <- M.isCustomFunc fname,
  [op] <- ops =  do -- box::new
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

 | otherwise =  fail $ "not found: " ++ (show fname)

transCustomAgg :: M.CustomAggregate -> MirGenerator h s ret (MirExp s)
transCustomAgg (M.CARange ty f1 f2) = evalRval (M.Aggregate M.AKTuple [f1,f2])
