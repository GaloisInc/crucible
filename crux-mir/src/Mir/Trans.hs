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
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}

module Mir.Trans(transCollection,transStatics,RustModule(..)
                , readMirRef
                , writeMirRef
                , subindexRef
                , evalBinOp
                , vectorCopy
                , evalRval
                , callExp) where

import Control.Monad
import Control.Monad.ST

import Control.Lens hiding (op,(|>))
import Data.Foldable

import qualified Data.ByteString as BS
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Data.Semigroup(Semigroup(..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Data.String (fromString)
import Numeric
import Numeric.Natural()

import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.FunctionHandle as FH
import qualified What4.ProgramLoc as PL
import qualified What4.FunctionName as FN
import qualified What4.Utils.StringLiteral as W4
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.SSAConversion as SSA
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Syntax as S
import qualified Lang.Crucible.Types as C


import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.Peano
import Data.Parameterized.TraversableFC
import Data.Parameterized.Nonce (newSTNonceGenerator)

import Mir.Mir
import Mir.MirTy
import qualified Mir.Mir as M
import qualified Mir.DefId as M

import Mir.Intrinsics
import Mir.Generator
import Mir.GenericOps
import Mir.TransTy

import Mir.PP(fmt)
import Text.PrettyPrint.ANSI.Leijen(Pretty(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import GHC.Stack

import Debug.Trace


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

u8ToBV8 :: ConstVal -> R.Expr MIR s (C.BVType 8)
u8ToBV8 (ConstInt (U8 c)) = R.App (E.BVLit knownRepr c)
u8ToBV8 _ = error $ "BUG: array literals should only contain bytes (u8)"
-- Expressions: variables and constants
--

transConstVal :: HasCallStack => Some C.TypeRepr -> M.ConstVal -> MirGenerator h s ret (MirExp s)
transConstVal (Some (C.BVRepr w)) (M.ConstInt i) =
    return $ MirExp (C.BVRepr w) (S.app $ E.BVLit w (fromInteger (M.fromIntegerLit i)))
transConstVal (Some (C.BoolRepr)) (M.ConstBool b) = return $ MirExp (C.BoolRepr) (S.litExpr b)
transConstVal (Some (UsizeRepr)) (M.ConstInt i) =
    do let n = fromInteger (M.fromIntegerLit i)
       return $ MirExp UsizeRepr (S.app $ usizeLit n)
transConstVal (Some (IsizeRepr)) (ConstInt i) =
      return $ MirExp IsizeRepr (S.app $ isizeLit (fromIntegerLit i))
transConstVal (Some (MirImmSliceRepr (C.BVRepr w))) (M.ConstStr bs)
  | Just Refl <- testEquality w (knownNat @8) = do
    let u8Repr = C.BVRepr $ knownNat @8
    let bytes = map (\b -> R.App (E.BVLit (knownNat @8) (toInteger b))) (BS.unpack bs)
    let vec = R.App $ E.VectorLit u8Repr (V.fromList bytes)
    mirVec <- mirVector_fromVector u8Repr vec
    let start = R.App $ usizeLit 0
    let len = R.App $ usizeLit $ fromIntegral $ BS.length bs
    let struct = S.mkStruct
            knownRepr
            (Ctx.Empty Ctx.:> mirVec Ctx.:> start Ctx.:> len)
    return $ MirExp (MirImmSliceRepr u8Repr) struct
transConstVal (Some (C.VectorRepr w)) (M.ConstArray arr)
      | Just Refl <- testEquality w (C.BVRepr (knownRepr :: NatRepr 8))
      = do let bytes = V.fromList (map u8ToBV8 arr)
           return $ MirExp (C.VectorRepr w) (R.App $ E.VectorLit w bytes)
transConstVal (Some (C.BVRepr w)) (M.ConstChar c) =
    do let i = toInteger (Char.ord c)
       return $ MirExp (C.BVRepr w) (S.app $ E.BVLit w i)
transConstVal (Some C.UnitRepr) (M.ConstFunction _did _substs) =
    return $ MirExp C.UnitRepr $ S.app E.EmptyApp

transConstVal (Some (C.RealValRepr)) (M.ConstFloat (M.FloatLit _ str)) =
    case reads str of
      (d , _):_ -> let rat = toRational (d :: Double) in
                   return (MirExp C.RealValRepr (S.app $ E.RationalLit rat))
      []        -> mirFail $ "cannot parse float constant: " ++ show str

transConstVal (Some _ty) (ConstInitializer funid ss) =
    callExp funid ss [] 
transConstVal tp cv = mirFail $ "fail or unimp constant: " ++ (show tp) ++ " " ++ (show cv)


lookupVar :: HasCallStack => M.Var -> MirGenerator h s ret (MirExp s)
lookupVar (M.Var vname _ vty _ _ pos) = do
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

        | otherwise -> mirFail ("bad type in lookupVar: " <> show vname <> " at " <> Text.unpack pos <>
                             "\n\t expected " <> show vtr <> " found " <> show (varInfoRepr varinfo))
      _ -> mirFail ("register not found: " <> show vname <> " at " <> Text.unpack pos)

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
          Nothing -> mirFail $ "return register has wrong type. Expected: "
                       ++ show tr ++ "\n Found " ++ show (varInfoRepr varinfo)

      _ -> mirFail $ "reg not found in retvar " ++ show (Map.keys vm)


-- ** Expressions: Operations and Aggregates

evalOperand :: HasCallStack => M.Operand -> MirGenerator h s ret (MirExp s)
evalOperand (M.Copy lv) = evalLvalue lv
evalOperand (M.Move lv) = evalLvalue lv
evalOperand (M.OpConstant (M.Constant conty conlit)) =
    case conlit of
       M.Value constval   -> transConstVal (tyToRepr conty) constval
       M.Item defId _args -> mirFail $ "cannot translate item " ++ show defId
       M.LitPromoted (M.Promoted idx) ->  do
          fn <- use currentFn
          let st = fn^.fpromoted
          case st V.!? idx of
            Just did -> lookupStatic did
            Nothing  -> mirFail $ "Promoted index " ++ show idx ++ " out of range "



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



transBinOp :: M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s)
transBinOp bop op1 op2 = do
    me1 <- evalOperand  op1
    me2 <- evalOperand  op2
    let mat = M.arithType op1 `mplus` M.arithType op2 
    fst <$> evalBinOp bop mat me1 me2

-- Evaluate a binop, returning both the result and an overflow flag.
evalBinOp :: M.BinOp -> Maybe M.ArithType -> MirExp s -> MirExp s ->
    MirGenerator h s ret (MirExp s, R.Expr MIR s C.BoolType)
evalBinOp bop mat me1 me2 =
    case (me1, me2) of
      (MirExp ty1@(C.BVRepr na) e1a, MirExp ty2@C.NatRepr e2a) ->
         case (bop, mat) of
            (M.Shl, _) -> do
                let e2bv = S.app (E.IntegerToBV na (S.app (E.NatToInteger e2a)))
                return (MirExp (C.BVRepr na) (S.app $ E.BVShl na e1a e2bv),
                    shiftOverflowNat na e2a)
            (M.Shr, Just M.Unsigned) -> do
                let e2bv = S.app (E.IntegerToBV na (S.app (E.NatToInteger e2a)))
                return (MirExp (C.BVRepr na) (S.app $ E.BVLshr na e1a e2bv),
                    shiftOverflowNat na e2a)
            (M.Shr, Just M.Signed) -> do
                let e2bv = S.app (E.IntegerToBV na (S.app (E.NatToInteger e2a)))
                return (MirExp (C.BVRepr na) (S.app $ E.BVAshr na e1a e2bv),
                    shiftOverflowNat na e2a)

            _ -> mirFail $ "No translation for binop: " ++ show bop ++ " with " ++ show ty1 ++ " and " ++ show ty2
      (MirExp ty1@(C.BVRepr na) e1a, MirExp ty2@(C.BVRepr ma) e2a) ->
          -- if the BVs are not the same width extend the shorter one
          extendToMax na e1a ma e2a (mat) $ \ n e1 e2 -> 
            case (bop, mat) of
              (M.Add, _) -> do
                let carry = case mat of
                        Just M.Unsigned -> E.BVCarry
                        Nothing -> E.BVCarry
                        Just M.Signed -> E.BVSCarry
                return (MirExp (C.BVRepr n) (S.app $ E.BVAdd n e1 e2), S.app $ carry n e1 e2)
              (M.Sub, _) -> do
                let borrow = case mat of
                        Just M.Unsigned -> E.BVUlt
                        Nothing -> E.BVUlt
                        Just M.Signed -> E.BVSBorrow
                return (MirExp (C.BVRepr n) (S.app $ E.BVSub n e1 e2), S.app $ borrow n e1 e2)
              -- FIXME: implement overflow checks for Mul, Div, and Rem
              (M.Mul, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVMul n e1 e2), unknownOverflow)
              (M.Div, Just M.Unsigned) -> return (MirExp (C.BVRepr n) (S.app $ E.BVUdiv n e1 e2), unknownOverflow)
              (M.Div, Just M.Signed) -> return (MirExp (C.BVRepr n) (S.app $ E.BVSdiv n e1 e2), unknownOverflow)
              (M.Rem, Just M.Unsigned) -> return (MirExp (C.BVRepr n) (S.app $ E.BVUrem n e1 e2), unknownOverflow)
              (M.Rem, Just M.Signed) -> return (MirExp (C.BVRepr n) (S.app $ E.BVSrem n e1 e2), unknownOverflow)
              -- Bitwise ops never overflow
              (M.BitXor, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVXor n e1 e2), noOverflow)
              (M.BitAnd, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVAnd n e1 e2), noOverflow)
              (M.BitOr, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVOr n e1 e2), noOverflow)
              -- Shift ops overflow when shift amount >= bit width
              -- FIXME: check the logic here.  Not sure about these truncations
              (M.Shl, _) -> do
                 res <- extendUnsignedBV (MirExp (C.BVRepr n) (S.app $ E.BVShl n e1 e2)) na
                 return (res, shiftOverflowBV na ma e2a)
              (M.Shr, Just M.Unsigned) -> do
                 res <- extendUnsignedBV (MirExp (C.BVRepr n) (S.app $ E.BVLshr n e1 e2)) na
                 return (res, shiftOverflowBV na ma e2a)
              (M.Shr, Nothing) -> do
                 res <- extendUnsignedBV (MirExp (C.BVRepr n) (S.app $ E.BVLshr n e1 e2)) na
                 return (res, shiftOverflowBV na ma e2a)
              (M.Shr, Just M.Signed) -> do
                 res <- extendSignedBV (MirExp (C.BVRepr n) (S.app $ E.BVAshr n e1 e2) ) na
                 return (res, shiftOverflowBV na ma e2a)
              -- Comparison ops never overflow
              (M.Lt, Just M.Unsigned) -> return (MirExp (C.BoolRepr) (S.app $ E.BVUlt n e1 e2), noOverflow)
              (M.Lt, Just M.Signed)   -> return (MirExp (C.BoolRepr) (S.app $ E.BVSlt n e1 e2), noOverflow)
              (M.Le, Just M.Unsigned) -> return (MirExp (C.BoolRepr) (S.app $ E.BVUle n e1 e2), noOverflow)
              (M.Le, Just M.Signed)   -> return (MirExp (C.BoolRepr) (S.app $ E.BVSle n e1 e2), noOverflow)

              (M.Gt, Just M.Unsigned) -> return (MirExp (C.BoolRepr) (S.app $ E.BVUlt n e2 e1), noOverflow)
              (M.Gt, Just M.Signed)   -> return (MirExp (C.BoolRepr) (S.app $ E.BVSlt n e2 e1), noOverflow)
              (M.Ge, Just M.Unsigned) -> return (MirExp (C.BoolRepr) (S.app $ E.BVUle n e2 e1), noOverflow)
              (M.Ge, Just M.Signed)   -> return (MirExp (C.BoolRepr) (S.app $ E.BVSle n e2 e1), noOverflow)

              (M.Ne, _) -> return (MirExp (C.BoolRepr) (S.app $ E.Not $ S.app $ E.BVEq n e1 e2), noOverflow)
              (M.Beq, _) -> return (MirExp (C.BoolRepr) (S.app $ E.BVEq n e1 e2), noOverflow)
              _ -> mirFail $ "No translation for binop: " ++ show bop ++ " " ++ show mat
                           ++ " for " ++ show ty1 ++ " and " ++ show ty2
      (MirExp C.BoolRepr e1, MirExp C.BoolRepr e2) ->
          case bop of
            M.BitAnd -> return (MirExp C.BoolRepr (S.app $ E.And e1 e2), noOverflow)
            M.BitXor -> return (MirExp C.BoolRepr (S.app $ E.BoolXor e1 e2), noOverflow)
            M.BitOr -> return (MirExp C.BoolRepr (S.app $ E.Or e1 e2), noOverflow)
            M.Beq -> return (MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.BoolXor e1 e2), noOverflow)
            M.Ne  -> return (MirExp C.BoolRepr (S.app $ E.BoolXor e1 e2), noOverflow)
            _ -> mirFail $ "No translation for bool binop: " ++ fmt bop
      (MirExp C.RealValRepr e1, MirExp C.RealValRepr e2) ->
          case bop of
            M.Beq -> return (MirExp C.BoolRepr (S.app $ E.RealEq e1 e2), noOverflow)
            M.Lt -> return (MirExp C.BoolRepr (S.app $ E.RealLt e1 e2), noOverflow)
            M.Le -> return (MirExp C.BoolRepr (S.app $ E.RealLe e1 e2), noOverflow)
            M.Gt -> return (MirExp C.BoolRepr (S.app $ E.RealLt e2 e1), noOverflow)
            M.Ge -> return (MirExp C.BoolRepr (S.app $ E.RealLe e2 e1), noOverflow)
            M.Ne -> return (MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.RealEq e1 e2), noOverflow)

            -- Binops on floats never set the overflow flag
            M.Add -> return (MirExp C.RealValRepr (S.app $ E.RealAdd e1 e2), noOverflow)
            M.Sub -> return (MirExp C.RealValRepr (S.app $ E.RealSub e1 e2), noOverflow)
            M.Mul -> return (MirExp C.RealValRepr (S.app $ E.RealMul e1 e2), noOverflow)
            M.Div -> return (MirExp C.RealValRepr (S.app $ E.RealDiv e1 e2), noOverflow)
            M.Rem -> return (MirExp C.RealValRepr (S.app $ E.RealMod e1 e2), noOverflow)

            _ -> mirFail $ "No translation for real number binop: " ++ fmt bop

      (_, _) -> mirFail $ "bad or unimplemented type: " ++ (fmt bop) ++ ", " ++ (show me1) ++ ", " ++ (show me2)

  where
    noOverflow :: R.Expr MIR s C.BoolType
    noOverflow = S.app $ E.BoolLit False
    -- For now, assume unsupported operations don't overflow.  Eventually all
    -- overflow checks should be implemented, and we can remove this.
    unknownOverflow = noOverflow

    -- Check that shift amount `e` is less than the input width `w`.
    shiftOverflowNat w e =
        let wLit = S.app $ E.NatLit $ natValue w
        in S.app $ E.Not $ S.app $ E.NatLt e wLit
    -- Check that shift amount `e` (whose width in `w'`) is less than the input
    -- width `w`.
    shiftOverflowBV :: (1 <= w') =>
        NatRepr w -> NatRepr w' -> R.Expr MIR s (C.BVType w') -> R.Expr MIR s C.BoolType
    shiftOverflowBV w w' e =
        let wLit = S.app $ E.BVLit w' $ intValue w
        in S.app $ E.Not $ S.app $ E.BVUlt w' e wLit



transCheckedBinOp ::  M.BinOp -> M.Operand -> M.Operand -> MirGenerator h s ret (MirExp s) -- returns tuple of (result, bool)
transCheckedBinOp op a b = do
    a' <- evalOperand  a
    b' <- evalOperand  b
    let mat = M.arithType a `mplus` M.arithType b
    (res, overflow) <- evalBinOp op mat a' b'
    return $ buildTupleMaybe [error "not needed", TyBool] [Just res, Just $ MirExp (C.BoolRepr) overflow]


-- Nullary ops in rust are used for resource allocation, so are not interpreted
transNullaryOp ::  M.NullOp -> M.Ty -> MirGenerator h s ret (MirExp s)
transNullaryOp _ _ = mirFail "nullop"

transUnaryOp :: M.UnOp -> M.Operand -> MirGenerator h s ret (MirExp s)
transUnaryOp uop op = do
    mop <- evalOperand op
    case (uop, mop) of
      (M.Not, MirExp C.BoolRepr e) -> return $ MirExp C.BoolRepr $ S.app $ E.Not e
      (M.Not, MirExp (C.BVRepr n) e) -> return $ MirExp (C.BVRepr n) $ S.app $ E.BVNot n e
      (M.Neg, MirExp (C.BVRepr n) e) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVSub n (S.app $ E.BVLit n 0) e)
      (M.Neg, MirExp C.IntegerRepr e) -> return $ MirExp C.IntegerRepr $ S.app $ E.IntNeg e
      (M.Neg, MirExp C.RealValRepr e) -> return $ MirExp C.RealValRepr $ S.app $ E.RealNeg e
      (_ , MirExp ty e) -> mirFail $ "Unimplemented unary op `" ++ fmt uop ++ "' for " ++ show ty


-- a -> u -> [a;u]
buildRepeat :: M.Operand -> M.ConstUsize -> MirGenerator h s ret (MirExp s)
buildRepeat op size = do
    (MirExp tp e) <- evalOperand op
    let n = fromInteger size
    return $ MirExp (C.VectorRepr tp) (S.app $ E.VectorReplicate tp (S.app $ E.NatLit n) e)




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
      _ -> mirFail ("unimplemented unsigned bvext: " ++ show tp ++ "  " ++ show w)

extendSignedBV :: (1 <= w) => MirExp s -> NatRepr w -> MirGenerator h s ret (MirExp s)
extendSignedBV (MirExp tp e) w = 
    case tp of
      (C.BVRepr n) | Just Refl <- testEquality w n ->
                return $ MirExp tp e
      (C.BVRepr n) | Just LeqProof <- testLeq (incNat w) n ->
                return $ MirExp (C.BVRepr w) (S.app $ E.BVTrunc w n e)
      (C.BVRepr n) | Just LeqProof <- testLeq (incNat n) w ->
                return $ MirExp (C.BVRepr w) (S.app $ E.BVSext w n e)
      _ -> mirFail $ "unimplemented signed bvext " ++ show tp ++ " " ++ show w


evalCast' :: HasCallStack => M.CastKind -> M.Ty -> MirExp s -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast' ck ty1 e ty2  =
    case (ck, ty1, ty2) of
      (M.Misc,a,b) | a == b -> return e

      (M.Misc, M.TyUint M.USize, M.TyInt M.USize)
       | MirExp UsizeRepr e0 <- e
       -> return $ MirExp IsizeRepr (usizeToIsize R.App e0)
      (M.Misc, M.TyInt M.USize, M.TyUint M.USize)
       | MirExp IsizeRepr e0 <- e
       -> return $ MirExp UsizeRepr (isizeToUsize R.App e0)

      (M.Misc, M.TyUint _, M.TyInt  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp IsizeRepr (bvToIsize sz R.App e0)

      (M.Misc, M.TyUint _, M.TyUint  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp UsizeRepr (bvToUsize sz R.App e0)

      (M.Misc, M.TyInt _, M.TyInt  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp IsizeRepr (sbvToIsize sz R.App e0)

      (M.Misc, M.TyInt _, M.TyUint  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp UsizeRepr (sbvToUsize sz R.App e0)

      (M.Misc, M.TyUint M.USize, M.TyUint bsz)
       | MirExp UsizeRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w -> return $
         MirExp (C.BVRepr w) (usizeToBv w R.App e0)

      (M.Misc, M.TyInt M.USize, M.TyUint bsz)
       | MirExp IsizeRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w -> return $
         MirExp (C.BVRepr w) (isizeToBv w R.App e0)

      (M.Misc, M.TyUint M.USize, M.TyInt bsz)
       | MirExp UsizeRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w -> return $
         MirExp (C.BVRepr w) (usizeToBv w R.App e0)

      (M.Misc, M.TyInt M.USize, M.TyInt bsz)
       | MirExp IsizeRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w -> return $
         MirExp (C.BVRepr w) (isizeToBv w R.App e0)

      (M.Misc, M.TyUint _, M.TyUint s) -> baseSizeToNatCont s $ extendUnsignedBV e 
      (M.Misc, M.TyInt _,  M.TyInt s)  -> baseSizeToNatCont s $ extendSignedBV e

      -- unsigned to signed (nothing to do except fix sizes)
      (M.Misc, M.TyUint _, M.TyInt s)  -> baseSizeToNatCont s $ extendUnsignedBV e

      -- signed to unsigned.  Testing indicates that this sign-extends.
      (M.Misc, M.TyInt _,  M.TyUint s) -> baseSizeToNatCont s $ extendSignedBV e

       -- boolean to nat
      (M.Misc, TyBool, TyUint M.USize)
       | MirExp C.BoolRepr e0 <- e
       -> return $ MirExp UsizeRepr (R.App $ usizeIte e0 (R.App $ usizeLit 1) (R.App $ usizeLit 0))
      (M.Misc, TyBool, TyInt M.USize)

       -- boolean to integer
       | MirExp C.BoolRepr e0 <- e
       -> return $ MirExp IsizeRepr (R.App $ isizeIte e0 (R.App $ isizeLit 1) (R.App $ isizeLit 0))

      -- booleans to BVs
      (M.Misc, TyBool, TyUint bsz)
       | MirExp C.BoolRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w -> 
           return $ MirExp (C.BVRepr w) (R.App $ E.BVIte e0 w (R.App $ E.BVLit w 1) (R.App $ E.BVLit w 0))
      (M.Misc, TyBool, TyInt bsz)
       | MirExp C.BoolRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w -> 
           return $ MirExp (C.BVRepr w) (R.App $ E.BVIte e0 w (R.App $ E.BVLit w 1) (R.App $ E.BVLit w 0))

      -- char to uint
      (M.Misc, M.TyChar, M.TyUint  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp UsizeRepr (bvToUsize sz R.App e0)
      (M.Misc, M.TyChar, M.TyUint s) -> baseSizeToNatCont s $ extendUnsignedBV e




{-      -- BV to Float
      (M.Misc, M.TyInt bsz, TyFloat fsz) 
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp C.FloatRepr -}

      -- Not sure why this appears in generated MIR, but libcore has some no-op
      -- unsizes from `*const dyn Any` to `*const dyn Any`
      (M.Unsize,a,b) | a == b -> return e

      (M.Unsize, M.TyRef (M.TyArray tp sz) M.Immut, M.TyRef (M.TySlice tp') M.Immut)
        | tp == tp', MirExp (C.VectorRepr elem_tp) ref <- e
        -> do let start = R.App $ usizeLit 0
              let len   = R.App $ usizeLit (fromIntegral sz)
              vec <- mirVector_fromVector elem_tp ref
              let tup   = S.mkStruct
                              (Ctx.Empty Ctx.:> MirVectorRepr elem_tp Ctx.:> UsizeRepr Ctx.:> UsizeRepr)
                              (Ctx.Empty Ctx.:> vec Ctx.:> start Ctx.:> len)
              return $ MirExp (MirImmSliceRepr elem_tp) tup
        | otherwise -> mirFail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2


      (M.Unsize, M.TyRef (M.TyArray tp _sz) M.Mut, M.TyRef (M.TySlice tp') M.Immut)
        | tp == tp' -> mirFail "FIXME! implement mut->immut unsize cast!"
        | otherwise -> mirFail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray tp sz) M.Mut, M.TyRef (M.TySlice tp') M.Mut)
        | tp == tp', MirExp (MirReferenceRepr (C.VectorRepr elem_tp)) ref <- e
        -> do let start = R.App $ usizeLit 0
              let len   = R.App $ usizeLit (fromIntegral sz)
              vecRef <- mirRef_vectorAsMirVector elem_tp ref
              let tup   = S.mkStruct
                              (Ctx.Empty Ctx.:> MirReferenceRepr (MirVectorRepr elem_tp) Ctx.:> UsizeRepr Ctx.:> UsizeRepr)
                              (Ctx.Empty Ctx.:> vecRef Ctx.:> start Ctx.:> len)
              return $ MirExp (MirSliceRepr elem_tp) tup
        | otherwise -> mirFail $ "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

      (M.Unsize, M.TyRef (M.TyArray _ _) M.Immut, M.TyRef (M.TySlice _) M.Mut) ->
         mirFail "Cannot cast an immutable array to a mutable slice"

      -- Trait object creation from a ref
      (M.UnsizeVtable vtbl, M.TyRef baseType _,
        M.TyRef (M.TyDynamic traitName _preds) _) ->
          mkTraitObject traitName vtbl e

      -- Casting between TyDynamics that vary only in their auto traits
      -- TODO: this should also normalize the TraitProjection predicates, to
      -- allow casting between equivalent descriptions of the same trait object
      (M.Unsize, M.TyRef (M.TyDynamic t1 _) _, M.TyRef (M.TyDynamic t2 _) _)
        | t1 == t2
        -> return e

      -- C-style adts, casting an enum value to a TyInt
      (M.Misc, M.TyAdt aname _ _, M.TyInt sz) -> do
        adt <- findAdt aname
        discr <- enumDiscriminant adt mempty e
        evalCast' M.Misc (M.TyInt M.USize) discr (M.TyInt sz)
      (M.Misc, M.TyAdt aname _ _, M.TyUint sz) -> do
        adt <- findAdt aname
        discr <- enumDiscriminant adt mempty e
        evalCast' M.Misc (M.TyInt M.USize) discr (M.TyUint sz)

      -- References have the same representation as Raw pointers
      (M.Misc, M.TyRef ty1 mut1, M.TyRawPtr ty2 mut2)
         | ty1 == ty2 && mut1 == mut2 -> return e

      (M.MutToConstPointer, M.TyRawPtr ty1 M.Mut, M.TyRawPtr ty2 M.Immut)
         | MirExp (MirReferenceRepr tp) ref <- e, ty1 == ty2
         -> do r <- readMirRef tp ref
               return (MirExp tp r)

      (M.ReifyFnPointer, M.TyFnDef defId substs, M.TyFnPtr sig@(M.FnSig args ret [] [] [] _ _))
         -> do mhand <- lookupFunction defId substs
               case mhand of
                 Just (me, sig')
                   | sig == sig' -> return me
                   | otherwise -> mirFail $
                       "ReifyFnPointer: bad MIR: method handle has wrong sig: " ++
                       show (defId, substs, sig, sig')
                 Nothing -> mirFail $
                        "ReifyFnPointer: bad MIR: can't find method handle: " ++
                        show (defId, substs)

      (M.ReifyFnPointer, M.TyFnDef defId substs, M.TyFnPtr sig@(M.FnSig _ _ _ _ _ _ _))
        -> mirFail $ "ReifyFnPointer: impossible: target FnSig has generics?: "
            ++ show (defId, substs, sig)


      _ -> mirFail $ "unimplemented cast: " ++ (show ck) ++
        "\n  ty: " ++ (show ty1) ++ "\n  as: " ++ (show ty2)
 
evalCast :: HasCallStack => M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast ck op ty = do
    e <- evalOperand op
    evalCast' ck (M.typeOf op) e ty

-- | Create a new trait object by combining `e` with the named vtable.  This is
-- only valid when `e` is TyRef or TyRawPtr.  Coercions via the `CoerceUnsized`
-- trait require unpacking and repacking structs, which we don't handle here.
mkTraitObject :: HasCallStack => M.TraitName ->
    M.VtableName -> MirExp s ->
    MirGenerator h s ret (MirExp s)
mkTraitObject traitName vtableName e = do
    handles <- Maybe.fromMaybe (error $ "missing vtable handles for " ++ show vtableName) <$>
        use (cs . vtableMap . at vtableName)

    let mkEntry :: MirHandle -> MirExp s
        mkEntry (MirHandle hname _ fh) =
            MirExp (C.FunctionHandleRepr (FH.handleArgTypes fh) (FH.handleReturnType fh))
                (R.App $ E.HandleLit fh)
    vtable@(MirExp vtableTy _) <- return $ buildTuple $ map mkEntry handles

    -- Check that the vtable we constructed has the appropriate type for the
    -- trait.  A mismatch would cause runtime errors at calls to trait methods.
    trait <- Maybe.fromMaybe (error $ "unknown trait " ++ show traitName) <$>
        use (cs . collection . M.traits . at traitName)
    Some vtableTy' <- return $ traitVtableType traitName trait
    case testEquality vtableTy vtableTy' of
        Just _ -> return ()
        Nothing -> error $ unwords
            ["vtable signature mismatch for vtable", show vtableName,
                "of trait", show traitName, ":", show vtableTy, "!=", show vtableTy']

    return $ buildTuple
        [ packAny e
        , packAny vtable
        ]

-- Expressions: evaluation of Rvalues and Lvalues

evalRefLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalRefLvalue lv =
      case lv of
        M.LBase (M.Local (M.Var nm mut ty _ _ pos)) ->
          do vm <- use varMap
             e@(MirExp tpr e0) <- case Map.lookup nm vm of
               Just (Some (VarReference reg)) ->
                 do r <- G.readReg reg
                    return $ MirExp (R.typeOfReg reg) r
               Just (Some (VarRegister reg)) -> do
                 case R.typeOfReg reg of
                    MirReferenceRepr tp -> do
                      r <- G.readReg reg
                      return $ MirExp (R.typeOfReg reg) r
                    _ -> mirFail $ ("Cannot take address of non-reference" <> show  nm)
               Just (Some (VarAtom a)) -> do
                 case R.typeOfAtom a of
                    MirReferenceRepr tp -> do
                      return $ MirExp (R.typeOfAtom a) (R.AtomExpr a)
                    _ -> mirFail $ ("Cannot take address of non-reference" <> show  nm)


               _ -> mirFail ("Mutable reference-taken variable not backed by reference! " <> show nm <> " at " <> Text.unpack pos)
             case ty of
                CTyBox _
                  | MirReferenceRepr tpr' <- tpr -> do
                    e0' <- readMirRef tpr' e0
                    return $ MirExp tpr' e0'
                  | otherwise -> mirFail $ "expected MirReferenceRepr for Box<_>, but got " ++ show tpr
                _ -> return e
        M.LProj lv elm -> evalRefProj lv elm

        M.LBase (M.PStatic did _t) -> lookupStaticRef did
        M.LBase (M.PPromoted idx _t) -> do
            fn <- use currentFn
            let st = fn^.fpromoted
            case st V.!? idx of
                Just did -> lookupStaticRef did
                Nothing  -> mirFail $ "Promoted index " ++ show idx ++ " out of range "

evalRefProj :: HasCallStack => M.Lvalue -> M.PlaceElem -> MirGenerator h s ret (MirExp s)
evalRefProj base projElem =
  do --traceM $ "evalRefProj " ++ show base ++ " " ++ show projElem
     MirExp tp ref <- evalRefLvalue base
     --traceM $ "  produced evaluated base of type:" ++ show tp
     case tp of
       MirReferenceRepr elty ->
         case projElem of
          M.Deref -> case tp of
            -- This handles cases like `&mut *x.foo` where `mut x: &mut Adt`.
            -- I'm not sure if it's correct in general
            -- TODO: figure out if this is right
            MirReferenceRepr (MirReferenceRepr tp') ->
                MirExp (MirReferenceRepr tp') <$> readMirRef (MirReferenceRepr tp') ref
            _ -> return $ MirExp tp ref

          M.PField idx _mirTy -> case M.typeOf base of
              M.TyAdt nm _ _ -> do
                adt <- findAdt nm
                case adt^.adtkind of
                    Struct -> structFieldRef adt mempty idx elty ref
                    Enum -> mirFail $ "tried to access field of non-downcast enum " ++
                        show base ++ ": " ++ show (M.typeOf base)
                    Union -> mirFail $ "evalLvalue (PField, Union) NYI"

              M.TyDowncast (M.TyAdt nm _ _) i -> do
                adt <- findAdt nm
                enumFieldRef adt mempty (fromInteger i) idx elty ref

              M.TyTuple ts -> tupleFieldRef ts idx elty ref
              M.TyClosure ts -> tupleFieldRef ts idx elty ref

              _ -> error $ "tried to get field " ++ show idx ++ " of unsupported type " ++
                show (M.typeOf base) ++ ": " ++ show base ++ " (repr = " ++ show tp ++ ")"

          M.ConstantIndex offset _min_len fromend
            | C.VectorRepr tp' <- elty
            , fromend == False ->
                do let natIdx = R.App $ usizeLit (fromIntegral offset)
                   ref' <- mirRef_vectorAsMirVector tp' ref
                   r' <- subindexRef tp' ref' natIdx
                   return (MirExp (MirReferenceRepr tp') r')

            | C.VectorRepr _tp' <- elty
            , fromend == True ->
                mirFail ("FIXME: implement constant fromend indexing in reference projection")

          M.Index var
            | C.VectorRepr tp' <- elty
            -> do ref' <- mirRef_vectorAsMirVector tp' ref
                  MirExp idxTy idx <- lookupVar var
                  case idxTy of
                    UsizeRepr ->
                      do r' <- subindexRef tp' ref' idx
                         return (MirExp (MirReferenceRepr tp') r')
                    C.BVRepr w ->
                      do idxUsize <- G.forceEvaluation (bvToUsize w R.App idx)
                         r' <- subindexRef tp' ref' idxUsize
                         return (MirExp (MirReferenceRepr tp') r')

                    _ -> mirFail ("Expected index value to be an integer value in reference projection " ++
                                show base ++ " " ++ show projElem ++ " " ++ show idxTy)
          M.Downcast idx ->
            return (MirExp tp ref)
          _ -> mirFail ("Unexpected interior reference " ++ fmt base ++ " PROJECTED  " ++ show projElem
                    ++ "\n for type " ++ show elty)
       _ -> mirFail ("Expected reference value in lvalue projection: " ++ show tp ++ " " ++ show base)


evalRval :: HasCallStack => M.Rvalue -> MirGenerator h s ret (MirExp s)
evalRval (M.Use op) = evalOperand op
evalRval (M.Repeat op size) = buildRepeat op size
evalRval (M.Ref bk lv _) =
  case bk of
    M.Shared  -> evalLvalue lv
    M.Mutable -> evalRefLvalue lv
    -- &unique is a special non-shared, non-mutable borrow used in mutable
    -- closures.  The type of `&unique x` as reported by rustc is `&mut T`, but
    -- `x` is not required to be mutable.  This means we need to construct a
    -- mutable `MirReference` from a non-mutable local.  Normally this wouldn't
    -- be possible, since the local won't be a `VarReference`.  However, since
    -- we know no mutation is done through the unique ref, we can instead
    -- create a new, temporary MirReference, with no worries about mutations
    -- being lost.
    M.Unique  -> do
        MirExp tp v <- evalLvalue lv
        ref <- newMirRef tp
        writeMirRef ref v
        return $ MirExp (MirReferenceRepr tp) ref

evalRval (M.Len lv) =
  case lv of
    M.LProj lv' M.Deref
      | M.TyRef (M.TySlice _) M.Mut <- M.typeOf lv'
      -> do MirExp t e <- evalLvalue lv'
            case t of
              MirSliceRepr _tp' ->
                do let len = S.getStruct (Ctx.natIndex @2) e
                   return $ MirExp UsizeRepr len
              _ -> mirFail "Expected mutable slice value"
      | M.TyRef (M.TySlice _) M.Immut <- M.typeOf lv'
      -> do MirExp t e <- evalLvalue lv'
            case t of
              MirImmSliceRepr _tp' ->
                do let len = S.getStruct (Ctx.natIndex @2) e
                   return $ MirExp UsizeRepr len
              _ -> mirFail "Expected immutable slice value"
    _ ->
      do MirExp t e <- evalLvalue lv
         case t of
           C.VectorRepr _ -> return $ MirExp UsizeRepr $ R.App $ natToUsize R.App $ S.vectorSize e
           _ -> mirFail "len expects vector input"

evalRval (M.Cast ck op ty) = evalCast ck op ty
evalRval (M.BinaryOp binop op1 op2) = transBinOp binop op1 op2
evalRval (M.CheckedBinaryOp binop op1 op2) = transCheckedBinOp  binop op1 op2
evalRval (M.NullaryOp nop nty) = transNullaryOp  nop nty
evalRval (M.UnaryOp uop op) = transUnaryOp  uop op
evalRval (M.Discriminant lv) = do
    e <- evalLvalue lv
    let ty = typeOf lv 
    case ty of
      TyAdt aname _ _ -> do
        adt <- findAdt aname
        enumDiscriminant adt mempty e
      _ -> mirFail $ "tried to access discriminant of non-enum type " ++ show ty

evalRval (M.Aggregate ak ops) = case ak of
                                   M.AKTuple ->  do
                                       exps <- mapM evalOperand ops
                                       return $ buildTuple exps
                                   M.AKArray ty -> do
                                       exps <- mapM evalOperand ops
                                       tyToReprCont ty $ \repr ->
                                           buildArrayLit repr exps
                                   M.AKClosure _defid _substs -> do
                                       args <- mapM evalOperand ops
                                       -- Closure environments have the same
                                       -- representation as tuples.
                                       return $ buildTuple args
evalRval rv@(M.RAdtAg (M.AdtAg adt agv ops ty)) = do
    case ty of
      TyAdt _ _ _ -> do
        es <- mapM evalOperand ops
        case adt^.adtkind of
            M.Struct -> buildStruct adt mempty es
            M.Enum -> buildEnum adt mempty (fromInteger agv) es
            M.Union -> do
                mirFail $ "evalRval: Union types are unsupported, for " ++ show (adt ^. adtname)
      _ -> mirFail $ "evalRval: unsupported type for AdtAg: " ++ show ty


evalLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalLvalue (M.LBase (M.Local var)) = lookupVar var
evalLvalue (M.LProj lv (M.PField field _ty)) = do
    db <- use debugLevel
    case M.typeOf lv of

      M.TyAdt nm _ _ -> do
        adt <- findAdt nm
        case adt^.adtkind of
            Struct -> do
                e <- evalLvalue lv
                getStructField adt mempty field e
            Enum -> mirFail $ "tried to access field of non-downcast enum " ++
                show lv ++ ": " ++ show (M.typeOf lv)
            Union -> mirFail $ "evalLvalue (PField, Union) NYI"

      M.TyDowncast (M.TyAdt nm _ _) i -> do
        adt <- findAdt nm
        e <- evalLvalue lv
        getEnumField adt mempty (fromInteger i) field e

      _ -> do -- otherwise, lv is a tuple (or a closure, which has the same translation)
        ag <- evalLvalue lv
        accessAggregateMaybe ag field
evalLvalue (M.LProj (M.LProj lv M.Deref) (M.Index i))
  | M.TyRef (M.TySlice _) M.Immut <- M.typeOf lv = do
    MirExp arr_tp arr <- evalLvalue lv
    MirExp ind_tp ind <- lookupVar i
    case (arr_tp, ind_tp) of
        (MirImmSliceRepr elt_tp, UsizeRepr) -> do
            let vec = S.getStruct Ctx.i1of3 arr
            let start = S.getStruct Ctx.i2of3 arr
            let len = S.getStruct Ctx.i3of3 arr
            G.assertExpr (R.App $ usizeLt ind len)
                (S.litExpr "index out of range (for access to &[_])")
            let ind' = R.App $ usizeAdd start ind
            MirExp elt_tp <$> mirVector_lookup elt_tp vec ind'
        _ -> mirFail $ "bad types for immutable slice indexing: " ++ show (arr_tp, ind_tp)
  | M.TyRef (M.TySlice _) M.Mut <- M.typeOf lv = do
    MirExp arr_tp arr <- evalLvalue lv
    MirExp ind_tp ind <- lookupVar i
    case (arr_tp, ind_tp) of
        (MirSliceRepr elt_tp, UsizeRepr) -> do
            let vecRef = S.getStruct Ctx.i1of3 arr
            vec <- readMirRef (MirVectorRepr elt_tp) vecRef
            let start = S.getStruct Ctx.i2of3 arr
            let len = S.getStruct Ctx.i3of3 arr
            G.assertExpr (R.App $ usizeLt ind len)
                (S.litExpr "index out of range (for access to &mut [_])")
            let ind' = R.App $ usizeAdd start ind
            MirExp elt_tp <$> mirVector_lookup elt_tp vec ind'
        _ -> mirFail $ "bad types for mutable slice indexing: " ++ show (arr_tp, ind_tp)

evalLvalue (M.LProj lv (M.Index i)) = do
    (MirExp arr_tp arr) <- evalLvalue lv
    (MirExp ind_tp ind) <- lookupVar i
    case (arr_tp, ind_tp) of
      (C.VectorRepr elt_tp, UsizeRepr) -> do
          G.assertExpr (R.App $ usizeLt ind (S.app (vectorSizeUsize R.App arr)))
                       (S.litExpr "Index out of range (for access to [_; _])")
          return $ MirExp elt_tp $ S.app $ vectorGetUsize elt_tp R.App arr ind
      _ -> mirFail $ "Bad index, arr_typ is:" ++ show arr_tp ++ "\nind_type is: " ++ show ind_tp

evalLvalue (M.LProj lv M.Deref) =
   case M.typeOf lv of
     M.TyRef _ M.Immut ->
         do evalLvalue lv
     M.TyRef _ M.Mut ->
         do MirExp ref_ty ref <- evalLvalue lv
            case ref_ty of
              MirReferenceRepr tp ->
                 do r <- readMirRef tp ref
                    return $ MirExp tp r

              _ -> mirFail $ unwords ["Expected reference value in mutable dereference", show $ pretty lv]
     CTyBox _ ->
         do MirExp ref_ty ref <- evalLvalue lv
            case ref_ty of
              MirReferenceRepr tp ->
                 do r <- readMirRef tp ref
                    return $ MirExp tp r
              _ -> mirFail $ "expected MirReferenceRepr for Box<_>, but got " ++ show ref_ty
     tp ->
       mirFail $ unwords ["Expected reference type in dereference", show tp, show lv]

-- downcast: extracting the injection from an ADT. This is done in rust after switching on the discriminant.
-- We don't really do anything here --- all the action is when we project from the downcasted adt
evalLvalue (M.LProj lv (M.Downcast _i)) = do
    evalLvalue lv
-- a static reference to a function pointer should be treated like a constant??
-- NO: just lookup the function value. But we are currently mis-translating the type so we can't do this yet.
--evalLvalue (M.Promoted _ (M.TyFnDef did ss)) = do
--    transConstVal (Some (C.AnyRepr)) (M.ConstFunction did ss)
--evalLvalue (M.LStatic did t) = do

evalLvalue (M.LBase (M.PStatic did _t)) = lookupStatic did
evalLvalue (M.LBase (M.PPromoted idx _t)) = do
   fn <- use currentFn
   let st = fn^.fpromoted
   case st V.!? idx of
     Just did -> lookupStatic did
     Nothing  -> mirFail $ "Promoted index " ++ show idx ++ " out of range "
evalLvalue lv = mirFail $ "unknown lvalue access: " ++ (show lv)


-- | access a static value
lookupStatic :: M.DefId -> MirGenerator h s ret (MirExp s)
lookupStatic did = do
   sm <- use (cs.staticMap)
   case Map.lookup did sm of
     Just (StaticVar gv) -> do v <- G.readGlobal gv
                               return (MirExp (G.globalType gv) v)
     Nothing -> mirFail $ "BUG: cannot find static variable: " ++ fmt did

assignStaticExp :: M.DefId -> MirExp s -> MirGenerator h s ret ()
assignStaticExp did (MirExp rhsTy rhs) = do
   sm <- use (cs.staticMap)
   case Map.lookup did sm of
     Just (StaticVar gv) ->
       case testEquality rhsTy (G.globalType gv) of
          Just Refl -> G.writeGlobal gv rhs
          Nothing -> mirFail $ "BUG: invalid type for assignment to stat mut " ++ fmt did
     Nothing -> mirFail $ "BUG: cannot find static variable: " ++ fmt did

lookupStaticRef :: M.DefId -> MirGenerator h s ret (MirExp s)
lookupStaticRef did = do
    sm <- use (cs.staticMap)
    case Map.lookup did sm of
        Just (StaticVar gv) ->
            MirExp (MirReferenceRepr $ G.globalType gv) <$> globalMirRef gv
        Nothing -> mirFail $ "BUG: cannot find static variable: " ++ fmt did

--------------------------------------------------------------------------------------
-- ** Statements
--

-- v := mirexp
assignVarExp :: HasCallStack => M.Var -> MirExp s -> MirGenerator h s ret ()

-- Implement implict coercion from mutable reference to immutable reference.  The major
-- invariant guarantee given by the borrow checker is that, so long as the immutable
-- reference is live, the value will not change.  This justifies immediately deferencing
-- the pointer to get out the value within.
assignVarExp v@(M.Var _vnamd _ (M.TyRef _lhs_ty M.Immut) _ _ _pos)
               (MirExp (MirReferenceRepr e_ty) e) =
         do r <- readMirRef e_ty e
            assignVarExp v (MirExp e_ty r)

-- For mutable slice to immutable slice, we make a copy of the vector so that
-- we have the correct range.
assignVarExp v@(M.Var _vnamd _ (M.TyRef (M.TySlice _lhs_ty) M.Immut) _ _ _pos)
               (MirExp (MirSliceRepr e_ty) e) =
 
         do let rvec  = S.getStruct Ctx.i1of3 e
            let start = S.getStruct Ctx.i2of3 e
            let len   = S.getStruct Ctx.i3of3 e
            vec <- readMirRef (MirVectorRepr e_ty) rvec
            let struct = S.mkStruct (mirImmSliceCtxRepr e_ty)
                    (Ctx.Empty Ctx.:> vec Ctx.:> start Ctx.:> len)
            assignVarExp v (MirExp (MirImmSliceRepr e_ty) struct)

assignVarExp v@(M.Var _vnamd _ (M.TyRef M.TyStr M.Immut) _ _ _pos)
               (MirExp (MirSliceRepr e_ty) e) =

         do let rvec  = S.getStruct Ctx.i1of3 e
            let start = S.getStruct Ctx.i2of3 e
            let len   = S.getStruct Ctx.i3of3 e
            vec <- readMirRef (MirVectorRepr e_ty) rvec
            let struct = S.mkStruct (mirImmSliceCtxRepr e_ty)
                    (Ctx.Empty Ctx.:> vec Ctx.:> start Ctx.:> len)
            assignVarExp v (MirExp (MirImmSliceRepr e_ty) struct)

assignVarExp (M.Var vname _ vty _ _ pos) me@(MirExp e_ty e) = do
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
                do mirFail ("Cannot assign to atom: " <> show vname <> " of type " <> show (pretty vty) <> " at " <> Text.unpack pos)
        | otherwise ->
            mirFail $ "type error in assignment: got " ++ (show (pretty e_ty)) ++ " but expected "
                     ++ (show (varInfoRepr varinfo)) ++ " in assignment of " ++ (show vname) ++ " which has type "
                     ++ (show vty) ++ " at " ++ (Text.unpack pos)
      Nothing -> mirFail ("register not found: " ++ show vname ++ " at " ++ Text.unpack pos)

-- lv := mirexp
assignLvExp :: HasCallStack => M.Lvalue -> MirExp s -> MirGenerator h s ret ()
assignLvExp lv re = do
    case lv of
        M.LBase (M.Local var) -> assignVarExp var re
        M.LBase (M.PStatic did _) -> assignStaticExp did re
                 
        M.LProj lv (M.PField field _ty) -> do
            case M.typeOf lv of
              M.TyAdt nm _ _ -> do
                adt <- findAdt nm
                case adt^.adtkind of
                    Struct -> do
                        old <- evalLvalue lv
                        new <- setStructField adt mempty field old re
                        assignLvExp lv new
                    Enum -> mirFail $ "tried to assign to field of non-downcast enum " ++
                        show lv ++ ": " ++ show (M.typeOf lv)
                    Union -> mirFail $ "assignLvExp (PField, Union) NYI"

              M.TyDowncast (M.TyAdt nm _ _) i -> do
                adt <- findAdt nm
                old <- evalLvalue lv
                new <- setEnumField adt mempty (fromInteger i) field old re
                assignLvExp lv new

              _ -> do
                ag <- evalLvalue lv
                new_ag <- modifyAggregateIdxMaybe ag re field
                assignLvExp lv new_ag
        M.LProj lv (M.Downcast i) -> do
          assignLvExp lv re

        M.LProj (M.LProj lv' M.Deref) (M.Index v)
          | M.TyRef (M.TySlice _) M.Mut <- M.typeOf lv' ->
            do MirExp slice_tp slice <- evalLvalue lv'

               MirExp ind_tp ind     <- lookupVar v
               MirExp r_tp r         <- return re
               case (slice_tp, ind_tp) of
                 (MirSliceRepr el_tp, UsizeRepr)
                   | Just Refl <- testEquality r_tp el_tp
                   -> do let ref   = S.getStruct (Ctx.natIndex @0) slice
                         let start = S.getStruct (Ctx.natIndex @1) slice
                         let len   = S.getStruct (Ctx.natIndex @2) slice
                         G.assertExpr (R.App $ usizeLt ind len) (S.litExpr "Index out of range")
                         let ind'  = R.App $ usizeAdd start ind
                         arr <- readMirRef (MirVectorRepr el_tp) ref
                         arr' <- mirVector_update el_tp arr ind' r
                         writeMirRef ref arr'

                 _ -> mirFail $ "bad type in slice assignment"

        M.LProj lv (M.Index v) -> do
            (MirExp arr_tp arr) <- evalLvalue lv
            (MirExp ind_tp ind) <- lookupVar v
            case re of
              MirExp r_tp r ->
                case (arr_tp, ind_tp) of
                  (C.VectorRepr x, UsizeRepr) ->
                      case (testEquality x r_tp) of
                        Just Refl -> do
                          G.assertExpr (R.App $ usizeLt ind (S.app $ vectorSizeUsize R.App arr))
                                       (S.litExpr "Index out of range")
                          let arr' = MirExp arr_tp (S.app $ vectorSetUsize r_tp R.App arr ind r)
                          assignLvExp lv arr'
                        Nothing -> mirFail "bad type in assign"
                  _ -> mirFail $ "bad type in assign"
        M.LProj lv M.Deref ->
            do MirExp ref_tp ref <- evalLvalue lv
               case (ref_tp, re) of
                 (MirReferenceRepr tp, MirExp tp' e)
                   | Just C.Refl <- testEquality tp tp' -> writeMirRef ref e
                 _ -> mirFail $ unwords ["Type mismatch when assigning through a reference", show lv, ":=", show re]            
        _ -> mirFail $ "rest assign unimp: " ++ (show lv) ++ ", " ++ (show re)

-- "Allocate" space for the variable by constructing an initial value for it (if possible)
-- This code will 
storageLive :: M.Var -> MirGenerator h s ret ()
storageLive (M.Var nm _ ty _ _ _) =
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
                 Nothing -> mirFail $ "Types don't match in storageLive. Created value of type: " ++ show rty ++ " for var of type: " ++ show (varInfoRepr varinfo)
             
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
                 Nothing -> mirFail "types don't match in storageLive. This is probably a bug"
       _ -> return ()


storageDead :: M.Var -> MirGenerator h s ret ()
storageDead (M.Var nm _ _ _ _ _) =
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
  case M.typeOf lv of
    -- Currently we require that all uses of `SetDiscriminant` get bundled up
    -- with related field writes into an `RAdtAg` assignment during the
    -- AllocateEnum pass.  Ideally this transformation would not be mandatory,
    -- but the problem is, rustc emits the `SetDiscriminant` statement *after*
    -- the field writes, not before.  Our current implementation of downcast
    -- field writes requires the downcast variant index to match the enum's
    -- current variant.  If we lifted this restriction (for example, by
    -- allowing an enum value to have multiple initialized variants
    -- simultaneously), then we could remove AllocateEnum.
    ty -> mirFail $ "don't know how to set discriminant of " ++ show ty
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
transSwitch (MirExp (C.BVRepr w) e) vs ts =
    doBVBranch w e vs ts

transSwitch (MirExp f _e) _ _  = mirFail $ "bad switch: " ++ show f

doBoolBranch :: R.Expr MIR s C.BoolType -> M.BasicBlockInfo -> M.BasicBlockInfo -> MirGenerator h s ret a
doBoolBranch e t f = do
    lm <- use labelMap
    case (Map.lookup t lm, Map.lookup f lm) of
      (Just tb, Just fb) -> G.branch e tb fb
      _ -> mirFail "bad lookup on boolbranch"

-- nat branch: branch by iterating through list
doIntBranch :: R.Expr MIR s C.IntegerType -> [Integer] -> [M.BasicBlockInfo] -> MirGenerator h s ret a
doIntBranch _ _ [i] = do
    lm <- use labelMap
    case (Map.lookup i lm) of
      Just lab -> G.jump lab
      _ -> mirFail "bad jump"
doIntBranch e (v:vs) (i:is) = do
    let test = S.app $ E.IntEq e $ S.app $ E.IntLit v
    ifteAny test (jumpToBlock i) (doIntBranch e vs is)
doIntBranch _ _ _ =
    mirFail "doIntBranch: improper switch!"

-- bitvector branch: branch by iterating through list
doBVBranch :: (1 <= w) => NatRepr w -> R.Expr MIR s (C.BVType w) ->
    [Integer] -> [M.BasicBlockInfo] -> MirGenerator h s ret a
doBVBranch w _ _ [i] = do
    lm <- use labelMap
    case (Map.lookup i lm) of
      Just lab -> G.jump lab
      _ -> mirFail "bad jump"
doBVBranch w e (v:vs) (i:is) = do
    let test = S.app $ E.BVEq w e $ S.app $ E.BVLit w v
    ifteAny test (jumpToBlock i) (doBVBranch w e vs is)
doBVBranch _ _ _ _ =
    mirFail "doBVBranch: improper switch!"

jumpToBlock :: M.BasicBlockInfo -> MirGenerator h s ret a
jumpToBlock bbi = do
    lm <- use labelMap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> mirFail "bad jump"

doReturn :: HasCallStack => C.TypeRepr ret -> MirGenerator h s ret a
doReturn tr = do
    e <- lookupRetVar tr
    G.returnFromFunction e

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- | Find the function expression for this name (instantiated with the given type arguments) 
-- It could be a regular function, a static trait invocation, or a dictionary argument
-- 
-- Will return an expression of type (FnHandleType args ret)
-- 
-- Some of these predicates will turn into additional (term) arguments, but only the call
-- site knows which
lookupFunction :: forall h s ret. HasCallStack => MethName -> Substs
   -> MirGenerator h s ret (Maybe (MirExp s, FnSig))
lookupFunction nm (Substs funsubst)
  | Some k <- peanoLength funsubst = do
  db   <- use debugLevel
  when (db > 3) $
    traceM $ "**lookupFunction: trying to resolve " ++ fmt nm ++ fmt (Substs funsubst)

  -- these  are defined at the bottom of Mir.Generator
  isImpl    <- resolveFn nm (Substs funsubst)
  isCustom  <- resolveCustom nm (Substs funsubst)

  -- Given a (polymorphic) function handle, turn it into an expression by
  -- instantiating the type arguments
  let mkFunExp :: Substs -> [Param] -> FH.FnHandle a r -> MirExp s
      mkFunExp (Substs hsubst) params fhandle
        | not $ null params = error $ "BUG: function sigs should no longer include generics"
        | not $ null hsubst = error $ "BUG: function sigs should no longer have substs"
        | otherwise =
        let fargctx  = FH.handleArgTypes fhandle
            fret     = FH.handleReturnType fhandle
        in MirExp (C.FunctionHandleRepr fargctx fret) $ R.App $ E.HandleLit fhandle

  case () of 
    ()

       -- a custom function (we will find it elsewhere)
       | Just _ <- isCustom
       -> return Nothing

       -- a normal function
       | Just (MirHandle nm fs fh) <- isImpl 
       -> do
            let preds  = fs^.fspredicates
            let gens   = fs^.fsgenerics
            let hsubst = Substs $ funsubst

            when (db > 3) $ do
              traceM $ "**lookupFunction: " ++ fmt nm ++ fmt (Substs funsubst) ++ " resolved as normal call"
              traceM $ "\tpreds are " ++ fmt preds
              traceM $ "\tgens are " ++ fmt gens
              traceM $ "\thsubst is " ++ fmt hsubst

            return $ Just $ (mkFunExp hsubst gens fh, specialize fs funsubst)

       | otherwise -> do
            when (db > 1) $ do
               traceM $ "***lookupFunction: Cannot find function " ++ show nm ++ " with type args " ++ show (pretty funsubst)
            return Nothing

callHandle :: HasCallStack =>
    MirExp s -> Abi -> Maybe Int -> [M.Operand] -> MirGenerator h s ret (MirExp s)
callHandle e abi spreadArg cargs
  | MirExp (C.FunctionHandleRepr ifargctx ifret) polyinst <- e = do
    db    <- use debugLevel
    when (db > 3) $
       traceM $ fmt (PP.fillSep [PP.text "At normal function call of",
           PP.text (show e), PP.text "with arguments", pretty cargs,
           PP.text "abi:",pretty abi])

    exps <- mapM evalOperand cargs
    exps' <- case abi of
      RustCall
        -- If the target has `spread_arg` set, then it expects a tuple
        -- instead of individual arguments.  This is a hack - see comment
        -- on the definition of Mir.Mir.FnSig for details.
        | isJust $ spreadArg -> return exps

        -- Empty tuples use UnitRepr instead of StructRepr
        | [selfExp, MirExp C.UnitRepr _] <- exps -> do
          return [selfExp]

        | [selfExp, tupleExp@(MirExp (C.StructRepr tupleTys) _)] <- exps -> do
          tupleParts <- mapM (accessAggregateMaybe tupleExp)
              [0 .. Ctx.sizeInt (Ctx.size tupleTys) - 1]
          return $ selfExp : tupleParts

        | otherwise -> mirFail $
          "callExp: RustCall arguments are the wrong shape: " ++ show cargs

      _ -> return exps

    exp_to_assgn exps' $ \ctx asgn -> do
      case (testEquality ctx ifargctx) of
        Just Refl -> do
          ret_e <- G.call polyinst asgn
          return (MirExp ifret ret_e)
        _ -> mirFail $ "type error in call of " ++ show e
                      ++ "\n    args      " ++ show ctx
                      ++ "\n vs fn params " ++ show ifargctx
  | otherwise = mirFail $ "don't know how to call handle " ++ show e

-- need to construct any dictionary arguments for predicates (if present)
callExp :: HasCallStack =>
           M.DefId
        -> Substs
        -> [M.Operand]
        -> MirGenerator h s ret (MirExp s)
callExp funid funsubst cargs = do
   db    <- use debugLevel
   mhand <- lookupFunction funid funsubst
   isCustom <- resolveCustom funid funsubst
   case () of
     () | Just (CustomOp op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmt (PP.fillSep [PP.text "At custom function call of",
                 pretty funid, PP.text "with arguments", pretty cargs, 
                 PP.text "and type parameters:", pretty funsubst])

          ops <- mapM evalOperand cargs
          let opTys = map M.typeOf cargs
          op opTys ops

        | Just (CustomOpNamed op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmt (PP.fillSep [PP.text "At custom function call of",
                 pretty funid, PP.text "with arguments", pretty cargs,
                 PP.text "and type parameters:", pretty funsubst])

          ops <- mapM evalOperand cargs
          op funid ops

       | Just (CustomMirOp op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmt (PP.fillSep [PP.text "At custom function call of",
               pretty funid, PP.text "with arguments", pretty cargs, 
               PP.text "and type parameters:", pretty funsubst])
          op cargs

       | Just (hand, sig) <- mhand -> do
         callHandle hand (sig^.fsabi) (sig^.fsspreadarg) cargs

     _ -> mirFail $ "callExp: Don't know how to call " ++ fmt funid ++ fmt funsubst



-- regular function calls: closure calls & dynamic trait method calls handled later
doCall :: forall h s ret a. (HasCallStack) => M.DefId -> Substs -> [M.Operand] 
   -> Maybe (M.Lvalue, M.BasicBlockInfo) -> C.TypeRepr ret -> MirGenerator h s ret a
doCall funid funsubst cargs cdest retRepr = do
    _am    <- use $ cs.collection
    db    <- use debugLevel
    isCustom <- resolveCustom funid funsubst
    case cdest of 
      (Just (dest_lv, jdest)) -> do
            ret <- callExp funid funsubst cargs 
            assignLvExp dest_lv ret
            jumpToBlock jdest
      
      Nothing
         -- special case for exit function that does not return
         | Just (CustomOpExit op) <- isCustom -> do
               exps <- mapM evalOperand cargs
               msg  <- op exps
               G.reportError (S.app $ E.StringLit $ W4.UnicodeLiteral msg)

        -- other functions that don't return
        | otherwise -> do
            _ <- callExp funid funsubst cargs 
            -- TODO: is this the correct behavior?
            G.reportError (S.app $ E.StringLit $ fromString "Program terminated.")


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
    isCustom <- resolveCustom funid funsubsts
    doCall funid funsubsts cargs cretdest tr -- cleanup ignored

transTerminator (M.Call funcOp cargs cretdest _) tr = do
    func <- evalOperand funcOp
    ret <- callHandle func RustAbi Nothing cargs
    case cretdest of
      Just (dest_lv, jdest) -> do
          assignLvExp dest_lv ret
          jumpToBlock jdest
      Nothing -> do
          G.reportError (S.app $ E.StringLit $ fromString "Program terminated.")

transTerminator (M.Assert cond _expected _msg target _cleanup) _ = do
    db <- use $ debugLevel
    when (db > 5) $ do
       traceM $ "Skipping assert " ++ fmt cond
    jumpToBlock target -- FIXME! asserts are ignored; is this the right thing to do? NO!
transTerminator (M.Resume) tr =
    doReturn tr -- resume happens when unwinding
transTerminator (M.Drop _dl dt _dunwind) _ =
    jumpToBlock dt -- FIXME! drop: just keep going
transTerminator M.Abort tr =
    G.reportError (S.litExpr "process abort in unwinding")
transTerminator M.Unreachable tr =
    G.reportError (S.litExpr "Unreachable!!!!!")
transTerminator t _tr =
    mirFail $ "unknown terminator: " ++ (show t)


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
initialValue (CTyInt512) =
    let w = knownNat :: NatRepr 512 in
    return $ Just $ MirExp (C.BVRepr w) (S.app (E.BVLit w 0))
initialValue (CTyBox t) = do
    mv <- initialValue t
    case mv of
      Just (MirExp tp e) -> do
        ref <- newMirRef tp
        writeMirRef ref e
        return $ Just (MirExp (MirReferenceRepr tp) ref)
      Nothing -> return Nothing
initialValue (CTyVector t) = do
    tyToReprCont t $ \ tr ->
      return $ Just (MirExp (C.VectorRepr tr) (S.app $ E.VectorLit tr V.empty))
initialValue (CTyArray t) = case tyToRepr t of
    Some (C.BVRepr w) -> do
        let idxs = Ctx.Empty Ctx.:> BaseUsizeRepr
        v <- arrayZeroed idxs w
        return $ Just $ MirExp (C.SymbolicArrayRepr idxs (C.BaseBVRepr w)) v
    _ -> error $ "can't initialize array of " ++ show t ++ " (expected BVRepr)"
initialValue ty@(CTyBv _sz)
  | Some (C.BVRepr w) <- tyToRepr ty
  = return $ Just $ MirExp (C.BVRepr w) $ S.app $ E.BVLit w 0
  | otherwise = mirFail $ "Bv type " ++ show ty ++ " does not have BVRepr"
initialValue M.TyBool       = return $ Just $ MirExp C.BoolRepr (S.false)
initialValue (M.TyTuple []) = return $ Just $ MirExp C.UnitRepr (R.App E.EmptyApp)
initialValue (M.TyTuple tys) = do
    mexps <- mapM initialValue tys
    return $ Just $ buildTupleMaybe tys mexps
initialValue (M.TyInt M.USize) = return $ Just $ MirExp IsizeRepr (R.App $ isizeLit 0)
initialValue (M.TyInt sz)      = baseSizeToNatCont sz $ \w ->
    return $ Just $ MirExp (C.BVRepr w) (S.app (E.BVLit w 0))
initialValue (M.TyUint M.USize) = return $ Just $ MirExp UsizeRepr (R.App $ usizeLit 0)
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
initialValue (M.TyRef (M.TyDynamic _ _) _) = do
    let x = R.App $ E.PackAny knownRepr $ R.App $ E.EmptyApp
    return $ Just $ MirExp knownRepr $ R.App $ E.MkStruct knownRepr $
        Ctx.Empty Ctx.:> x Ctx.:> x
initialValue (M.TyRawPtr (M.TyDynamic _ _) _) = do
    let x = R.App $ E.PackAny knownRepr $ R.App $ E.EmptyApp
    return $ Just $ MirExp knownRepr $ R.App $ E.MkStruct knownRepr $
        Ctx.Empty Ctx.:> x Ctx.:> x
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
initialValue (M.TyClosure tys) = do
    mexps <- mapM initialValue tys
    return $ Just $ buildTupleMaybe tys mexps

initialValue (M.TyAdt nm _ _) = do
    adt <- findAdt nm
    case adt ^. adtkind of
        Struct -> do
            let var = M.onlyVariant adt
            fldExps <- mapM (initField mempty) (var^.M.vfields)
            Just <$> buildStruct' adt mempty fldExps
        Enum -> case adt ^. adtvariants of
            -- Uninhabited enums can't be initialized.
            [] -> return Nothing
            -- Inhabited enums get initialized to their first variant.
            (var : _) -> do
                fldExps <- mapM (initField mempty) (var^.M.vfields)
                Just <$> buildEnum' adt mempty 0 fldExps
        Union -> return Nothing
initialValue (M.TyFnPtr _) = return $ Nothing
initialValue (M.TyDynamic _ _) = return $ Nothing
initialValue (M.TyProjection _ _) = return $ Nothing
initialValue _ = return Nothing

initField :: Substs -> Field -> MirGenerator h s ret (Maybe (MirExp s))
initField args (Field _name ty _subst) = initialValue (tySubst args ty)

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
           do 
              reg <- G.newUnassignedReg (MirReferenceRepr tp)
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

 g (M.LBase (M.Local (M.Var nm _ _ _ _ _))) = Set.singleton nm
 g (M.LProj lv _) = g lv

 g _ = mempty


buildIdentMapRegs :: forall h s ret. HasCallStack => M.MirBody -> [M.Var] -> MirGenerator h s ret (VarMap s)
buildIdentMapRegs (M.MirBody localvars blocks) extravars =
   buildIdentMapRegs_ addressTakenVars needsInitVars (map (\(M.Var name _ ty _ _ _) -> (name,ty)) (localvars ++ extravars))
 where
   addressTakenVars = mconcat (map addrTakenVars blocks)
   -- "allocate" space for return variable

   -- Does MIR allow initializing the local field-by-field?
   allowsFieldwiseInit (M.Var _ _ (M.TyTuple (_:_)) _ _ _) = True
   allowsFieldwiseInit (M.Var _ _ (M.TyAdt _ _ _) _ _ _) = True
   allowsFieldwiseInit _ = False

   needsInit v = v ^. varIsZST || allowsFieldwiseInit v

   needsInitVars = Set.fromList $ ["_0"] ++ (map (^.varname) (filter needsInit localvars))


buildLabelMap :: forall h s ret. M.MirBody -> MirGenerator h s ret (LabelMap s)
buildLabelMap (M.MirBody _ blocks) = Map.fromList <$> mapM buildLabel blocks

buildLabel :: forall h s ret. M.BasicBlock -> MirGenerator h s ret (M.BasicBlockInfo, R.Label s)
buildLabel (M.BasicBlock bi _) = do
    lab <- G.newLabel
    return (bi, lab)

-- | Build the initial state for translation of functions
initFnState :: (?debug::Int,?customOps::CustomOpMap,?assertFalseOnError::Bool)
            => CollectionState
            -> Fn
            -> FH.FnHandle args ret 
            -> Ctx.Assignment (R.Atom s) args      -- ^ register assignment for args 
            -> FnState s
initFnState colState fn handle inputs =
  FnState { _varMap     = mkVarMap (reverse argtups) argtypes inputs Map.empty,
            _currentFn  = fn,
            _debugLevel = ?debug,
            _cs         = colState,
            _labelMap   = Map.empty,
            _customOps  = ?customOps,
            _assertFalseOnError = ?assertFalseOnError
         }
    where
      args = fn^.fargs

      argtups  = map (\(M.Var n _ t _ _ _) -> (n,t)) args
      argtypes = FH.handleArgTypes handle

      mkVarMap :: [(Text.Text, M.Ty)] -> C.CtxRepr args -> Ctx.Assignment (R.Atom s) args -> VarMap s -> VarMap s
      mkVarMap [] ctx _ m
            | Ctx.null ctx = m
            | otherwise = error "wrong number of args"
      mkVarMap ((name,ti):ts) ctx asgn m =
            unfold_ctx_assgn ti ctx asgn $ \(Some atom) ctx' asgn' ->
                 mkVarMap ts ctx' asgn' (Map.insert name (Some (VarAtom atom)) m)


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
      _ -> mirFail "bad label"



-------------------------------------------------------------------------------------------



-- | Translate a MIR function, returning a jump expression to its entry block
-- argvars are registers
-- The first block in the list is the entrance block
genFn :: HasCallStack => M.Fn -> C.TypeRepr ret -> MirGenerator h s ret (R.Expr MIR s ret)
genFn (M.Fn fname argvars sig body@(MirBody localvars blocks) statics) rettype = do

  let gens  = sig^.fsgenerics
  let preds = sig^.fspredicates
  let atys  = sig^.fsassoc_tys
  
  lm <- buildLabelMap body
  labelMap .= lm

  vm' <- buildIdentMapRegs body []
  varMap %= Map.union vm'

  case localvars of
    (var0 : _) -> storageLive var0
    _ -> return ()

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
    _ -> mirFail "bad thing happened"

transDefine :: forall h.
  ( HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool
  , ?printCrucible::Bool) 
  => CollectionState 
  -> M.Fn 
  -> ST h (Text, Core.AnyCFG MIR)
transDefine colState fn@(M.Fn fname fargs fsig _ _) =
  case (Map.lookup fname (colState^.handleMap)) of
    Nothing -> fail "bad handle!!"
    Just (MirHandle _hname _hsig (handle :: FH.FnHandle args ret)) -> do
      let rettype  = FH.handleReturnType handle
      let def :: G.FunctionDef MIR FnState args ret (ST s2)
          def inputs = (s,f) where
            s = initFnState colState fn handle inputs 
            f = genFn fn rettype
      ng <- newSTNonceGenerator
      (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos ng handle def
      when ?printCrucible $ do
          traceM $ unwords [" =======", show fname, "======="]
          traceShowM $ pretty g
          traceM $ unwords [" ======= end", show fname, "======="]
      case SSA.toSSA g of
        Core.SomeCFG g_ssa -> return (M.idText fname, Core.AnyCFG g_ssa)


-- | Allocate method handles for each of the functions in the Collection
-- Fn preds must include *all* predicates necessary for translating
-- the fbody at this point (i.e. "recursive" predicates for impls)
-- and these preds must already have their associated types abstracted???
mkHandleMap :: (HasCallStack) => Collection -> FH.HandleAllocator -> IO HandleMap
mkHandleMap col halloc = mapM mkHandle (col^.functions) where

    mkHandle :: M.Fn -> IO MirHandle
    mkHandle (M.Fn fname fargs ty _fbody _statics)  =
       let
           targs = map typeOf fargs
           handleName = FN.functionNameFromText (M.idText fname)
       in
          tyListToCtx targs $ \argctx -> do
          tyToReprCont (ty^.fsreturn_ty) $ \retrepr -> do
             h <- FH.mkHandle' halloc handleName argctx retrepr
             return $ MirHandle fname ty h 

vtableShimName :: M.VtableName -> M.DefId -> Text
vtableShimName vtableName fnName =
    M.idText vtableName <> "$shim$" <> M.idText fnName

vtableShimSig :: M.VtableName -> M.DefId -> FnSig -> FnSig
vtableShimSig vtableName fnName sig = sig & M.fsarg_tys %~ \xs -> case xs of
    [] -> error $ unwords
        ["function", show fnName, "in", show vtableName, "has no receiver arg"]
    (_ : tys) -> M.TyErased : tys

-- | Allocate method handles for all vtable shims.
mkVtableMap :: (HasCallStack) => Collection -> FH.HandleAllocator -> IO VtableMap
mkVtableMap col halloc = mapM mkVtable (col^.vtables)
  where
    mkVtable :: M.Vtable -> IO [MirHandle]
    mkVtable (M.Vtable name items) = mapM (mkHandle name) items

    mkHandle :: M.DefId -> M.VtableItem -> IO MirHandle
    mkHandle vtableName (VtableItem fnName _)
      | Just fn <- Map.lookup fnName (col^.functions) =
        let shimSig = vtableShimSig vtableName fnName (fn ^. M.fsig)
            handleName = FN.functionNameFromText (vtableShimName vtableName fnName)
        in
            tyListToCtx (shimSig ^. M.fsarg_tys) $ \argctx -> do
            tyToReprCont (shimSig ^. M.fsreturn_ty) $ \retrepr -> do
                h <- FH.mkHandle' halloc handleName argctx retrepr
                return $ MirHandle fnName shimSig h
      | otherwise = error $ unwords ["undefined function", show fnName, "in", show vtableName]

transVtable :: forall h. (HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool)
  => CollectionState
  -> M.Vtable
  -> ST h [(Text, Core.AnyCFG MIR)]
transVtable colState (M.Vtable name items) 
  | Just handles <- Map.lookup name (colState ^. vtableMap) =
    zipWithM (transVtableShim colState name) items handles
  | otherwise = error $ unwords ["no vtableMap entry for", show name]

transVtableShim :: forall h. (HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool) 
  => CollectionState 
  -> M.VtableName
  -> M.VtableItem
  -> MirHandle
  -> ST h (Text, Core.AnyCFG MIR)
transVtableShim colState vtableName (VtableItem fnName defName)
        (MirHandle hname hsig (shimFH :: FH.FnHandle args ret)) =
    -- Unpack shim signature
    let shimArgs = FH.handleArgTypes shimFH in
    let shimRet = FH.handleReturnType shimFH in

    -- Retrieve impl Fn and FnHandle; unpack impl signature
    (\k -> case Map.lookup fnName (colState^.collection.functions) of
            Just fn -> k fn
            Nothing -> die ["failed to look up implementation", show fnName])
        $ \implFn ->
    withMethodHandle fnName (die ["failed to look up implementation", show fnName])
        $ \implFH ->
    let implMirArg0 = head $ implFn ^. M.fsig . M.fsarg_tys in
    let implArgs = FH.handleArgTypes implFH in
    let implRet = FH.handleReturnType implFH in

    -- Peel off receiver from shim and impl arg lists
    -- NB: assignments built by `tyListToCtx` are constructed in reverse order
    elimAssignmentLeft shimArgs (die ["shim has no arguments"])
        $ \eqShimArgs@Refl shimArg0 shimArgs' ->
    elimAssignmentLeft implArgs (die ["impl has no arguments"])
        $ \eqImplArgs@Refl implArg0 implArgs' ->

    -- Check equalities over Crucible (translated) types:
    -- * Non-receiver arg types of impl and shim are equal
    (\k -> case testEquality implArgs' shimArgs' of { Just x -> k x;
        Nothing -> die ["argument type mismatch:", show implArgs, "vs", show shimArgs] })
        $ \eqArgs'@Refl ->
    -- * Return types of impl and shim are equal
    (\k -> case testEquality implRet shimRet of { Just x -> k x;
        Nothing -> die ["return type mismatch:", show implRet, "vs", show shimRet] })
        $ \eqRet@Refl ->
    -- * Shim receiver type is ANY
    (\k -> case testEquality shimArg0 C.AnyRepr of { Just x -> k x;
        Nothing -> die ["shim receiver is not ANY:", show shimArg0] }) $ \eqShimArg0Any@Refl ->

    -- Construct the shim and return it
    withBuildShim implMirArg0 implArg0 implArgs' implRet implFH $ \shimDef -> do
        ng <- newSTNonceGenerator
        (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos ng shimFH shimDef
        case SSA.toSSA g of
            Core.SomeCFG g_ssa -> return (vtableShimName vtableName fnName, Core.AnyCFG g_ssa)

  where
    die :: [String] -> a
    die words = error $ unwords
        (["failed to generate vtable shim for", show vtableName,
            "entry", show defName, "(instance", show fnName, "):"] ++ words)

    withMethodHandle :: forall r.
        MethName ->
        (r) ->
        (forall args ret. FH.FnHandle args ret -> r) ->
        r
    withMethodHandle name kNothing kJust =
        case Map.lookup name (colState^.handleMap) of
            Just (MirHandle _ _ fh) -> kJust fh
            Nothing -> kNothing

    withBuildShim :: forall r recvTy argTys retTy.
        M.Ty -> C.TypeRepr recvTy -> C.CtxRepr argTys -> C.TypeRepr retTy ->
        FH.FnHandle (recvTy :<: argTys) retTy ->
        (G.FunctionDef MIR [] (C.AnyType :<: argTys) retTy (ST h) -> r) ->
        r
    withBuildShim recvMirTy recvTy argTys retTy implFH k =
        k $ buildShim recvMirTy recvTy argTys retTy implFH

    buildShim ::
        M.Ty -> C.TypeRepr recvTy -> C.CtxRepr argTys -> C.TypeRepr retTy ->
        FH.FnHandle (recvTy :<: argTys) retTy ->
        G.FunctionDef MIR [] (C.AnyType :<: argTys) retTy (ST h)
    buildShim recvMirTy recvTy argTys retTy implFH
      | M.TyRef recvMirTy' M.Immut <- recvMirTy =
        buildShimRef recvTy argTys retTy implFH
      | M.TyRef recvMirTy' M.Mut <- recvMirTy =
        buildShimMut recvTy argTys retTy implFH
      | otherwise = die ["unsupported MIR receiver type", show recvMirTy]

    buildShimRef :: forall recvTy argTys retTy.
        C.TypeRepr recvTy -> C.CtxRepr argTys -> C.TypeRepr retTy ->
        FH.FnHandle (recvTy :<: argTys) retTy ->
        G.FunctionDef MIR [] (C.AnyType :<: argTys) retTy (ST h)
    buildShimRef recvTy argTys retTy implFH argsA = (\x -> ([], x)) $ do
        let (recv, args) = splitMethodArgs argsA (Ctx.size argTys)

        callImm <- G.newLambdaLabel' recvTy
        G.defineLambdaBlock callImm $ \recvImm -> do
            G.tailCall (R.App $ E.HandleLit implFH) (recvImm <: args)

        callMut <- G.newLambdaLabel' (C.ReferenceRepr recvTy)
        G.defineLambdaBlock callMut $ \recvMut -> do
            recvImm <- G.readRef recvMut
            G.tailCall (R.App $ E.HandleLit implFH) (recvImm <: args)

        notImm <- G.newLabel
        G.continue notImm $
            G.branchMaybe (R.App $ E.UnpackAny recvTy recv) callImm notImm

        notMut <- G.newLabel
        G.continue notMut $
            G.branchMaybe (R.App $ E.UnpackAny (C.ReferenceRepr recvTy) recv) callMut notMut

        G.reportError $ R.App $ E.StringLit $ fromString $
            "bad receiver type for " ++ show fnName

    buildShimMut :: forall recvTy argTys retTy.
        C.TypeRepr recvTy -> C.CtxRepr argTys -> C.TypeRepr retTy ->
        FH.FnHandle (recvTy :<: argTys) retTy ->
        G.FunctionDef MIR [] (C.AnyType :<: argTys) retTy (ST h)
    buildShimMut recvTy argTys retTy implFH argsA = (\x -> ([], x)) $ do
        let (recv, args) = splitMethodArgs @C.AnyType @argTys argsA (Ctx.size argTys)
        recvDowncast <- G.fromJustExpr (R.App $ E.UnpackAny recvTy recv)
            (R.App $ E.StringLit $ fromString $ "bad receiver type for " ++ show fnName)
        G.tailCall (R.App $ E.HandleLit implFH) (recvDowncast <: args)

splitMethodArgs :: forall recvTy argTys s.
    Ctx.Assignment (R.Atom s) (recvTy :<: argTys) ->
    Ctx.Size argTys ->
    (R.Expr MIR s recvTy, Ctx.Assignment (R.Expr MIR s) argTys)
splitMethodArgs args argsSize =
    let (arg0, args') = splitAssignmentLeft args argsSize in
    (R.AtomExpr arg0, fmapFC R.AtomExpr args')


type (x :: k) :<: (xs :: Ctx.Ctx k) = Ctx.SingleCtx x Ctx.<+> xs

(<:) :: forall f tp ctx. f tp -> Ctx.Assignment f ctx -> Ctx.Assignment f (tp :<: ctx)
x <: xs = Ctx.singleton x Ctx.<++> xs

elimAssignmentLeft :: forall k f (ctx :: Ctx.Ctx k) r.
    Ctx.Assignment f ctx ->
    (Ctx.EmptyCtx :~: ctx -> r) ->
    (forall (tp :: k) (ctx' :: Ctx.Ctx k).
        tp :<: ctx' :~: ctx -> f tp -> Ctx.Assignment f ctx' -> r) ->
    r
elimAssignmentLeft xs kNil kCons = case Ctx.viewAssign xs of
    Ctx.AssignEmpty -> kNil Refl
    Ctx.AssignExtend xs' x' -> elimAssignmentLeft xs'
        (\Refl -> kCons Refl x' Ctx.empty)
        (\Refl x'' xs'' -> kCons Refl x'' (xs'' Ctx.:> x'))

unappendAssignment :: forall k f (xs :: Ctx.Ctx k) (ys :: Ctx.Ctx k).
    Ctx.Size ys ->
    Ctx.Assignment f (xs Ctx.<+> ys) ->
    (Ctx.Assignment f xs, Ctx.Assignment f ys)
unappendAssignment sz asn = case Ctx.viewSize sz of
    Ctx.ZeroSize ->
        -- ys ~ EmptyCtx  ->  xs <+> ys ~ xs
        (asn, Ctx.empty)
    Ctx.IncSize sz' ->
        -- ys ~ ys' ::> y'  ->  xs <+> ys ~ (xs <+> ys') ::> y'
        case Ctx.viewAssign asn of
            Ctx.AssignExtend asn' val' ->
                case unappendAssignment sz' asn' of
                    (asn1, asn2) -> (asn1, asn2 Ctx.:> val')

unwrapSingletonAssignment :: forall k f (tp :: k).
    Ctx.Assignment f (Ctx.SingleCtx tp) -> f tp
unwrapSingletonAssignment asn = case Ctx.viewAssign asn of
    Ctx.AssignExtend _ val -> val

splitAssignmentLeft :: forall k f (tp :: k) (ctx :: Ctx.Ctx k).
    Ctx.Assignment f (tp :<: ctx) ->
    Ctx.Size ctx ->
    (f tp, Ctx.Assignment f ctx)
splitAssignmentLeft xs sz =
    let (l, r) = unappendAssignment sz xs in
    (unwrapSingletonAssignment l, r)


lookupTrait :: M.Collection -> M.TraitName -> M.Trait
lookupTrait col traitName = case col ^. M.traits . at traitName of
    Just x -> x
    Nothing -> error $ "undefined trait " ++ show traitName

-- Get the function signature of the declaration of a trait method.  Raises an
-- error if the method is not found in the trait.
traitMethodSig :: M.Trait -> M.MethName -> M.FnSig
traitMethodSig trait methName = case matchedMethSigs of
    [sig] -> sig
    [] -> error $ unwords ["undefined method", show methName,
        "in trait", show (trait ^. M.traitName)]
    _ -> error $ unwords ["multiply-defined method", show methName,
        "in trait", show (trait ^. M.traitName)]
  where
    matchedMethSigs =
        Maybe.mapMaybe (\item -> case item of
            TraitMethod methName' sig | methName' == methName -> Just sig
            _ -> Nothing) (trait ^. M.traitItems)

-- Generate method handles for all virtual-call shims (IkVirtual intrinsics)
-- used in the current crate.
mkVirtCallHandleMap :: (HasCallStack) =>
    Collection -> FH.HandleAllocator -> IO HandleMap
mkVirtCallHandleMap col halloc = mconcat <$> mapM mkHandle (Map.toList $ col ^. M.intrinsics)
  where
    mkHandle :: (M.IntrinsicName, M.Intrinsic) ->
        IO (Map M.DefId MirHandle)
    mkHandle (name, intr)
      | IkVirtual dynTraitName _ <- intr ^. M.intrInst . M.inKind =
        let methName = intr ^. M.intrInst ^. M.inDefId
            methSubsts = intr ^. M.intrInst ^. M.inSubsts
            trait = lookupTrait col dynTraitName
            methSig = tySubst methSubsts $ clearSigGenerics $ traitMethodSig trait methName

            handleName = FN.functionNameFromText $ M.idText $ intr ^. M.intrName
        in liftM (Map.singleton name) $
            tyListToCtx (methSig ^. M.fsarg_tys) $ \argctx ->
            tyToReprCont (methSig ^. M.fsreturn_ty) $ \retrepr -> do
                 h <- FH.mkHandle' halloc handleName argctx retrepr
                 return $ MirHandle (intr ^. M.intrName) methSig h
      | otherwise = return Map.empty
      where

-- Generate a virtual-call shim.  The shim takes (&dyn Foo, args...), splits
-- the `&dyn` into its data-pointer and vtable components, looks up the
-- appropriate method (a vtable shim, produced by transVtableShim), and passes
-- in the data and `args...`.
transVirtCall :: forall h. (HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool)
  => CollectionState
  -> M.IntrinsicName
  -> M.MethName
  -> M.TraitName
  -> Integer
  -> ST h (Text, Core.AnyCFG MIR)
transVirtCall colState intrName methName dynTraitName methIndex
  | MirHandle hname hsig (methFH :: FH.FnHandle args ret) <- methMH =
    -- Unpack virtual-call shim signature.  The receiver should be `DynRefType`
    elimAssignmentLeft (FH.handleArgTypes methFH) (die ["method handle has no arguments"])
        $ \eqMethArgs@Refl recvTy argTys ->
    let retTy = FH.handleReturnType methFH in

    checkEq recvTy dynRefRepr (die ["method receiver is not `&dyn`/`&mut dyn`"])
        $ \eqRecvTy@Refl ->

    -- Unpack vtable type
    withSome vtableType $ \vtableStructTy ->
    elimStructType vtableStructTy (die ["vtable type is not a struct"])
        $ \eqVtableStructTy@Refl vtableTys ->

    let someVtableIdx = case Ctx.intIndex (fromInteger methIndex) (Ctx.size vtableTys) of
            Just x -> x
            Nothing -> die ["method index out of range for vtable:",
                "method =", show methIndex, "; size =", show (Ctx.size vtableTys)] in
    withSome someVtableIdx $ \vtableIdx ->

    -- Check that the vtable entry has the correct signature.
    elimFunctionHandleType (vtableTys Ctx.! vtableIdx) (die ["vtable entry is not a function"])
        $ \eqVtableEntryTy@Refl vtsArgTys vtsRetTy ->
    elimAssignmentLeft vtsArgTys (die ["vtable shim has no arguments"])
        $ \eqVtsArgs@Refl vtsRecvTy vtsArgTys ->

    checkEq vtsRecvTy C.AnyRepr (die ["vtable shim receiver is not Any"])
        $ \eqVtsRecvTy@Refl ->
    checkEq vtsArgTys argTys
        (die ["vtable shim arguments don't match method; vtable shim =",
            show vtsArgTys, "; method =", show argTys])
        $ \eqVtsArgTys@Refl ->
    checkEq vtsRetTy retTy
        (die ["vtable shim return type doesn't match method; vtable shim =",
            show vtsRetTy, "; method =", show retTy])
        $ \eqVtsRetTy@Refl ->

    do
        ng <- newSTNonceGenerator
        (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos ng methFH
            (buildShim argTys retTy vtableTys vtableIdx)
        case SSA.toSSA g of
            Core.SomeCFG g_ssa -> return (M.idText intrName, Core.AnyCFG g_ssa)

  where
    die :: [String] -> a
    die words = error $ unwords
        (["failed to generate virtual-call shim for", show methName,
            "(intrinsic", show intrName, "):"] ++ words)

    dynTrait = case colState ^. collection . M.traits . at dynTraitName of
        Just x -> x
        Nothing -> die ["undefined trait " ++ show dynTraitName]

    -- The type of the entire vtable.  Note `traitVtableType` wants the trait
    -- substs only, omitting the Self type.
    vtableType :: Some C.TypeRepr
    vtableType = traitVtableType dynTraitName dynTrait

    methMH = case Map.lookup intrName (colState ^. handleMap) of
        Just x -> x
        Nothing -> die ["failed to find method handle for", show intrName]

    buildShim ::
        C.CtxRepr argTys -> C.TypeRepr retTy -> C.CtxRepr vtableTys ->
        Ctx.Index vtableTys (C.FunctionHandleType (C.AnyType :<: argTys) retTy) ->
        G.FunctionDef MIR [] (DynRefType :<: argTys) retTy (ST h)
    buildShim argTys retTy vtableTys vtableIdx argsA = (\x -> ([], x)) $ do
        let (recv, args) = splitMethodArgs argsA (Ctx.size argTys)

        -- Extract data and vtable parts of the `&dyn` receiver
        let recvData = R.App $ E.GetStruct recv dynRefDataIndex C.AnyRepr
        let recvVtable = R.App $ E.GetStruct recv dynRefVtableIndex C.AnyRepr

        -- Downcast the vtable to its proper struct type
        errBlk <- G.newLabel
        G.defineBlock errBlk $ do
            G.reportError $ R.App $ E.StringLit $ fromString $
                unwords ["bad vtable downcast:", show dynTraitName,
                    "to", show vtableTys]

        let vtableStructTy = C.StructRepr vtableTys
        okBlk <- G.newLambdaLabel' vtableStructTy
        vtable <- G.continueLambda okBlk $ do
            G.branchMaybe (R.App $ E.UnpackAny vtableStructTy recvVtable) okBlk errBlk

        -- Extract the function handle from the vtable
        let vtsFH = R.App $ E.GetStruct vtable vtableIdx
                (C.FunctionHandleRepr (C.AnyRepr <: argTys) retTy)

        -- Call it
        G.tailCall vtsFH (recvData <: args)

withSome :: Some f -> (forall tp. f tp -> r) -> r
withSome s k = viewSome k s

elimStructType ::
    C.TypeRepr ty ->
    (r) ->
    (forall ctx. ty :~: C.StructType ctx -> C.CtxRepr ctx -> r) ->
    r
elimStructType ty kOther kStruct
  | C.StructRepr ctx <- ty = kStruct Refl ctx
  | otherwise = kOther

elimFunctionHandleType ::
    C.TypeRepr ty ->
    (r) ->
    (forall argTys retTy.
        ty :~: C.FunctionHandleType argTys retTy ->
        C.CtxRepr argTys -> C.TypeRepr retTy -> r) ->
    r
elimFunctionHandleType ty kOther kFH
  | C.FunctionHandleRepr argTys retTy <- ty = kFH Refl argTys retTy
  | otherwise = kOther

checkEq :: TestEquality f => f a -> f b ->
    r -> (a :~: b -> r) -> r
checkEq a b kNe kEq
  | Just pf <- testEquality a b = kEq pf
  | otherwise = kNe



mkDiscrMap :: M.Collection -> Map M.AdtName [Integer]
mkDiscrMap col = mconcat
    [ Map.singleton (adt^.M.adtname) (adtIndices adt col)
    | adt <- Map.elems $ col^.M.adts, adt^.M.adtkind == Enum ]



---------------------------------------------------------------------------

-- | transCollection: translate a MIR collection
transCollection ::
    (HasCallStack, ?debug::Int, ?assertFalseOnError::Bool,
     ?libCS::CollectionState, ?customOps::CustomOpMap,
     ?printCrucible::Bool) 
    => M.Collection
    -> FH.HandleAllocator
    -> IO RustModule
transCollection col halloc = do

    when (?debug > 3) $ do
      traceM $ "MIR collection"
      traceM $ show (pretty col)

    -- build up the state in the Generator

    hmap1 <- mkHandleMap col halloc 
    hmap2 <- mkVirtCallHandleMap col halloc
    let hmap = hmap1 <> hmap2

    vm <- mkVtableMap col halloc

    -- translate the statics and create the initialization code
    -- allocate references for statics
    let allocateStatic :: Static -> Map M.DefId StaticVar -> IO (Map M.DefId StaticVar)
        allocateStatic static staticMap = 
          tyToReprCont (static^.sTy) $ \staticRepr -> do
            let gname =  (M.idText (static^.sName) <> "_global")
            g <- G.freshGlobalVar halloc gname staticRepr
            return $ Map.insert (static^.sName) (StaticVar g) staticMap

    sm <- foldrM allocateStatic Map.empty (col^.statics)

    let dm = mkDiscrMap col


    let colState :: CollectionState
        colState = CollectionState hmap vm sm dm col

    -- translate all of the functions
    pairs1 <- mapM (stToIO . transDefine (?libCS <> colState)) (Map.elems (col^.M.functions))
    pairs2 <- mapM (stToIO . transVtable (?libCS <> colState)) (Map.elems (col^.M.vtables))

    pairs3 <- Maybe.catMaybes <$> mapM (\intr -> case intr^.M.intrInst of
        Instance (IkVirtual dynTraitName methodIndex) methodId substs ->
            stToIO $ Just <$> transVirtCall (?libCS <> colState)
                (intr^.M.intrName) methodId dynTraitName methodIndex
        _ -> return Nothing) (Map.elems (col ^. M.intrinsics))

    return $ RustModule
                { _rmCS    = colState
                , _rmCFGs  = Map.fromList (pairs1 <> concat pairs2 <> pairs3)
                }

-- | Produce a crucible CFG that initializes the global variables for the static
-- part of the crate
transStatics :: CollectionState -> FH.HandleAllocator -> IO (Core.AnyCFG MIR)
transStatics colState halloc = do
  let sm = colState^.staticMap
  let hmap = colState^.handleMap
  let initializeStatic :: forall h s r . Static -> G.Generator MIR s (Const ()) r (ST h) ()
      initializeStatic static = do
        case Map.lookup (static^.sName) sm of
          Just (StaticVar g) -> do
            let repr = G.globalType g
            case Map.lookup (static^.sName) hmap of
               Just (MirHandle _ _ (handle :: FH.FnHandle init ret))
                | Just Refl <- testEquality repr        (FH.handleReturnType handle)
                , Just Refl <- testEquality (Ctx.empty) (FH.handleArgTypes handle)
                -> do  val <- G.call (G.App $ E.HandleLit handle) Ctx.empty
                       G.writeGlobal g val
               Just (MirHandle _ _ handle) ->
                  fail $ "BUG: invalid type for initializer " ++ fmt (static^.sName)
               Nothing -> fail $ "BUG: cannot find handle for static " ++ fmt (static^.sName)
          Nothing -> fail $ "BUG: cannot find global for " ++ fmt (static^.sName)

  -- TODO: make the name of the static initialization function configurable
  let initName = FN.functionNameFromText "static_initializer"
  initHandle <- FH.mkHandle' halloc initName Ctx.empty C.UnitRepr
  let def :: G.FunctionDef MIR (Const ()) Ctx.EmptyCtx C.UnitType (ST w)
      def inputs = (s, f) where
          s = Const ()
          f = do mapM_ initializeStatic (colState^.collection.statics)
                 return (R.App $ E.EmptyApp)
  init_cfg <- stToIO $ do
    ng <- newSTNonceGenerator
    (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos ng initHandle def
    case SSA.toSSA g of
        Core.SomeCFG g_ssa -> return (Core.AnyCFG g_ssa)

  return init_cfg

------------------------------------------------------------------------------------------------


--
-- Generate a loop that copies a MirVector into a Vector.
-- 
vectorCopy :: C.TypeRepr elt ->
             G.Expr MIR s UsizeType ->
             G.Expr MIR s UsizeType ->
             G.Expr MIR s (MirVectorType elt) ->
             MirGenerator h s ret (G.Expr MIR s (C.VectorType elt))
vectorCopy ety start stop inp = do
  elt <- mirVector_lookup ety inp (S.app $ usizeLit 0)
  let sz  = S.app $ usizeSub stop start
  let out = S.app $ E.VectorReplicate ety (R.App $ usizeToNat sz) elt
  ir <- G.newRef start
  or <- G.newRef out
  let pos = PL.InternalPos
  G.while (pos, do i <- G.readRef ir
                   return (G.App $ usizeLt i stop))
          (pos, do i <- G.readRef ir
                   elt <- mirVector_lookup ety inp i
                   o   <- G.readRef or
                   let j = (G.App $ usizeSub i start)
                   let o' = S.app $ vectorSetUsize ety R.App o j elt
                   G.writeRef or o'
                   G.writeRef ir (G.App $ usizeAdd i $ G.App $ usizeLit 1))
  o <- G.readRef or
  return o



--  LocalWords:  params IndexMut FnOnce Fn IntoIterator iter impl
--  LocalWords:  tovec fromelem tmethsubst MirExp initializer callExp
--  LocalWords:  mkTraitObject mkCustomTraitObject TyClosure
--  LocalWords:  transTerminator transStatement
