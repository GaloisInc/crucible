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

module Mir.Trans(transCollection,transStatics,RustModule(..)
                , readMirRef
                , writeMirRef
                , subindexRef
                , evalBinOp
                , vectorCopy
                , buildClosureType
                , callExp) where

import Control.Monad
import Control.Monad.ST

import Control.Lens hiding (op,(|>))
import Data.Foldable

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
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.SSAConversion as SSA
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Syntax as S
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.Substitution()


import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.Peano
import Data.Parameterized.BoolRepr

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



-----------------------------------------------------------------------


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

charToBV32 :: Char -> R.Expr MIR s (C.BVType 32)
charToBV32 c = R.App (E.BVLit knownRepr (toInteger (Char.ord c)))

u8ToBV8 :: ConstVal -> R.Expr MIR s (C.BVType 8)
u8ToBV8 (ConstInt (U8 c)) = R.App (E.BVLit knownRepr c)
u8ToBV8 _ = error $ "BUG: array literals should only contain bytes (u8)"
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
transConstVal (Some (C.VectorRepr _w)) (M.ConstStr str)
      = do let u32    = C.BVRepr (knownRepr :: NatRepr 32)
           let bytes  = V.fromList (map charToBV32 str)
           return $ MirExp (C.VectorRepr u32) (R.App $ E.VectorLit u32 bytes)
transConstVal (Some (C.VectorRepr w)) (M.ConstArray arr)
      | Just Refl <- testEquality w (C.BVRepr (knownRepr :: NatRepr 8))
      = do let bytes = V.fromList (map u8ToBV8 arr)
           return $ MirExp (C.VectorRepr w) (R.App $ E.VectorLit w bytes)
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

transConstVal (Some _ty) (ConstInitializer funid ss) =
    callExp funid ss [] 
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

-- TODO: should we differentiate between a Move and a Copy?
-- Can call Copy::copy trait if the stdlib is available
evalOperand :: HasCallStack => M.Operand -> MirGenerator h s ret (MirExp s)
evalOperand (M.Copy lv) = evalLvalue lv
evalOperand (M.Move lv) = evalLvalue lv
evalOperand (M.OpConstant (M.Constant conty conlit)) =
    case conlit of
       M.Value constval   -> transConstVal (tyToRepr conty) constval
       M.Item defId _args -> fail $ "cannot translate item " ++ show defId
       M.LitPromoted (M.Promoted idx) ->  do
          fn <- use currentFn
          let st = fn^.fpromoted
          case st V.!? idx of
            Just did -> lookupStatic did
            Nothing  -> fail $ "Promoted index " ++ show idx ++ " out of range "



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

            _ -> fail $ "No translation for binop: " ++ show bop ++ " with " ++ show ty1 ++ " and " ++ show ty2
      (MirExp C.IntegerRepr e1, MirExp C.IntegerRepr e2) ->
            case bop of
              M.Add -> return $ MirExp C.IntegerRepr (S.app $ E.IntAdd e1 e2)
              M.Sub -> return $ MirExp C.IntegerRepr (S.app $ E.IntSub e1 e2)
              M.Mul -> return $ MirExp C.IntegerRepr (S.app $ E.IntMul e1 e2)
              M.Div -> return $ MirExp C.IntegerRepr (S.app $ E.IntDiv e1 e2)
              M.Rem -> return $ MirExp C.IntegerRepr (S.app $ E.IntMod e1 e2)
              M.Lt  -> return $ MirExp (C.BoolRepr) (S.app $ E.IntLt e1 e2)
              M.Le  -> return $ MirExp (C.BoolRepr) (S.app $ E.IntLe e1 e2)
              M.Gt  -> return $ MirExp (C.BoolRepr) (S.app $ E.IntLt e2 e1)
              M.Ge  -> return $ MirExp (C.BoolRepr) (S.app $ E.IntLe e2 e1)
              M.Ne  -> return $ MirExp (C.BoolRepr) (S.app $ E.Not $ S.app $ E.IntEq e1 e2)
              M.Beq -> return $ MirExp (C.BoolRepr) (S.app $ E.IntEq e1 e2)
              _ -> fail $ "No translation for integer binop: " ++ show bop 
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

              (M.Gt, Just M.Unsigned) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVUlt n e2 e1)
              (M.Gt, Just M.Signed) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVSlt n e2 e1)
              (M.Ge, Just M.Unsigned) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVUle n e2 e1)
              (M.Ge, Just M.Signed) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVSle n e2 e1)

              (M.Ne, _) -> return $ MirExp (C.BoolRepr) (S.app $ E.Not $ S.app $ E.BVEq n e1 e2)
              (M.Beq, _) -> return $ MirExp (C.BoolRepr) (S.app $ E.BVEq n e1 e2)
              _ -> fail $ "No translation for binop: " ++ show bop ++ " for " ++ show ty1 ++ " and " ++ show ty2
      (MirExp C.BoolRepr e1, MirExp C.BoolRepr e2) ->
          case bop of
            M.BitAnd -> return $ MirExp C.BoolRepr (S.app $ E.And e1 e2)
            M.BitXor -> return $ MirExp C.BoolRepr (S.app $ E.BoolXor e1 e2)
            M.BitOr -> return $ MirExp C.BoolRepr (S.app $ E.Or e1 e2)
            M.Beq -> return $ MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.BoolXor e1 e2)
            _ -> fail $ "No translation for bool binop: " ++ fmt bop
      (MirExp C.NatRepr e1, MirExp C.NatRepr e2) ->
          case bop of
            M.Beq -> return $ MirExp C.BoolRepr (S.app $ E.NatEq e1 e2)
            M.Lt -> return $ MirExp C.BoolRepr (S.app $ E.NatLt e1 e2)
            M.Le -> return $ MirExp C.BoolRepr (S.app $ E.NatLe e1 e2)
            M.Gt -> return $ MirExp C.BoolRepr (S.app $ E.NatLt e2 e1)
            M.Ge -> return $ MirExp C.BoolRepr (S.app $ E.NatLe e2 e1)

            M.Add -> return $ MirExp C.NatRepr (S.app $ E.NatAdd e1 e2)
            M.Sub -> return $ MirExp C.NatRepr (S.app $ E.NatSub e1 e2)
            M.Mul -> return $ MirExp C.NatRepr (S.app $ E.NatMul e1 e2)
            M.Div -> return $ MirExp C.NatRepr (S.app $ E.NatDiv e1 e2)
            M.Rem -> return $ MirExp C.NatRepr (S.app $ E.NatMod e1 e2)
            M.Ne -> return $ MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.NatEq e1 e2)
            _ -> fail $ "No translation for natural number binop: " ++ fmt bop
      (MirExp C.RealValRepr e1, MirExp C.RealValRepr e2) ->
          case bop of
            M.Beq -> return $ MirExp C.BoolRepr (S.app $ E.RealEq e1 e2)
            M.Lt -> return $ MirExp C.BoolRepr (S.app $ E.RealLt e1 e2)
            M.Le -> return $ MirExp C.BoolRepr (S.app $ E.RealLe e1 e2)
            M.Gt -> return $ MirExp C.BoolRepr (S.app $ E.RealLt e2 e1)
            M.Ge -> return $ MirExp C.BoolRepr (S.app $ E.RealLe e2 e1)

            M.Add -> return $ MirExp C.RealValRepr (S.app $ E.RealAdd e1 e2)
            M.Sub -> return $ MirExp C.RealValRepr (S.app $ E.RealSub e1 e2)
            M.Mul -> return $ MirExp C.RealValRepr (S.app $ E.RealMul e1 e2)
            M.Div -> return $ MirExp C.RealValRepr (S.app $ E.RealDiv e1 e2)
            M.Rem -> return $ MirExp C.RealValRepr (S.app $ E.RealMod e1 e2)
            M.Ne -> return $ MirExp C.BoolRepr (S.app $ E.Not $ S.app $ E.RealEq e1 e2)
            _ -> fail $ "No translation for real number binop: " ++ fmt bop

      (_, _) -> fail $ "bad or unimplemented type: " ++ (fmt bop) ++ ", " ++ (show me1) ++ ", " ++ (show me2)



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
      (M.Neg, MirExp C.IntegerRepr e) -> return $ MirExp C.IntegerRepr $ S.app $ E.IntNeg e
      (M.Neg, MirExp C.RealValRepr e) -> return $ MirExp C.RealValRepr $ S.app $ E.RealNeg e
      (_ , MirExp ty e) -> fail $ "Unimplemented unary op `" ++ fmt uop ++ "' for " ++ show ty


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


evalCast' :: HasCallStack => M.CastKind -> M.Ty -> MirExp s -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast' ck ty1 e ty2  =
    case (ck, ty1, ty2) of
      (M.Misc,a,b) | a == b -> return e

      -- TODO: sketchy casts to unsized types: for now, they are implemented as infinite precision,
      -- but eventually will need to allow some configurable precision for these conversions.
      (M.Misc, M.TyUint _, M.TyInt  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp C.IntegerRepr (R.App $ E.BvToInteger sz e0)
      (M.Misc, M.TyInt _, M.TyInt  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp C.IntegerRepr (R.App $ E.SbvToInteger sz e0)

      (M.Misc, M.TyUint _, M.TyUint M.USize) -> fail "Cannot cast to unsized type"

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

      -- Trait object creation. Need this cast for closures
      (M.Unsize, M.TyRef baseType _, M.TyRef (M.TyDynamic (M.TraitPredicate traitName _:_)) _) ->
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

      -- References have the same representation as Raw pointers
      (M.Misc, M.TyRef ty1 mut1, M.TyRawPtr ty2 mut2)
         | ty1 == ty2 && mut1 == mut2 -> return e

      (M.Misc, M.TyRawPtr ty1 M.Mut, M.TyRawPtr ty2 M.Immut)
         | MirExp (MirReferenceRepr tp) ref <- e, ty1 == ty2
         -> do r <- readMirRef tp ref
               return (MirExp tp r)


      _ -> fail $ "unimplemented cast: " ++ (show ck) ++ " " ++ (show ty1) ++ " as " ++ (show ty2)
 
evalCast :: HasCallStack => M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
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
    mkCustomTraitObject traitName baseType e

-- Expressions: evaluation of Rvalues and Lvalues

evalRefLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalRefLvalue lv =
      case lv of
        M.Local (M.Var nm mut ty _ pos) ->
          do vm <- use varMap
             case Map.lookup nm vm of
               Just (Some (VarReference reg)) ->
                 do r <- G.readReg reg
                    return $ MirExp (R.typeOfReg reg) r
               Just (Some (VarRegister reg)) ->
                 case R.typeOfReg reg of
                    MirReferenceRepr tp -> do
                      r <- G.readReg reg
                      return $ MirExp (R.typeOfReg reg) r
                    _ -> fail $ ("Cannot take address of non-reference" <> show  nm)
               Just (Some (VarAtom a)) ->
                 case R.typeOfAtom a of
                    MirReferenceRepr tp -> do
                      return $ MirExp (R.typeOfAtom a) (R.AtomExpr a)
                    _ -> fail $ ("Cannot take address of non-reference" <> show  nm)


               _ -> fail ("Mutable reference-taken variable not backed by reference! " <> show nm <> " at " <> Text.unpack pos)
        M.LProjection proj -> evalRefProj proj

        _ -> fail ("FIXME! evalRval, Ref for non-local lvars" ++ show lv)

getVariant :: HasCallStack => M.Ty -> MirGenerator h s ret (M.Variant, Substs)
getVariant (M.TyAdt nm args) = do
    am <- use $ cs.collection
    case Map.lookup nm (am^.adts) of
       Nothing -> fail ("Unknown ADT: " ++ show nm)
       Just (M.Adt _ [struct_variant]) -> return (struct_variant, args)
       _      -> fail ("Expected ADT with exactly one variant: " ++ show nm)
getVariant (M.TyDowncast (M.TyAdt nm args) ii) = do
    let i = fromInteger ii
    am <- use $ cs.collection
    case Map.lookup nm (am^.adts) of
       Nothing -> fail ("Unknown ADT: " ++ show nm)
       Just (M.Adt _ vars) | i < length vars -> return $ (vars !! i, args)
       _      -> fail ("Expected ADT with more than " ++ show i ++ " variants: " ++ show nm)
getVariant ty = fail $ "Variant type expected, received " ++ show (pretty ty) ++ " instead"

evalRefProj :: HasCallStack => M.LvalueProjection -> MirGenerator h s ret (MirExp s)
evalRefProj prj@(M.LvalueProjection base projElem) =
  do --traceM $ "evalRefProj:" ++ fmt prj ++ " of type " ++ fmt (typeOf prj) 
     MirExp tp ref <- evalRefLvalue base
     --traceM $ "produced evaluated base of type:" ++ show tp
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
          M.Downcast idx ->
            return (MirExp tp ref)
          _ -> fail ("Unexpected interior reference " ++ fmt base ++ " PROJECTED  " ++ show projElem
                    ++ "\n for type " ++ show elty)
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



transCustomAgg :: CustomAggregate -> MirGenerator h s ret (MirExp s) -- deprecated
transCustomAgg (CARange _ty f1 f2) = evalRval (Aggregate AKTuple [f1,f2])


-- A closure is  of the form [handle, tuple of arguments] (packed into an any)
-- (arguments being those variables packed into the closure, not the function arguments)
-- NOTE: what if the closure has a polymorphic types?? How can we tell?
buildClosureHandle :: M.DefId      -- ^ name of the function
                    -> Substs      -- ^ types of the closed over variables 
                    -> [MirExp s]  -- ^ values of the closed over variables
                    -> MirGenerator h s ret (MirExp s)
buildClosureHandle funid (Substs tys) args
  = tyListToCtx tys $ \ subst -> do
      hmap <- use $ cs.handleMap
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

-- | returns type of the closure paired with type of the arguments.
buildClosureType ::
      M.DefId
   -> Substs
   -> MirGenerator h s ret (Some C.TypeRepr, Some C.TypeRepr) 
buildClosureType defid (Substs (_:_:args)) = do
    hmap <- use $ cs.handleMap
    case (Map.lookup defid hmap) of
      Just (MirHandle _ _sig fhandle) -> do
          tyListToCtx args $ \argsctx -> do
              reprsToCtx [Some (FH.handleType fhandle), Some C.AnyRepr] $ \t ->
                  return $ (Some (C.StructRepr t), Some (C.StructRepr argsctx))
      _ ->
       do fail ("buildClosureType: unknown function: " ++ show defid)
buildClosureType defid ss = fail $ "BUG: incorrect substitution in buildClosureType: " ++ fmt ss


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
                 -- copy the vector according to the slice information
                 do let vr    = S.getStruct Ctx.i1of3 ref
                    let start = S.getStruct Ctx.i2of3 ref
                    let len   = S.getStruct Ctx.i3of3 ref
                    v <- readMirRef (C.VectorRepr tp) vr
                    nv <- vectorCopy tp start (start S..+ len) v
                    return $ MirExp (C.VectorRepr tp) nv

              _ -> error $ unwords ["Expected reference value in mutable dereference", show $ pretty lv]
     tp ->
       fail $ unwords ["Expected reference type in dereference", show tp, show lv]

-- downcast: extracting the injection from an ADT. This is done in rust after switching on the discriminant.
-- We don't really do anything here --- all the action is when we project from the downcasted adt
evalLvalue (M.LProjection (M.LvalueProjection lv (M.Downcast _i))) = do
    evalLvalue lv
-- a static reference to a function pointer should be treated like a constant??
-- NO: just lookup the function value. But we are currently mis-translating the type so we can't do this yet.
--evalLvalue (M.Promoted _ (M.TyFnDef did ss)) = do
--    transConstVal (Some (C.AnyRepr)) (M.ConstFunction did ss)
--evalLvalue (M.LStatic did t) = do

evalLvalue (M.LStatic did _t) = lookupStatic did
evalLvalue (M.LPromoted idx _t) = do
   fn <- use currentFn
   let st = fn^.fpromoted
   case st V.!? idx of
     Just did -> lookupStatic did
     Nothing  -> fail $ "Promoted index " ++ show idx ++ " out of range "
evalLvalue lv = fail $ "unknown lvalue access: " ++ (show lv)


-- | access a static value
lookupStatic :: M.DefId -> MirGenerator h s ret (MirExp s)
lookupStatic did = do
   sm <- use (cs.staticMap)
   case Map.lookup did sm of
     Just (StaticVar gv) -> do v <- G.readGlobal gv
                               return (MirExp (G.globalType gv) v)
     Nothing -> fail $ "BUG: cannot find static variable: " ++ fmt did

assignStaticExp :: M.DefId -> MirExp s -> MirGenerator h s ret ()
assignStaticExp did (MirExp rhsTy rhs) = do
   sm <- use (cs.staticMap)
   case Map.lookup did sm of
     Just (StaticVar gv) ->
       case testEquality rhsTy (G.globalType gv) of
          Just Refl -> G.writeGlobal gv rhs
          Nothing -> fail $ "BUG: invalid type for assignment to stat mut " ++ fmt did
     Nothing -> fail $ "BUG: cannot find static variable: " ++ fmt did

--------------------------------------------------------------------------------------
-- ** Statements
--

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


assignVarExp (M.Var vname _ vty _ pos) me@(MirExp e_ty e) = do
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
        M.LStatic did _ -> assignStaticExp did re
                 
        M.LProjection (M.LvalueProjection lv (M.PField field _ty)) -> do

            am <- use $ cs.collection
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
   -> MirGenerator h s ret (Maybe (MirExp s, FnSig))
lookupFunction nm (Substs funsubst)
  | Some k <- peanoLength funsubst = do
  db   <- use debugLevel
  when (db > 3) $
    traceM $ "**lookupFunction: trying to resolve " ++ fmt nm ++ fmt (Substs funsubst)

  -- these  are defined at the bottom of Mir.Generator
  isStatic  <- resolveStaticTrait nm (Substs funsubst)
  isDictPrj <- resolveDictionaryProjection nm (Substs funsubst)
  isImpl    <- resolveFn nm (Substs funsubst)
  isCustom  <- resolveCustom nm (Substs funsubst)

  -- Given a (polymorphic) function handle, turn it into an expression by
  -- instantiating the type arguments
  let mkFunExp :: Substs -> [Param] -> FH.FnHandle a r -> MirExp s
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
             FalseRepr ->
                error $ "BUG: invalid number of type args to : " ++ show fhandle
                      ++ "\n" ++ show (ctxSizeP tyargs) ++ " not <= " ++ show fk
          Just Refl ->
            let polyfcn  = R.App $ E.PolyHandleLit fk fhandle
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
    ()

       -- a custom function (we will find it elsewhere)
       | Just _ <- isCustom
       -> return Nothing

       -- a normal function, resolve associated types to additional type arguments
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

       -- dictionary projection, prefer this to a static trait invocation (next case)
       | Just (var, exp, sig, Substs methsubst) <- isDictPrj
       -> do
             
             fun <- evalRval exp
             let fun' = instantiateTraitMethod fun (Substs methsubst)
             let ssig = specialize sig methsubst 
             when (db > 3) $ do
               traceM $ "**lookupFunction: " ++ fmt nm ++ fmt (Substs funsubst) ++ " resolved as dictionary projection" 
               traceM $ "\tfound var       " ++ fmt var
               traceM $ "\texp type     is " ++ fmt sig
               traceM $ "\tsubst type   is " ++ fmt ssig
               traceM $ "\tfunsubst is     " ++ fmt funsubst
               traceM $ "\tmethsubst is    " ++ fmt (Substs methsubst)

             return $ (Just (fun', ssig))

       -- a static invocation of a trait, the type argument (from funsubst) is a concrete type
       -- so we can just look up the method in the static method table
       | Just (MirHandle name sig handle, Substs methsubst) <- isStatic
       -> do

             let exp  = mkFunExp (Substs methsubst) (sig^.fsgenerics) handle
             let ssig = specialize sig methsubst

             when (db > 3) $ do
               traceM $ "**lookupFunction: " ++ fmt nm ++ fmt (Substs funsubst) ++ " resolved as static trait call" 
               traceM $ "\tfound handle    " ++ fmt name
               traceM $ "\tmirHandle ty is " ++ fmt sig
               traceM $ "\tfunsubst is     " ++ fmt (Substs funsubst)
               traceM $ "\tmethsubst is    " ++ fmt (Substs methsubst)
               traceM $ "\tspec ty is      " ++ fmt ssig

             return $ Just (exp, ssig)


       | otherwise -> do
            when (db > 1) $ do
               traceM $ "***lookupFunction: Cannot find function " ++ show nm ++ " with type args " ++ show (pretty funsubst)
            return Nothing



-- | Make a dictionary for a function call for the specified predicates
mkDict :: (Var, Predicate) -> MirGenerator h s ret (MirExp s)
mkDict (var, pred@(TraitPredicate tn (Substs ss))) = do
  db <- use debugLevel
  vm <- use varMap
  col  <- use $ cs.collection
  case Map.lookup (var^.varname) vm of
    Just _ -> lookupVar var
    Nothing -> do
      let (TyAdt did subst)              = var^.varty
      let (Adt _ [Variant _ _ fields _]) = case (col^.adts) Map.!? did of
                                             Just adt -> adt
                                             Nothing  -> error $ "Cannot find " ++ fmt did ++ " in adts"
      let go :: HasCallStack => Field -> MirGenerator h s ret (MirExp s)
          go (Field fn (TyFnPtr field_sig) _) = do
            mhand <- lookupFunction fn subst
            case mhand of
              Just (e,sig)   -> do
                 db <- use debugLevel
                 let sig'   = tySubst (Substs ss) field_sig
                     spreds = sig' ^.fspredicates
                     preds  = sig  ^.fspredicates
                 if (length preds > length spreds) then do
                    let extras = drop (length spreds) preds
                    when (db > 3) $ do
                       traceM $ fmt fn ++ " for " ++ fmt pred
                       traceM $ "sig:    " ++ fmt sig
                       traceM $ "preds:  " ++ fmt preds
                       traceM $ "fsig    " ++ fmt field_sig
                       traceM $ "spreds: " ++ fmt spreds
                       traceM $ "extras: " ++ fmt extras
                    dexps <- mapM mkDict (Maybe.mapMaybe (\x -> (,x) <$> dictVar x) extras)
                    case (e, dexps) of
                      -- TODO: this currently only handles ONE extra predicate on the method
                      -- need to generalize closure creation to *multiple* predicates
                      (MirExp (C.FunctionHandleRepr args ret) fn, [MirExp ty dict]) -> do
                         case Ctx.viewAssign args of
                            Ctx.AssignEmpty -> error $ "BUG: No arguments!"
                            Ctx.AssignExtend (rargs :: C.CtxRepr rargs)
                                             (v :: C.TypeRepr arg) -> do
                              case testEquality v ty of
                                Nothing -> error $ "BUG: dictionary type doesn't match"
                                Just Refl ->
                                  C.assumeClosed @arg $
                                  return (MirExp
                                            (C.FunctionHandleRepr rargs ret)
                                            (R.App $ E.Closure rargs ret fn v dict))
                      (_,_) -> return e
                 else
                    return e -- error $ "found predicates when building a dictionary for " ++ show var
              Nothing     -> error $ "when building a dictionary for " ++  fmt var
                                  ++ " couldn't find an entry for " ++ fmt fn
                                  ++ " of type " ++ fmt (var^.varty)
          go (Field fn ty _) = error $ "BUG: mkDict, fields must be functions, found"
                                        ++ fmt ty ++ " for " ++ fmt fn ++ " instead."
      when (db > 3) $ traceM $ "Building dictionary for " ++ fmt pred
                    ++ " of type " ++ fmt (var^.varty)
      entries <- mapM go fields
      when (db > 3) $ traceM $ "Done building dictionary for " ++ fmt var
      return $ buildTaggedUnion 0 entries
mkDict (var, _) = error $ "BUG: mkDict, only make dictionaries for TraitPredicates"

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

       | Just (CustomMirOp op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmt (PP.fillSep [PP.text "At custom function call of",
               pretty funid, PP.text "with arguments", pretty cargs, 
               PP.text "and type parameters:", pretty funsubst])
          op cargs

       | Just (MirExp (C.FunctionHandleRepr ifargctx ifret) polyinst, sig) <- mhand -> do
          when (db > 3) $
             traceM $ fmt (PP.fillSep [PP.text "At normal function call of",
                 pretty funid, PP.text "with arguments", pretty cargs,
                 PP.text "sig:",pretty sig,
                 PP.text "and type parameters:", pretty funsubst])

          exps <- mapM evalOperand cargs
          let preds = sig^.fspredicates
          dexps <- mapM mkDict (Maybe.mapMaybe (\x -> (,x) <$> (dictVar x)) preds)
          exp_to_assgn (exps ++ dexps) $ \ctx asgn -> do
            case (testEquality ctx ifargctx) of
              Just Refl -> do
                ret_e <- G.call polyinst asgn
                return (MirExp ifret ret_e)
              _ -> fail $ "type error in call of " ++ fmt funid ++ fmt funsubst
                            ++ "\n    args      " ++ show ctx
                            ++ "\n vs fn params " ++ show ifargctx

     _ -> fail $ "callExp: Don't know how to call " ++ fmt funid ++ fmt funsubst



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
               G.reportError (S.app $ E.TextLit msg)

        -- other functions that don't return
        | otherwise -> do
            _ <- callExp funid funsubst cargs 
            -- TODO: is this the correct behavior?
            G.reportError (S.app $ E.TextLit "Program terminated.")


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
    case (funsubsts, cargs) of
      (Substs (M.TyDynamic (TraitPredicate traitName _ : _):_), tobj:_args) |
       Nothing  <- isCustom -> do
        -- this is a method call on a trait object, and is not a custom function
        db <- use debugLevel
        when (db > 2) $
           traceM $ show (PP.sep [PP.text "At TRAIT function call of ",
                   pretty funid, PP.text " with arguments ", pretty cargs, 
                   PP.text "with type parameters: ", pretty funsubsts])
        fail $ "trait method calls unsupported "

      _ -> do -- this is a normal function call
        doCall funid funsubsts cargs cretdest tr -- cleanup ignored
        
transTerminator (M.Assert cond _expected _msg target _cleanup) _ = do
    db <- use $ debugLevel
    when (db > 5) $ do
       traceM $ "Skipping assert " ++ fmt cond
    jumpToBlock target -- FIXME! asserts are ignored; is this the right thing to do? NO!
transTerminator (M.Resume) tr =
    doReturn tr -- resume happens when unwinding
transTerminator (M.Drop _dl dt _dunwind) _ =
    jumpToBlock dt -- FIXME! drop: just keep going
transTerminator M.Unreachable tr =
    G.reportError (S.litExpr "Unreachable!!!!!")
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
initialValue M.TyStr = do
    let w = C.BVRepr (knownNat :: NatRepr 32)
    return $ Just $ (MirExp (C.VectorRepr w) (S.app (E.VectorLit w V.empty)))
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
    am <- use $ cs.collection
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

   isTuple (M.Var _ _ (M.TyTuple (_:_)) _ _) = True
   isTuple _ = False

   needsInitVars = Set.fromList $ ["_0"] ++ (map (^.varname) (filter isTuple localvars))


buildLabelMap :: forall h s ret. M.MirBody -> MirGenerator h s ret (LabelMap s)
buildLabelMap (M.MirBody _ blocks) = Map.fromList <$> mapM buildLabel blocks

buildLabel :: forall h s ret. M.BasicBlock -> MirGenerator h s ret (M.BasicBlockInfo, R.Label s)
buildLabel (M.BasicBlock bi _) = do
    lab <- G.newLabel
    return (bi, lab)

-- | Build the initial state for translation of functions
initFnState :: (?debug::Int,?customOps::CustomOpMap)
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
            _customOps  = ?customOps
         }
    where
      sig = fn^.fsig
      args = fn^.fargs

      argPredVars = Maybe.mapMaybe dictVar (sig^.fspredicates)
      argtups  = map (\(M.Var n _ t _ _) -> (n,t)) (args ++ argPredVars)
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
      _ -> fail "bad label"



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

transDefine :: forall h. (HasCallStack, ?debug::Int, ?customOps::CustomOpMap) 
  => CollectionState 
  -> M.Fn 
  -> ST h (Text, Core.AnyCFG MIR)
transDefine colState fn@(M.Fn fname fargs fsig _ _) =
  case (Map.lookup fname (colState^.handleMap)) of
    Nothing -> fail "bad handle!!"
    Just (MirHandle _hname _hsig (handle :: FH.FnHandle args ret)) -> do
      let rettype  = FH.handleReturnType handle
      let def :: G.FunctionDef MIR s2 FnState args ret
          def inputs = (s,f) where
            s = initFnState colState fn handle inputs 
            f = genFn fn rettype
      (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos handle def
      case SSA.toSSA g of
        Core.SomeCFG g_ssa -> return (M.idText fname, Core.AnyCFG g_ssa)


-- | Allocate method handles for each of the functions in the Collection
-- Fn preds must include *all* predicates necessary for translating
-- the fbody at this point (i.e. "recursive" predicates for impls)
-- and these preds must already have their associated types abstracted???
mkHandleMap :: forall s . (HasCallStack) => Collection -> FH.HandleAllocator s -> ST s HandleMap
mkHandleMap col halloc = mapM mkHandle (col^.functions) where

    mkHandle :: M.Fn -> ST s MirHandle
    mkHandle (M.Fn fname fargs ty _fbody _statics)  =
       let
           -- add dictionary args to type
           targs = map typeOf (fargs ++ Maybe.mapMaybe dictVar (ty^.fspredicates))
           handleName = FN.functionNameFromText (M.idText fname)
       in
          tyListToCtx targs $ \argctx -> do
          tyToReprCont (ty^.fsreturn_ty) $ \retrepr -> do
             h <- FH.mkHandle' halloc handleName argctx retrepr
             return $ MirHandle fname ty h 


---------------------------------------------------------------------------

-- | transCollection: translate a MIR collection
transCollection :: forall s. (HasCallStack, ?debug::Int, ?libCS::CollectionState, ?customOps::CustomOpMap) 
      => M.Collection
      -> FH.HandleAllocator s
      -> ST s RustModule
transCollection col halloc = do

    when (?debug > 3) $ do
      traceM $ "MIR collection"
      traceM $ show (pretty col)

    -- build up the state in the Generator

    hmap <- mkHandleMap col halloc 

    let stm = mkStaticTraitMap col

    -- translate the statics and create the initialization code
    -- allocate references for statics
    let allocateStatic :: Static -> Map M.DefId StaticVar -> ST s (Map M.DefId StaticVar)
        allocateStatic static staticMap = 
          tyToReprCont (static^.sTy) $ \staticRepr -> do
            let gname =  (M.idText (static^.sName) <> "_global")
            g <- G.freshGlobalVar halloc gname staticRepr
            case C.checkClosed staticRepr of
               Just C.Dict -> return $ Map.insert (static^.sName) (StaticVar g) staticMap
               Nothing -> error $ "BUG: Invalid type for static var: " ++ show staticRepr

    sm <- foldrM allocateStatic Map.empty (col^.statics)

    let colState :: CollectionState
        colState = CollectionState hmap stm sm col 

    -- translate all of the functions
    pairs <- mapM (transDefine (?libCS <> colState)) (Map.elems (col^.M.functions))
    return $ RustModule
                { _rmCS    = colState
                , _rmCFGs  = Map.fromList pairs 
                }

-- | Produce a crucible CFG that initializes the global variables for the static
-- part of the crate
transStatics :: CollectionState -> FH.HandleAllocator s -> ST s (Core.AnyCFG MIR)
transStatics colState halloc = do
  let sm = colState^.staticMap
  let hmap = colState^.handleMap
  let initializeStatic :: forall h s r . Static -> G.Generator MIR h s (Const ()) r ()
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
  let def :: G.FunctionDef MIR w (Const ()) Ctx.EmptyCtx C.UnitType
      def inputs = (s, f) where
          s = Const ()
          f = do mapM_ initializeStatic (colState^.collection.statics)
                 return (R.App $ E.EmptyApp)
  init_cfg <- do (R.SomeCFG g, []) <- G.defineFunction PL.InternalPos initHandle def
                 case SSA.toSSA g of
                    Core.SomeCFG g_ssa -> return (Core.AnyCFG g_ssa)

  return init_cfg

------------------------------------------------------------------------------------------------


--
-- Generate a loop that copies a vector  
-- 
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
                   let j = (G.App (E.NatSub i start))
                   let o' = S.app $ E.VectorSetEntry ety o j elt
                   G.writeRef or o'
                   G.writeRef ir (G.App (E.NatAdd i (G.App $ E.NatLit 1))))
  o <- G.readRef or
  return o



--  LocalWords:  params IndexMut FnOnce Fn IntoIterator iter impl
--  LocalWords:  tovec fromelem tmethsubst MirExp initializer callExp
--  LocalWords:  mkTraitObject mkCustomTraitObject TyClosure
--  LocalWords:  transTerminator transStatement
