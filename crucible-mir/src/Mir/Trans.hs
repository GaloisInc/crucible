{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
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
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}

module Mir.Trans(transCollection,transStatics,RustModule(..)
                , readMirRef
                , writeMirRef
                , subindexRef
                , evalBinOp
                , evalOperand
                , vectorCopy, ptrCopy, copyNonOverlapping
                , evalRval
                , callExp
                , callHandle
                , doVirtCall
                , derefExp, readPlace, addrOfPlace
                , transmuteExp
                , extendUnsignedBV
                ) where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Class

import Control.Lens hiding (op,(|>))
import qualified Control.Lens.Extras as Lens (is)
import Data.Foldable

import Data.Bits (shift, shiftL)
import qualified Data.ByteString as BS
import qualified Data.Char as Char
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Traversable as Trav
import qualified Data.Vector as V
import Data.String (fromString)
import Numeric
import Numeric.Natural()

import Prettyprinter (Pretty(..))
import qualified Prettyprinter as PP

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
import Lang.Crucible.Panic


import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Parameterized.Nonce (newSTNonceGenerator)

import Mir.Mir
import qualified Mir.Mir as M
import qualified Mir.DefId as M

import Mir.Intrinsics
import Mir.Generator
import Mir.GenericOps
import Mir.TransTy

import Mir.PP (fmt, fmtDoc)

import Debug.Trace



parsePosition :: Text.Text -> PL.Position
parsePosition posText =
  case Text.split (==':') posText of
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

transConstVal :: HasCallStack => M.Ty -> Some C.TypeRepr -> M.ConstVal -> MirGenerator h s ret (MirExp s)

-- Custom types
transConstVal (CTyBv _) (Some (C.BVRepr w)) (M.ConstStruct [M.ConstInt i, M.ConstStruct []]) = do
    val <- case M.fromIntegerLit i of
        0 -> return 0   -- Bv::ZERO
        1 -> return 1   -- Bv::ONE
        2 -> return $ (1 `shift` fromIntegral (intValue w)) - 1    -- Bv::MAX
        i' -> mirFail $ "unknown bitvector constant " ++ show i'
    return $ MirExp (C.BVRepr w) (S.app $ eBVLit w val)
transConstVal CTyMethodSpec _ _ = do
    mirFail "transConstVal: can't construct MethodSpec without an override"
transConstVal CTyMethodSpecBuilder _ _ = do
    mirFail "transConstVal: can't construct MethodSpecBuilder without an override"

transConstVal _ty (Some (C.BVRepr w)) (M.ConstInt i) =
    return $ MirExp (C.BVRepr w) (S.app $ eBVLit w (fromInteger (M.fromIntegerLit i)))
transConstVal _ty (Some (C.BoolRepr)) (M.ConstBool b) = return $ MirExp (C.BoolRepr) (S.litExpr b)
transConstVal _ty (Some (UsizeRepr)) (M.ConstInt i) =
    do let n = fromInteger (M.fromIntegerLit i)
       return $ MirExp UsizeRepr (S.app $ usizeLit n)
transConstVal _ty (Some (IsizeRepr)) (ConstInt i) =
      return $ MirExp IsizeRepr (S.app $ isizeLit (fromIntegerLit i))

--
-- This code handles slice references, both for ordinary array slices
-- and string slices. (These differ from ordinary references in having
-- a length.)  It needs to look up the definition ID, and then:
--    * extract the type from the global variable it finds
--      (note that it'll be a MirVectorRepr that it needs to unwrap)
--    * construct a reference to the global variable
--      (with globalMirRef rather than constMirRef, that's the point of
--      all this)
--    * apply subindexRef as above
--    * cons up the length
--    * call mkStruct
--    * cons up the final MirExp
--
-- staticSlicePlace does the first four of these actions; addrOfPlace
-- does the last two.
--
transConstVal (M.TyRef _ _) (Some MirSliceRepr) (M.ConstSliceRef defid len) = do
    place <- staticSlicePlace len defid
    addr <- addrOfPlace place
    return addr

transConstVal _ty (Some (MirVectorRepr u8Repr@(C.BVRepr w))) (M.ConstStrBody bs)
  | Just Refl <- testEquality w (knownNat @8) = do
    let bytes = map (\b -> R.App (eBVLit (knownNat @8) (toInteger b))) (BS.unpack bs)
    let vec = R.App $ E.VectorLit u8Repr (V.fromList bytes)
    mirVec <- mirVector_fromVector u8Repr vec
    return $ MirExp (MirVectorRepr u8Repr) mirVec

transConstVal (M.TyArray ty _sz) (Some (MirVectorRepr tpr)) (M.ConstArray arr) = do
    arr' <- Trav.for arr $ \e -> do
        MirExp tpr' e' <- transConstVal ty (Some tpr) e
        Refl <- testEqualityOrFail tpr tpr' $
            "transConstVal (ConstArray): returned wrong type: expected " ++
            show tpr ++ ", got " ++ show tpr'
        pure e'
    vec <- mirVector_fromVector tpr $ R.App $ E.VectorLit tpr $ V.fromList arr'
    return $ MirExp (MirVectorRepr tpr) vec

transConstVal _ty (Some (C.BVRepr w)) (M.ConstChar c) =
    do let i = toInteger (Char.ord c)
       return $ MirExp (C.BVRepr w) (S.app $ eBVLit w i)
transConstVal _ty (Some C.UnitRepr) (M.ConstFunction _did) =
    return $ MirExp C.UnitRepr $ S.app E.EmptyApp
transConstVal _ty (Some C.UnitRepr) (M.ConstTuple []) =
    return $ MirExp C.UnitRepr $ S.app E.EmptyApp
transConstVal (M.TyTuple tys) (Some MirAggregateRepr) (M.ConstTuple vals) =
    transConstTuple tys vals
transConstVal (M.TyClosure upvar_tys) (Some MirAggregateRepr) (M.ConstClosure upvar_vals) =
    transConstTuple upvar_tys upvar_vals

transConstVal _ty (Some (C.RealValRepr)) (M.ConstFloat (M.FloatLit _ str)) =
    case reads str of
      (d , _):_ -> let rat = toRational (d :: Double) in
                   return (MirExp C.RealValRepr (S.app $ E.RationalLit rat))
      []        -> mirFail $ "cannot parse float constant: " ++ show str

transConstVal _ty _ (ConstInitializer funid) =
    callExp funid []
transConstVal _ty _ (ConstStaticRef did) =
    staticPlace did >>= addrOfPlace
transConstVal ty _ ConstZST = initialValue ty >>= \case
    Just x -> return x
    Nothing -> mirFail $
        "failed to evaluate ZST constant of type " ++ show ty ++ " (initialValue failed)"
transConstVal _ty (Some MirReferenceRepr) (ConstRawPtr i) =
    MirExp MirReferenceRepr <$> integerToMirRef (R.App $ usizeLit i)
transConstVal ty@(M.TyAdt aname _ _) tpr (ConstStruct fields) = do
    adt <- findAdt aname
    col <- use $ cs . collection
    case findReprTransparentField col adt of
        Just idx ->
            transTransparentVal ty tpr adt fields idx
        Nothing -> do
            let fieldDefs = adt ^. adtvariants . ix 0 . vfields
            let fieldTys = map (\f -> f ^. fty) fieldDefs
            exps <- zipWithM (\val ty -> tyToReprM ty >>= \rpr -> transConstVal ty rpr val) fields fieldTys
            buildStruct adt exps

transConstVal ty@(M.TyAdt aname _ _) tpr (ConstEnum variant fields) = do
    adt <- findAdt aname
    col <- use $ cs . collection
    case findReprTransparentField col adt of
        Just idx ->
            transTransparentVal ty tpr adt fields idx
        Nothing -> do
            let fieldDefs = adt ^. adtvariants . ix variant . vfields
            let fieldTys = map (\f -> f ^. fty) fieldDefs
            exps <- zipWithM (\val ty -> tyToReprM ty >>= \rpr -> transConstVal ty rpr val) fields fieldTys
            buildEnum adt variant exps
transConstVal ty (Some MirReferenceRepr) init = do
    let pointeeTy = M.typeOfProj M.Deref ty
    Some tpr <- tyToReprM pointeeTy
    MirExp tpr' val <- transConstVal pointeeTy (Some tpr) init
    Refl <- testEqualityOrFail tpr tpr' $
        "transConstVal returned wrong type: expected " ++ show tpr ++ ", got " ++ show tpr'
    ref <- constMirRef tpr val
    return $ MirExp MirReferenceRepr ref
transConstVal _ty (Some tpr@(C.FunctionHandleRepr argTys retTy)) (ConstFnPtr did) = do
    mbHndl <- resolveFn did
    case mbHndl of
        Just (MirHandle _ _ hndl) -> do
            Refl <- testEqualityOrFail argTys (FH.handleArgTypes hndl) $ unlines
                [ "transConstVal (ConstFnPtr): argument types mismatch"
                , "expected: " ++ show argTys
                , "actual:   " ++ show (FH.handleArgTypes hndl)
                , "def id:   " ++ show did
                ]
            Refl <- testEqualityOrFail retTy (FH.handleReturnType hndl) $ unlines
                [ "transConstVal (ConstFnPtr): return type mismatch"
                , "expected: " ++ show retTy
                , "actual:   " ++ show (FH.handleReturnType hndl)
                , "def id:   " ++ show did
                ]
            return $ MirExp tpr $ R.App $ E.HandleLit hndl
        Nothing -> mirFail $
            "transConstVal (ConstFnPtr): Couldn't resolve function " ++ show did
transConstVal ty tp cv = mirFail $
    "fail or unimp constant: " ++ show ty ++ " (" ++ show tp ++ ") " ++ show cv

-- Translate a constant (non-empty) tuple or constant closure value.
transConstTuple :: [M.Ty] -> [ConstVal] -> MirGenerator h s ret (MirExp s)
transConstTuple tys vals = do
    exps <- forM (zip tys vals) $ \(ty, val) -> do
        Some tpr <- tyToReprM ty
        transConstVal ty (Some tpr) val
    buildTupleMaybeM tys (map Just exps)

-- Translate a struct or enum marked with repr(transparent).
transTransparentVal ::
  M.Ty {- The transparent struct or enum type (only used for error messages) -} ->
  Some C.TypeRepr {- The Crucible representation of the transparent struct or
                     enum type. -} ->
  Adt {- The transparent struct or enum's Adt description. -} ->
  [ConstVal] {- The field values of the transparent struct or enum variant.
                Really, it should only be a single field value, but we must
                check that this is actually the case. -} ->
  Int {- The index of the underlying field in the variant. -} ->
  MirGenerator h s ret (MirExp s)
transTransparentVal ty tpr adt fields idx = do
    ty <- case adt ^? adtvariants . ix 0 . vfields . ix idx . fty of
        Just x -> return x
        Nothing -> mirFail $ "repr(transparent) field index " ++ show idx ++
            " out of range for " ++ show (pretty ty)
    const <- case fields ^? ix idx of
        Just x -> return x
        Nothing -> mirFail $ "repr(transparent) field index " ++ show idx ++
            " out of range for " ++ show (pretty ty) ++ " initializer"
    transConstVal ty tpr const

typedVarInfo :: HasCallStack => Text -> C.TypeRepr tp -> MirGenerator h s ret (VarInfo s tp)
typedVarInfo name tpr = do
    optV <- use $ varMap . at name
    case optV of
        Nothing -> mirFail $
            "variable " ++ show name ++ " not found"
        Just (Some vi) -> do
            let tpr' = varInfoRepr vi
            Refl <- testEqualityOrFail tpr tpr' $
                "expected var " ++ show name ++ " to have type " ++ show tpr
                    ++ ", but it has type " ++ show tpr' ++ " instead"
            return vi

readVar :: C.TypeRepr tp -> VarInfo s tp -> MirGenerator h s ret (R.Expr MIR s tp)
readVar tpr vi = do
    case vi of
        VarRegister reg -> G.readReg reg
        VarReference _ reg -> G.readReg reg >>= readMirRef tpr
        VarAtom a -> return $ R.AtomExpr a

varExp :: HasCallStack => M.Var -> MirGenerator h s ret (MirExp s)
varExp (M.Var vname _ vty _) = do
    Some tpr <- tyToReprM vty
    vi <- typedVarInfo vname tpr
    x <- readVar tpr vi
    return $ MirExp tpr x

varPlace :: HasCallStack => M.Var -> MirGenerator h s ret (MirPlace s)
varPlace (M.Var vname _ vty _) = do
    Some tpr <- tyToReprM vty
    vi <- typedVarInfo vname tpr
    r <- case vi of
        VarReference _ reg -> G.readReg reg
        -- TODO: these cases won't be needed once immutable ref support is done
        -- - make them report an error instead
        VarRegister reg -> do
            x <- G.readReg reg
            r <- constMirRef tpr x
            return r
        VarAtom a -> do
            r <- constMirRef tpr $ R.AtomExpr a
            return r
    return $ MirPlace tpr r NoMeta

staticPlace :: HasCallStack => M.DefId -> MirGenerator h s ret (MirPlace s)
staticPlace did = do
    sm <- use $ cs.staticMap
    case Map.lookup did sm of
        Just (StaticVar gv) ->
            MirPlace (G.globalType gv) <$> globalMirRef gv <*> pure NoMeta
        Nothing -> mirFail $ "cannot find static variable " ++ fmt did

-- variant of staticPlace for slices
-- tpr is the element type; len is the length
staticSlicePlace :: HasCallStack => Int -> M.DefId -> MirGenerator h s ret (MirPlace s)
staticSlicePlace len did = do
    sm <- use $ cs.staticMap
    case Map.lookup did sm of
        Just (StaticVar gv) -> do
            let tpr_found = G.globalType gv
            Some tpr <- case tpr_found of
                MirVectorRepr tpr -> return $ Some tpr
                _ -> mirFail $
                    "staticSlicePlace: wrong type: expected vector, found " ++ show tpr_found
            ref <- globalMirRef gv
            ref' <- subindexRef tpr ref (R.App $ usizeLit 0)
            let len' = R.App $ usizeLit $ fromIntegral len
            return $ MirPlace tpr ref' (SliceMeta len')
        Nothing -> mirFail $ "cannot find static variable " ++ fmt did

-- NOTE: The return var in the MIR output is always "_0"
getReturnExp :: HasCallStack => C.TypeRepr ret -> MirGenerator h s ret (R.Expr MIR s ret)
getReturnExp tpr = do
    vi <- typedVarInfo "_0" tpr
    readVar tpr vi


-- ** Expressions: Operations and Aggregates

evalOperand :: HasCallStack => M.Operand -> MirGenerator h s ret (MirExp s)
evalOperand (M.Copy lv) = evalPlace lv >>= readPlace
evalOperand (M.Move lv) = evalPlace lv >>= readPlace
evalOperand (M.OpConstant (M.Constant conty constval)) = do
    Some tpr <- tyToReprM conty
    transConstVal conty (Some tpr) constval
evalOperand (M.Temp rv) = evalRval rv

-- | Dereference a `MirExp` (which must be `MirReferenceRepr` pointing to a
-- sized type), producing a `MirPlace`.
derefExp :: HasCallStack => M.Ty -> MirExp s -> MirGenerator h s ret (MirPlace s)
derefExp pointeeTy (MirExp MirReferenceRepr e) = do
    Some tpr <- tyToReprM pointeeTy
    return $ MirPlace tpr e NoMeta
derefExp pointeeTy (MirExp tpr _) = mirFail $ "don't know how to deref " ++ show tpr

readPlace :: HasCallStack => MirPlace s -> MirGenerator h s ret (MirExp s)
readPlace (MirPlace tpr r NoMeta) = MirExp tpr <$> readMirRef tpr r
readPlace (MirPlace tpr _ meta) =
    mirFail $ "don't know how to read from place with metadata " ++ show meta
        ++ " (type " ++ show tpr ++ ")"

addrOfPlace :: HasCallStack => MirPlace s -> MirGenerator h s ret (MirExp s)
addrOfPlace (MirPlace tpr r NoMeta) = return $ MirExp MirReferenceRepr r
addrOfPlace (MirPlace tpr r (SliceMeta len)) =
    return $ MirExp MirSliceRepr $ mkSlice r len
addrOfPlace (MirPlace _tpr r (DynMeta vtable)) =
    return $ MirExp DynRefRepr $
      R.App $ E.MkStruct DynRefCtx $
      Ctx.Empty Ctx.:> r Ctx.:> vtable


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
    case bop of
        Unchecked bop' -> do
            (res, overflow) <- evalBinOp bop' mat me1 me2
            G.assertExpr (S.notExpr overflow) $
              S.litExpr $
              "Binary operation (" <> Text.pack (show (pretty bop')) <>
              ") would overflow"
            pure res
        WithOverflow bop' -> do
            (res, overflow) <- evalBinOp bop' mat me1 me2
            col <- use $ cs . collection
            buildTupleM [typeOf op1, TyBool] [res, MirExp C.BoolRepr overflow]
        _ -> fst <$> evalBinOp bop mat me1 me2

-- Evaluate a binop, returning both the result and an overflow flag.
evalBinOp :: forall h s ret. M.BinOp -> Maybe M.ArithType -> MirExp s -> MirExp s ->
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
          -- In all cases except shifts, the inputs should already have the
          -- same width, and `extendToMax` is a no-op (except it provides the
          -- proof that `na` and `ma` are equal).  For shifts, the second input
          -- (shift amount) can have any width, so we pad one side or the other
          -- to make the widths match up.
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
              (M.Mul, Just M.Unsigned) ->
                return (MirExp (C.BVRepr n) (S.app $ E.BVMul n e1 e2), umulOverflow n e1 e2)
              (M.Mul, Just M.Signed) ->
                return (MirExp (C.BVRepr n) (S.app $ E.BVMul n e1 e2), smulOverflow n e1 e2)
              (M.Div, Just M.Unsigned) ->
                return (MirExp (C.BVRepr n) (S.app $ E.BVUdiv n e1 e2), udivOverflow n e1 e2)
              (M.Div, Just M.Signed) ->
                return (MirExp (C.BVRepr n) (S.app $ E.BVSdiv n e1 e2), sdivOverflow n e1 e2)
              (M.Rem, Just M.Unsigned) ->
                return (MirExp (C.BVRepr n) (S.app $ E.BVUrem n e1 e2), udivOverflow n e1 e2)
              (M.Rem, Just M.Signed) ->
                return (MirExp (C.BVRepr n) (S.app $ E.BVSrem n e1 e2), sdivOverflow n e1 e2)
              -- Bitwise ops never overflow
              (M.BitXor, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVXor n e1 e2), noOverflow)
              (M.BitAnd, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVAnd n e1 e2), noOverflow)
              (M.BitOr, _) -> return (MirExp (C.BVRepr n) (S.app $ E.BVOr n e1 e2), noOverflow)
              -- Shift ops overflow when shift amount >= bit width
              -- If `extendToMax` padded the first argument, we need to
              -- truncate the result back down to its original width using
              -- `extendUnsignedBV`.
              --
              -- TODO: clean this up so it's more precise about how the
              -- operands get extended/truncated, instead of using the somewhat
              -- magical `extendToMax` / `extendUnsignedBV` functions.
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

      (MirExp MirReferenceRepr e1, MirExp MirReferenceRepr e2) ->
          case bop of
            M.Beq -> do
                eq <- mirRef_eq e1 e2
                return (MirExp C.BoolRepr eq, noOverflow)
            M.Ne -> do
                eq <- mirRef_eq e1 e2
                return (MirExp C.BoolRepr $ S.app $ E.Not eq, noOverflow)
            _ -> mirFail $ "No translation for pointer binop: " ++ fmt bop

      (MirExp MirReferenceRepr e1, MirExp UsizeRepr e2) -> do
          newRef <- mirRef_offsetWrap e1 e2
          return (MirExp MirReferenceRepr newRef, noOverflow)

      (_, _) -> mirFail $ "bad or unimplemented type: " ++ (fmt bop) ++ ", " ++ (show me1) ++ ", " ++ (show me2)

  where
    noOverflow :: R.Expr MIR s C.BoolType
    noOverflow = S.app $ E.BoolLit False

    -- Check whether unsigned multiplication of `e1 * e2` overflows `w` bits.
    -- If `zext e1 * zext e2 /= zext (e1 * e2)`, then overflow has occurred.
    mulOverflow :: forall w. (1 <= w, 1 <= w + w) =>
        NatRepr w ->
        (R.Expr MIR s (C.BVType w) -> R.Expr MIR s (C.BVType (w + w))) ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s C.BoolType
    mulOverflow w ext e1 e2 = S.app $ E.Not $ S.app $ E.BVEq w'
        (S.app $ E.BVMul w' (ext e1) (ext e2))
        (ext $ S.app $ E.BVMul w e1 e2)
      where w' = addNat w w

    umulOverflow :: forall w. (1 <= w) =>
        NatRepr w -> R.Expr MIR s (C.BVType w) -> R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s C.BoolType
    umulOverflow w e1 e2
      | LeqProof <- leqAdd2 (leqRefl w) (LeqProof @1 @w),
        LeqProof <- dblPosIsPos (LeqProof @1 @w) =
        mulOverflow w (S.app . E.BVZext (addNat w w) w) e1 e2
    smulOverflow :: forall w. (1 <= w) =>
        NatRepr w -> R.Expr MIR s (C.BVType w) -> R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s C.BoolType
    smulOverflow w e1 e2
      | LeqProof <- leqAdd2 (leqRefl w) (LeqProof @1 @w),
        LeqProof <- dblPosIsPos (LeqProof @1 @w) =
        mulOverflow w (S.app . E.BVSext (addNat w w) w) e1 e2

    -- Check that shift amount `e` is less than the input width `w`.
    shiftOverflowNat w e =
        let wLit = S.app $ E.NatLit $ natValue w
        in S.app $ E.Not $ S.app $ E.NatLt e wLit
    -- Check that shift amount `e` (whose width in `w'`) is less than the input
    -- width `w`.
    shiftOverflowBV :: (1 <= w') =>
        NatRepr w -> NatRepr w' -> R.Expr MIR s (C.BVType w') -> R.Expr MIR s C.BoolType
    shiftOverflowBV w w' e =
        let wLit = S.app $ eBVLit w' $ intValue w
        in S.app $ E.Not $ S.app $ E.BVUlt w' e wLit

    udivOverflow :: (1 <= w) =>
        NatRepr w ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s C.BoolType
    udivOverflow w _x y = S.app $ E.BVEq w y $ S.app $ eBVLit w 0

    sdivOverflow :: (1 <= w) =>
        NatRepr w ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s C.BoolType
    sdivOverflow w x y =
        S.app $ E.Or (udivOverflow w x y) $
            -- Are we dividing INT_MIN by -1?  E.g. `x == -128 && y == -1`
            S.app $ E.And
                (S.app $ E.BVEq w x $ S.app $ eBVLit w (1 `shiftL` (w' - 1)))
                (S.app $ E.BVEq w y $ S.app $ eBVLit w ((1 `shiftL` w') - 1))
      where w' = fromIntegral $ intValue w

-- Nullary ops in rust are used for resource allocation, so are not interpreted
transNullaryOp ::  M.NullOp -> M.Ty -> MirGenerator h s ret (MirExp s)
transNullaryOp nop ty =
  case nop of
    M.AlignOf -> getLayoutFieldAsMirExp "AlignOf" layAlign ty
    M.SizeOf -> getLayoutFieldAsMirExp "SizeOf" laySize ty
    M.UbChecks -> do
      -- Disable undefined behavior checks.
      -- TODO: re-enable this later, and fix the tests that break
      -- (see https://github.com/GaloisInc/mir-json/issues/107)
      return $ MirExp C.BoolRepr $ R.App $ E.BoolLit False

transUnaryOp :: M.UnOp -> M.Operand -> MirGenerator h s ret (MirExp s)
transUnaryOp uop op = do
    mop <- evalOperand op
    case (uop, mop) of
      (M.Not, MirExp C.BoolRepr e) -> return $ MirExp C.BoolRepr $ S.app $ E.Not e
      (M.Not, MirExp (C.BVRepr n) e) -> return $ MirExp (C.BVRepr n) $ S.app $ E.BVNot n e
      (M.Neg, MirExp (C.BVRepr n) e) -> return $ MirExp (C.BVRepr n) (S.app $ E.BVSub n (S.app $ eBVLit n 0) e)
      (M.Neg, MirExp C.IntegerRepr e) -> return $ MirExp C.IntegerRepr $ S.app $ E.IntNeg e
      (M.Neg, MirExp C.RealValRepr e) -> return $ MirExp C.RealValRepr $ S.app $ E.RealNeg e
      (M.PtrMetadata, MirExp MirSliceRepr e) -> return $ MirExp UsizeRepr $ getSliceLen e
      (_ , MirExp ty e) -> mirFail $ "Unimplemented unary op `" ++ fmt uop ++ "' for " ++ show ty


-- a -> u -> [a;u]
buildRepeat :: M.Operand -> M.ConstUsize -> MirGenerator h s ret (MirExp s)
buildRepeat op size = do
    (MirExp tp e) <- evalOperand op
    let n = fromInteger size
    exp <- mirVector_fromVector tp $ S.app $ E.VectorReplicate tp (S.app $ E.NatLit n) e
    return $ MirExp (MirVectorRepr tp) exp




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


evalCast' :: forall h s ret. HasCallStack => M.CastKind -> M.Ty -> MirExp s -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast' ck ty1 e ty2  = do
    col <- use $ cs . collection
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
           return $ MirExp (C.BVRepr w) (R.App $ E.BVIte e0 w (R.App $ eBVLit w 1) (R.App $ eBVLit w 0))
      (M.Misc, TyBool, TyInt bsz)
       | MirExp C.BoolRepr e0 <- e
       -> baseSizeToNatCont bsz $ \w ->
           return $ MirExp (C.BVRepr w) (R.App $ E.BVIte e0 w (R.App $ eBVLit w 1) (R.App $ eBVLit w 0))

      -- char to usize
      (M.Misc, M.TyChar, M.TyUint  M.USize)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp UsizeRepr (bvToUsize sz R.App e0)
      -- char to other uint
      (M.Misc, M.TyChar, M.TyUint s) -> baseSizeToNatCont s $ extendUnsignedBV e

      -- byte to char
      (M.Misc, M.TyUint B8, M.TyChar) -> baseSizeToNatCont M.B32 $ extendUnsignedBV e



{-      -- BV to Float
      (M.Misc, M.TyInt bsz, TyFloat fsz)
       | MirExp (C.BVRepr sz) e0 <- e
       -> return $ MirExp C.FloatRepr -}

      -- Not sure why this appears in generated MIR, but libcore has some no-op
      -- unsizes from `*const dyn Any` to `*const dyn Any`
      -- TODO: Remove this completely.
      (M.Unsize,a,b) | a == b -> return e

      -- ADT -> ADT unsizing is done via `CoerceUnsized`, and handled here.
      -- Reference-to-ADT -> reference-to-ADT casting is handled separately,
      -- below.
      (M.Unsize, M.TyAdt aname1 _ _, M.TyAdt aname2 _ _) ->
        coerceUnsized ck aname1 aname2 e
      (M.UnsizeVtable _, M.TyAdt aname1 _ _, M.TyAdt aname2 _ _) ->
        coerceUnsized ck aname1 aname2 e

      (M.Unsize, M.TyRef (M.TyArray tp sz) _, M.TyRef (M.TySlice tp') _) ->
        unsizeArray tp sz tp'
      (M.Unsize, M.TyRawPtr (M.TyArray tp sz) _, M.TyRawPtr (M.TySlice tp') _) ->
        unsizeArray tp sz tp'

      -- Trait object creation from a ref
      (M.UnsizeVtable vtbl, M.TyRef baseType _,
        M.TyRef (M.TyDynamic traitName) _) ->
          mkTraitObject traitName vtbl e
      (M.UnsizeVtable vtbl, M.TyRawPtr baseType _,
        M.TyRawPtr (M.TyDynamic traitName) _) ->
          mkTraitObject traitName vtbl e

      -- Casting between TyDynamics that vary only in their auto traits
      -- TODO: this should also normalize the TraitProjection predicates, to
      -- allow casting between equivalent descriptions of the same trait object
      (M.Unsize, M.TyRef (M.TyDynamic t1) _, M.TyRef (M.TyDynamic t2) _)
        | t1 == t2
        -> return e

      (M.Unsize, M.TyRef _ _, M.TyRef (M.TyDynamic _) _) ->
        mirFail $ unlines $
          [ "error when casting:"
          , "  ty: "<>show ty1
          , "  as: "<>show ty2
          , "expected `UnsizeVtable` cast kind, but saw `Unsize` cast kind" ]
      (M.Unsize, M.TyRawPtr _ _, M.TyRawPtr (M.TyDynamic _) _) ->
        mirFail $ unlines $
          [ "error when casting:"
          , "  ty: "<>show ty1
          , "  as: "<>show ty2
          , "expected `UnsizeVtable` cast kind, but saw `Unsize` cast kind" ]

      -- Unsized casts from references to sized structs to references to DSTs.
      -- We defer to the provided cast kind to determine what kind of unsizing
      -- cast we expect to perform, i.e. what kind of metadata to include in the
      -- created fat pointer.
      (M.Unsize, M.TyRef (M.TyAdt an1 _ _) m1, M.TyRef (M.TyAdt an2 _ _) m2) ->
        unsizeAdtSlice M.TyRef an1 m1 an2 m2
      (M.Unsize, M.TyRawPtr (M.TyAdt an1 _ _) m1, M.TyRawPtr (M.TyAdt an2 _ _) m2) ->
        unsizeAdtSlice M.TyRawPtr an1 m1 an2 m2
      (M.UnsizeVtable vtable, M.TyRef (M.TyAdt an1 _ _) m1, M.TyRef (M.TyAdt an2 _ _) m2) ->
        unsizeAdtDyn vtable M.TyRef an1 m1 an2 m2
      (M.UnsizeVtable vtable, M.TyRawPtr (M.TyAdt an1 _ _) m1, M.TyRawPtr (M.TyAdt an2 _ _) m2) ->
        unsizeAdtDyn vtable M.TyRawPtr an1 m1 an2 m2

      -- C-style adts, casting an enum value to a TyInt
      (M.Misc, M.TyAdt aname _ _, M.TyInt sz) -> do
        adt <- findAdt aname
        discr <- enumDiscriminant adt e
        evalCast' M.Misc (M.TyInt M.USize) discr (M.TyInt sz)
      (M.Misc, M.TyAdt aname _ _, M.TyUint sz) -> do
        adt <- findAdt aname
        discr <- enumDiscriminant adt e
        evalCast' M.Misc (M.TyInt M.USize) discr (M.TyUint sz)

      -- References have the same representation as Raw pointers
      (M.Misc, M.TyRef ty1 mut1, M.TyRawPtr ty2 mut2)
         | ty1 == ty2 && mut1 == mut2 -> return e

      (M.MutToConstPointer, M.TyRawPtr ty1 M.Mut, M.TyRawPtr ty2 M.Immut)
         | ty1 == ty2 -> return e

      -- Integer-to-pointer casts.  Pointer-to-integer casts are not yet
      -- supported.
      (M.Misc, M.TyInt _, M.TyRawPtr ty _) -> transmuteExp e ty1 ty2
      (M.Misc, M.TyUint _, M.TyRawPtr ty _) -> transmuteExp e ty1 ty2

      --  *const [T] -> *T (discards the length and returns only the pointer)
      (M.Misc, M.TyRawPtr (M.TySlice t1) m1, M.TyRawPtr t2 m2)
        | t1 == t2, m1 == m2, MirExp MirSliceRepr e' <- e
        -> return $ MirExp MirReferenceRepr (getSlicePtr e')
      (M.Misc, M.TyRawPtr M.TyStr m1, M.TyRawPtr (M.TyUint M.B8) m2)
        | m1 == m2, MirExp MirSliceRepr e' <- e
        -> return $ MirExp MirReferenceRepr (getSlicePtr e')

      --  *const [T; N] -> *const T (get first element)
      (M.Misc, M.TyRawPtr (M.TyArray t1 _) m1, M.TyRawPtr t2 m2)
        | t1 == t2, m1 == m2, MirExp MirReferenceRepr e' <- e
        -> do
          Some tpr <- tyToReprM t1
          MirExp MirReferenceRepr <$> subindexRef tpr e' (R.App $ usizeLit 0)

      --  *const [u8] <-> *const str (no-ops)
      (M.Misc, M.TyRawPtr (M.TySlice (M.TyUint M.B8)) m1, M.TyRawPtr M.TyStr m2)
        | m1 == m2 -> return e
      (M.Misc, M.TyRawPtr M.TyStr m1, M.TyRawPtr (M.TySlice (M.TyUint M.B8)) m2)
        | m1 == m2 -> return e

      -- Arbitrary pointer-to-pointer casts are allowed as long as the source
      -- and destination types have the same Crucible representation.  This is
      -- similar to calling `transmute`.
      (M.Misc, M.TyRawPtr _ _, M.TyRawPtr _ _)
         | ty1 == ty2 -> return e
         | tyToRepr col ty1 == tyToRepr col ty2 -> return e

      (M.ReifyFnPointer, M.TyFnDef defId, M.TyFnPtr sig@(M.FnSig args ret _))
         -> do mhand <- lookupFunction defId
               case mhand of
                 Just (me, sig')
                   | sig == sig' -> return me
                   | otherwise -> mirFail $
                       "ReifyFnPointer: bad MIR: method handle has wrong sig: " ++
                       show (defId, sig, sig')
                 Nothing -> mirFail $
                        "ReifyFnPointer: bad MIR: can't find method handle: " ++
                        show defId

      (M.ClosureFnPointer shimDefId, M.TyClosure [], M.TyFnPtr sig@(M.FnSig args ret _))
         -> do mhand <- lookupFunction shimDefId
               case mhand of
                 Just (me, sig')
                   | sig == sig' -> return me
                   | otherwise -> mirFail $
                       "ClosureFnPointer: bad MIR: method handle has wrong sig: " ++
                       show (shimDefId, sig, sig')
                 Nothing -> mirFail $
                        "ClosureFnPointer: bad MIR: can't find method handle: " ++
                        show shimDefId

      (M.Transmute, _, _) -> transmuteExp e ty1 ty2

      -- This casts from a safe pointer to an unsafe one.
      -- Since we don't track safeness this is just a no-op for now, but if
      -- we decide to track that, this needs to be updated.
      (M.UnsafeFnPointer, _, _) | ty1 == ty2 -> pure e

      _ -> mirFail $ "unimplemented cast: " ++ (show ck) ++
        "\n  ty: " ++ (show ty1) ++ "\n  as: " ++ (show ty2)
  where
    -- | Attempt to access the repr(transparent) field types of the two structs,
    -- failing if only one is repr(transparent)
    reprTransparentFieldTys :: AdtName -> AdtName -> MirGenerator h s ret (Maybe (Ty, Ty))
    reprTransparentFieldTys an1 an2 = do
      col <- use $ cs . collection
      adt1 <- findAdt an1
      adt2 <- findAdt an2
      case (reprTransparentFieldTy col adt1, reprTransparentFieldTy col adt2) of
        (Just field1Ty, Just field2Ty) ->
          pure $ Just (field1Ty, field2Ty)
        (Nothing, Nothing) ->
          pure Nothing
        (Just _, Nothing) ->
          mirFail $ unwords
            [ "reprTransparentFieldTys: impossible:"
            , show $ adt1 ^. M.adtname, "was repr(transparent), but"
            , show $ adt2 ^. M.adtname, "was not" ]
        (Nothing, Just _) ->
          mirFail $ unwords
            [ "reprTransparentFieldTys: impossible:"
            , show $ adt2 ^. M.adtname, "was repr(transparent), but"
            , show $ adt1 ^. M.adtname, "was not" ]

    -- | Perform an unsized cast from a reference to a struct containing an
    -- array in its (transitively) last field to one containing a slice or @str@
    -- in the same position.
    unsizeAdtSlice ::
      (Ty -> Mutability -> Ty) ->
      AdtName -> Mutability ->
      AdtName -> Mutability ->
      MirGenerator h s ret (MirExp s)
    unsizeAdtSlice ref an1 m1 an2 m2 =
      reprTransparentFieldTys an1 an2 >>= \case
        Just (field1Ty, field2Ty) ->
          evalCast' ck (ref field1Ty m1) e (ref field2Ty m2)
        Nothing ->
          unsizeAdtSliceNormal an1 an2

    -- | `unsizeAdtSlice`, for non-@repr(transparent)@ structs.
    unsizeAdtSliceNormal :: AdtName  -> AdtName -> MirGenerator h s ret (MirExp s)
    unsizeAdtSliceNormal an1 an2 = do
      adtRef <- case e of
        MirExp MirReferenceRepr adtRef -> pure adtRef
        _ -> mirFail "unsizeAdtSlice called on non-reference"
      col <- use $ cs . collection

      -- We expect to be casting from an array-containing DST to a
      -- slice-containing DST. For the target of the cast to be a valid DST, the
      -- slice needs to be its last field (or its last field's last field),
      -- which means the source needs to have an array in the same position
      lenExpr <- case findLastFieldRec col an1 of
        Just field ->
          case field ^. M.fty of
            M.TyArray _elemTy len ->
              pure $ R.App $ usizeLit $ fromIntegral len
            _ ->
              mirFail "attempted Unsize cast from non-array source"
        Nothing ->
          mirFail $ "unsizedAdtSlice: unable to determine last field of "<>show an1

      -- Sanity-check that we are indeed casting to a type with a slice in the
      -- expected position
      let ref = MirExp MirSliceRepr (mkSlice adtRef lenExpr)
      case findLastFieldRec col an2 of
        Nothing ->
          mirFail $ "unsizedAdtSlice: unable to determine last field of "<>show an2
        Just field ->
          case field ^. M.fty of
            M.TySlice _elemTy -> pure ref
            _ -> mirFail "attempted Unsize cast to non-slice target"

    -- | Perform an unsized cast from a reference to a struct containing any
    -- initializable type in its (transitively) last field to one containing a
    -- trait object in the same position. The restriction on initializability
    -- makes it substantially easier to implement `Mir.TransTy.structFieldRef` -
    -- see that function for details.
    unsizeAdtDyn ::
      VtableName ->
      (Ty -> Mutability -> Ty) ->
      AdtName -> Mutability ->
      AdtName -> Mutability ->
      MirGenerator h s ret (MirExp s)
    unsizeAdtDyn vtable ref an1 m1 an2 m2 =
      reprTransparentFieldTys an1 an2 >>= \case
        Just (field1Ty, field2Ty) ->
          evalCast' ck (ref field1Ty m1) e (ref field2Ty m2)
        Nothing ->
          unsizeAdtDynNormal vtable an1 an2

    -- | `unsizeAdtDyn`, for non-@repr(transparent)@ structs.
    unsizeAdtDynNormal :: VtableName -> AdtName  -> AdtName -> MirGenerator h s ret (MirExp s)
    unsizeAdtDynNormal vtable castSource castTarget = do
      col <- use $ cs . collection
      eventualTraitObject <- case findLastFieldRec col castSource of
        Nothing ->
          mirFail $ "unsizedAdtDyn: unable to determine last field of "<>show castSource
        Just field ->
          pure (field ^. M.fty)
      -- `FkMaybe` fields are not initializable, and our rationale for
      -- prohibiting them here is described in `unsizeAdtDyn`, above, and
      -- `Mir.TransTy.structFieldRef`
      case tyToFieldRepr col eventualTraitObject of
        Left err -> mirFail ("unsizeAdtDynNormal: " ++ err)
        Right (Some (FieldRepr (FkMaybe _))) ->
          mirFail "error: unsizeAdtDyn with non-initializable unsized field"
        Right (Some (FieldRepr (FkInit _))) ->
          case findLastFieldRec col castTarget of
            Nothing ->
              mirFail $ "unsizedAdtDyn: unable to determine last field of "<>show castTarget
            Just field ->
              case field ^. M.fty of
                M.TyDynamic traitName -> mkTraitObject traitName vtable e
                _ -> mirFail "attempted UnsizeVtable cast with non-trait-object target"

    unsizeArray ty sz ty'
      | ty == ty', MirExp MirReferenceRepr ref <- e
      = do
        Some elem_tp <- tyToReprM ty
        let len   = R.App $ usizeLit (fromIntegral sz)
        ref' <- subindexRef elem_tp ref (R.App $ usizeLit 0)
        let tup   = S.mkStruct mirSliceCtxRepr
                        (Ctx.Empty Ctx.:> ref' Ctx.:> len)
        return $ MirExp MirSliceRepr tup
      | otherwise = mirFail $
        "Type mismatch in cast: " ++ show ck ++ " " ++ show ty1 ++ " as " ++ show ty2

    -- Implementation of the "coerce unsized" operation.  If `Foo<T>:
    -- CoerceUnsized<Foo<U>>`, then this operation is enabled for converting
    -- `Foo<T>` to `Foo<U>`.  The actual operation consists of disassembling
    -- the struct, coercing any raw pointers inside, and putting it back
    -- together again.
    coerceUnsized :: HasCallStack =>
        M.CastKind -> M.AdtName -> M.AdtName -> MirExp s -> MirGenerator h s ret (MirExp s)
    coerceUnsized ck an1 an2 e = do
        col <- use $ cs . collection
        adt1 <- findAdt an1
        adt2 <- findAdt an2
        case (reprTransparentFieldTy col adt1, reprTransparentFieldTy col adt2) of
            (Just ty1, Just ty2) ->
              -- The struct is #[repr(transparent)], so it has only one non-ZST
              -- field. This field must be the pointer/ref field being coerced,
              -- as rustc currently forbids implementing CoerceUnsized if it
              -- can't a field to coerce. Since this field is being coerced, its
              -- old and new types should never be equal. Because CoerceUnsized
              -- is unstable, a future version of rustc might change this
              -- behavior, so we leave this check here in place as a safeguard.
              if ty1 == ty2
                then pure e
                else evalCast' ck ty1 e ty2
            (Nothing, Nothing) -> coerceUnsizedNormal ck adt1 adt2 e
            _ -> mirFail $ "impossible: coerceUnsized: one of " ++ show (an1, an2) ++
                " is repr(transparent) and the other is not?"

    coerceUnsizedNormal :: HasCallStack =>
        M.CastKind -> M.Adt -> M.Adt -> MirExp s -> MirGenerator h s ret (MirExp s)
    coerceUnsizedNormal ck adt1 adt2 e = do
        when (adt1 ^. adtkind /= Struct || adt2 ^. adtkind /= Struct) $ mirFail $
            "coerceUnsized not yet implemented for non-struct types: " ++ show (an1, an2)
        let v1 = Maybe.fromJust $ adt1 ^? adtvariants . ix 0
        let v2 = Maybe.fromJust $ adt2 ^? adtvariants . ix 0
        let numFields = v1 ^. vfields . to length
        let numFields' = v2 ^. vfields . to length
        when (numFields' /= numFields) $ mirFail $
            "coerceUnsized on incompatible types (mismatched fields): " ++ show (an1, an2)
        vals' <- forM (zip3 [0..] (v1 ^. vfields) (v2 ^. vfields)) $ \(i, f1, f2) -> do
            val <- getStructField adt1 i e
            -- Only compute a cast if the types are syntactically unequal.
            if (f1 ^. fty) == (f2 ^. fty)
              then pure val
              else evalCast' ck (f1 ^. fty) val (f2 ^. fty)
        buildStruct adt2 vals'
      where
        an1 = adt1 ^. adtname
        an2 = adt2 ^. adtname


evalCast :: HasCallStack => M.CastKind -> M.Operand -> M.Ty -> MirGenerator h s ret (MirExp s)
evalCast ck op ty = do
    e <- evalOperand op
    evalCast' ck (M.typeOf op) e ty

transmuteExp :: HasCallStack => MirExp s -> M.Ty -> M.Ty -> MirGenerator h s ret (MirExp s)
transmuteExp e@(MirExp argTy argExpr) srcMirTy destMirTy = do
  Some retTy <- tyToReprM destMirTy
  case (argTy, retTy) of
    -- Splitting an integer into pieces (usually bytes)
    (C.BVRepr w1, MirVectorRepr (C.BVRepr w2))
      | natValue w1 `mod` natValue w2 == 0 -> do
        let n = natValue w1 `div` natValue w2
        pieces <- forM [0 .. n - 1] $ \i -> do
          Some i' <- return $ mkNatRepr i
          let offset = natMultiply i' w2
          LeqProof <- case testLeq (addNat offset w2) w1 of
            Just x -> return x
            Nothing -> panic "transmute" ["impossible: (w1 / w2 - 1) * w2 + w2 > w1?"]
          return $ R.App $ E.BVSelect (natMultiply i' w2) w2 w1 argExpr
        let v = R.App $ E.VectorLit (C.BVRepr w2) (V.fromList pieces)
        mv <- mirVector_fromVector (C.BVRepr w2) v
        return $ MirExp retTy mv

    -- Reconstructing an integer from pieces (usually bytes)
    (MirVectorRepr (C.BVRepr w1), C.BVRepr w2)
      | natValue w2 `mod` natValue w1 == 0 -> do
        let n = natValue w2 `div` natValue w1
        vecRef <- constMirRef (MirVectorRepr (C.BVRepr w1)) argExpr
        pieces <- forM [0 .. n - 1] $ \i -> do
          let idx = R.App $ usizeLit (fromIntegral i)
          elemRef <- subindexRef (C.BVRepr w1) vecRef idx
          readMirRef (C.BVRepr w1) elemRef
        let go :: (1 <= wp) =>
              NatRepr wp ->
              [R.Expr MIR s (C.BVType wp)] ->
              (forall wr. (1 <= wr) => NatRepr wr -> R.Expr MIR s (C.BVType wr) -> a) ->
              a
            go _ [] _ = panic "transmute" ["impossible: w2/w1 == 0?"]
            go wp [x] k = k wp x
            go wp (x:xs) k = go wp xs (\wr rest ->
              case leqAdd (leqProof (knownNat @1) wr) wp of
                LeqProof -> k (addNat wr wp) (R.App $ E.BVConcat wr wp rest x))
        concatExpr <- go w1 pieces $ \wr result -> do
          Refl <- case testEquality wr w2 of
            Just x -> return x
            Nothing -> panic "transmute" ["impossible: w1 * (w2/w1) != w2?"]
          return result
        return $ MirExp retTy concatExpr

    -- Cast integer to pointer, like `0 as *mut T`
    (C.BVRepr w, MirReferenceRepr) -> do
        int <- case srcMirTy of
            M.TyInt _ -> return $ sbvToUsize w R.App argExpr
            M.TyUint _ -> return $ bvToUsize w R.App argExpr
            _ -> mirFail $ "unexpected srcMirTy " ++ show srcMirTy ++ " for tpr " ++ show argTy
        MirExp MirReferenceRepr <$> integerToMirRef int

    -- Transmuting between values of the same Crucible repr
    _ | Just Refl <- testEquality argTy retTy -> return e

    _ -> mirFail $
      "can't transmute " ++ show argTy ++ " to " ++ show retTy

-- | Create a new trait object by combining `e` with the named vtable.  This is
-- only valid when `e` is TyRef or TyRawPtr.  Coercions via the `CoerceUnsized`
-- trait require unpacking and repacking structs, which we don't handle here.
mkTraitObject :: forall h s ret.
    HasCallStack =>
    M.TraitName ->
    M.VtableName ->
    MirExp s ->
    MirGenerator h s ret (MirExp s)
mkTraitObject traitName vtableName e = do
    handles <- Maybe.fromMaybe (error $ "missing vtable handles for " ++ show vtableName) <$>
        use (cs . vtableMap . at vtableName)

    let mkEntry :: MirHandle -> MirExp s
        mkEntry (MirHandle hname _ fh) =
            MirExp (C.FunctionHandleRepr (FH.handleArgTypes fh) (FH.handleReturnType fh))
                (R.App $ E.HandleLit fh)
    vtable@(MirExp vtableTy _) <- return $ mkStructExp $ map mkEntry handles

    -- Check that the vtable we constructed has the appropriate type for the
    -- trait.  A mismatch would cause runtime errors at calls to trait methods.
    trait <- Maybe.fromMaybe (error $ "unknown trait " ++ show traitName) <$>
        use (cs . collection . M.traits . at traitName)
    col <- use $ cs . collection
    Some vtableTy' <- case traitVtableType col traitName trait of
                        Left err -> error ("mkTraitObject: " ++ err)
                        Right x -> return x
    case testEquality vtableTy vtableTy' of
        Just _ -> return ()
        Nothing -> error $ unwords
            ["vtable signature mismatch for vtable", show vtableName,
                "of trait", show traitName, ":", show vtableTy, "!=", show vtableTy']

    return $ mkStructExp
        [ e
        , packAny vtable
        ]

    where
        -- | `E.MkStruct`, but lifted to work on `MirExp`s.  We use this for
        -- building vtables and trait objects.  These don't correspond to any
        -- `M.TyAdt` or `M.TyTuple`, so we can't use the higher-level
        -- `buildStruct` or `buildTupleM` functions for this.
        mkStructExp :: [MirExp s] -> MirExp s
        mkStructExp exps = mkStructExp' Ctx.Empty Ctx.Empty exps

        mkStructExp' :: forall ctx.
            C.CtxRepr ctx ->
            Ctx.Assignment (R.Expr MIR s) ctx ->
            [MirExp s] ->
            MirExp s
        mkStructExp' ctx asn [] = MirExp (C.StructRepr ctx) (S.app $ E.MkStruct ctx asn)
        mkStructExp' ctx asn (MirExp tpr e : exps) =
            mkStructExp' (ctx Ctx.:> tpr) (asn Ctx.:> e) exps

-- Expressions: evaluation of Rvalues and Lvalues

evalRval :: HasCallStack => M.Rvalue -> MirGenerator h s ret (MirExp s)
evalRval (M.Use op) = evalOperand op
evalRval (M.Repeat op size) = buildRepeat op size
evalRval (M.Ref _bk lv _) = evalPlace lv >>= addrOfPlace
evalRval (M.AddressOf _mutbl lv) = evalPlace lv >>= addrOfPlace
evalRval (M.Len lv) =
    case M.typeOf lv of
        M.TyArray _ len ->
            return $ MirExp UsizeRepr $ R.App $ usizeLit $ fromIntegral len
        ty@(M.TySlice _) -> do
            place <- evalPlace lv
            meta <- case place of
                MirPlace _tpr _ref meta -> pure meta
            case meta of
                SliceMeta len -> return $ MirExp UsizeRepr len
                _ -> mirFail $ "bad metadata " ++ show meta ++ " for reference to " ++ show ty
        ty -> mirFail $ "don't know how to take Len of " ++ show ty
evalRval (M.Cast ck op ty) = evalCast ck op ty
evalRval (M.BinaryOp binop op1 op2) = transBinOp binop op1 op2
evalRval (M.NullaryOp nop nty) = transNullaryOp  nop nty
evalRval (M.UnaryOp uop op) = transUnaryOp  uop op
evalRval (M.Discriminant lv discrTy) = do
    e <- evalLvalue lv
    let enumTy = typeOf lv
    case enumTy of
      TyAdt aname _ _ -> do
        adt <- findAdt aname
        enumDiscriminant adt e
      _ -> mirFail $ "tried to access discriminant of non-enum type " ++ show enumTy

evalRval (M.Aggregate ak ops) =
    case ak of
        M.AKTuple ->  do
            col <- use $ cs . collection
            let tys = map typeOf ops
            exps <- mapM evalOperand ops
            buildTupleMaybeM tys (map Just exps)
        M.AKArray ty -> do
            exps <- mapM evalOperand ops
            Some repr <- tyToReprM ty
            buildArrayLit repr exps
        M.AKClosure -> do
            -- Closure environments have the same
            -- representation as tuples.
            col <- use $ cs . collection
            let tys = map typeOf ops
            exps <- mapM evalOperand ops
            buildTupleMaybeM tys (map Just exps)
        M.AKRawPtr ty _mutbl -> do
            args <- mapM evalOperand ops
            (MirExp tprPtr ptr, MirExp tprMeta meta) <- case args of
                [p, m] -> return (p, m)
                _ -> mirFail $ "evalRval: expected exactly two operands for " ++ show ak
                    ++ ", but got " ++ show args
            case ty of
                TySlice _ -> case (tprPtr, tprMeta) of
                    (MirReferenceRepr, UsizeRepr) -> do
                        let tup = S.mkStruct
                                (Ctx.Empty Ctx.:> MirReferenceRepr Ctx.:> knownRepr)
                                (Ctx.Empty Ctx.:> ptr Ctx.:> meta)
                        return $ MirExp MirSliceRepr tup
                    _ -> mirFail $ "evalRval: unexpected reprs " ++ show (tprPtr, tprMeta)
                        ++ " for aggregate " ++ show ak
                _ -> mirFail $ "evalRval: unsupported output type for " ++ show ak
evalRval rv@(M.RAdtAg (M.AdtAg adt agv ops ty optField)) = do
    case ty of
      -- It's not legal to construct a MethodSpec using a Rust struct
      -- constructor, so we translate as "assert(false)" instead.  Only
      -- functions in the `method_spec::raw` should be creating MethodSpecs
      -- directly, and those functions will be overridden, so the code we
      -- generate here never runs.
      CTyMethodSpec ->
        mirFail $ "evalRval: can't construct MethodSpec without an override"
      CTyMethodSpecBuilder ->
        mirFail $ "evalRval: can't construct MethodSpecBuilder without an override"
      TyAdt _ _ _ -> do
        col <- use $ cs . collection
        es <- mapM evalOperand ops
        case findReprTransparentField col adt of
          Just rtIdx ->
            case optField of
              Nothing -> do
                -- `repr(transparent)` struct/enum case.
                op <- case ops ^? ix rtIdx of
                    Just op -> pure op
                    Nothing -> mirFail $ "repr(transparent) field index " ++ show rtIdx ++
                        " out of range for " ++ show (adt ^. adtname)
                evalOperand op
              Just unionFieldIdx
                | unionFieldIdx == rtIdx -> do
                    -- `repr(transparent)` union, initializing the primary
                    -- field.  The result is the value of the field.
                    op <- case ops ^? ix 0 of
                        Just op -> pure op
                        Nothing -> mirFail $ "missing operand for union AdtAg of type "
                            ++ show (adt ^. adtname)
                    evalOperand op
                | otherwise -> do
                    -- `repr(transparent)` union, initializing one of the
                    -- zero-sized fields.  The result is an uninitialized
                    -- union value.
                    initialValue ty >>= \mv -> case mv of
                        Just v -> return v
                        Nothing -> mirFail $ "uninitialized union AdtAg unsupported for " ++ show ty
          Nothing -> do
            case adt^.adtkind of
                M.Struct -> buildStruct adt es
                M.Enum _ -> buildEnum adt (fromInteger agv) es
                M.Union -> do
                    mirFail $ "evalRval: Union types are unsupported, for " ++ show (adt ^. adtname)
      _ -> mirFail $ "evalRval: unsupported type for AdtAg: " ++ show ty
evalRval (M.ThreadLocalRef did _) = staticPlace did >>= addrOfPlace

-- We treat CopyForDeref(lv) the same as Rvalue::Use(Operand::Copy(lv)).
evalRval rv@(M.CopyForDeref lv) = evalLvalue lv

evalRval rv@(M.ShallowInitBox op ty) = mirFail
    "evalRval: ShallowInitBox not supported"

evalLvalue :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirExp s)
evalLvalue lv = evalPlace lv >>= readPlace


evalPlace :: HasCallStack => M.Lvalue -> MirGenerator h s ret (MirPlace s)
evalPlace (M.LBase var) = varPlace var
evalPlace (M.LProj lv proj) = do
    pl <- evalPlace lv
    evalPlaceProj (M.typeOf lv) pl proj

evalPlaceProj ::
  forall h s ret.
  HasCallStack =>
  M.Ty ->
  MirPlace s ->
  M.PlaceElem ->
  MirGenerator h s ret (MirPlace s)
evalPlaceProj ty pl@(MirPlace tpr ref NoMeta) M.Deref = do
    -- In the general case (when T is a sized type), we have a MirPlace input of
    -- the form:
    --
    --   MirPlace (*T) <expr: **T> NoMeta
    --
    -- And we want to produce output of the form:
    --
    --   MirPlace T <expr': *T> NoMeta
    --
    -- Where *T is hand-wavy syntax for reference types (e.g., &T and *const T).
    -- Note the double indirection in <expr: **T>.
    --
    -- Things get a little bit trickier when dealing with unsized types,
    -- however. See the comments below.
    case ty of
        M.TyRef t _ -> doRef t
        M.TyRawPtr t _ -> doRef t
        CTyBox t -> doRef t
        _ -> mirFail $ "deref not supported on " ++ show ty
  where
    doRef :: M.Ty -> MirGenerator h s ret (MirPlace s)
    doRef (M.TySlice ty') | MirSliceRepr <- tpr = doSlice ty' ref
    doRef M.TyStr | MirSliceRepr <- tpr = doSlice (M.TyUint M.B8) ref
    doRef (M.TyDynamic _) | DynRefRepr <- tpr = doDyn ref
    doRef adtTy@(M.TyAdt _ _ _) | MirSliceRepr <- tpr = doSliceAdt adtTy ref
    doRef adtTy@(M.TyAdt _ _ _) | DynRefRepr <- tpr = doDynAdt adtTy ref
    doRef ty' | MirReferenceRepr <- tpr = do
        -- This use of `tyToReprM` is okay because `TyDynamic` and other
        -- unsized cases are handled above.
        Some tpr' <- tyToReprM ty'
        MirPlace tpr' <$> readMirRef tpr ref <*> pure NoMeta
    doRef _ = mirFail $ "deref: bad repr for " ++ show ty ++ ": " ++ show tpr

    -- Slice types [U] are unsized, so we handle them differently. Given a
    -- MirPlace input of the form:
    --
    --   MirPlace (*[U]) <expr: **[U]> NoMeta
    --
    -- We produce output of the form:
    --
    --   MirPlace U <data: *U> (SliceMeta len)
    --
    -- Where `data` is the slice's data pointer and `len` is the slice's length.
    doSlice :: M.Ty -> R.Expr MIR s MirReferenceType -> MirGenerator h s ret (MirPlace s)
    doSlice ty' ref' = do
        -- This use of `tyToReprM` is okay because we know the element type of
        -- a slice is always sized.
        Some tpr' <- tyToReprM ty'
        slice <- readMirRef MirSliceRepr ref'
        let ptr = getSlicePtr slice
        let len = getSliceLen slice
        return $ MirPlace tpr' ptr (SliceMeta len)

    -- Types like `dyn Trait` are unsized, so we handle them differently. Given
    -- a MirPlace input of the form:
    --
    --   MirPlace (*dyn Trait) <expr: **dyn Trait> NoMeta
    --
    -- We produce output of the form:
    --
    --   MirPlace AnyType <data: *?> (DynMeta vtable)
    --
    -- Where `data` is the trait object's data pointer (a reference to some
    -- unknown type) and `vtable` is the trait object's vtable. Note that it is
    -- unimportant what type we use as the first argument to MirPlace, as there
    -- is no way to directly access `data` (e.g., you can't access (*x).field if
    -- `x: &dyn Trait`). As such, it is acceptable to fill it in with a dummy
    -- type like AnyType.
    doDyn :: R.Expr MIR s MirReferenceType -> MirGenerator h s ret (MirPlace s)
    doDyn ref' = do
        dynRef <- readMirRef DynRefRepr ref'
        let dynRefData = S.getStruct dynRefDataIndex dynRef
        let dynRefVtable = S.getStruct dynRefVtableIndex dynRef
        return $ MirPlace C.AnyRepr dynRefData (DynMeta dynRefVtable)

    -- For (dynamically-sized) ADTs wrapping slices, with MirPlace input of the
    -- form:
    --
    --   MirPlace (*S<[T]>) <expr: **S<[T]> NoMeta
    --
    -- We produce output of the form:
    --
    --   MirPlace AnyRepr <expr: *S<[T; len]> (SliceMeta len)
    --
    -- Where `len` is the wrapped slice's length.
    doSliceAdt :: M.Ty -> R.Expr MIR s MirReferenceType -> MirGenerator h s ret (MirPlace s)
    doSliceAdt adtTy ref' =
      do
        -- Normally we'd use `tyToReprM adtTy` to get the ADT's representation,
        -- but that would involve computing its slice field's representation,
        -- which should error. Because it represents an unsized value, we don't
        -- expect to check/use this type directly elsewhere, so we can get away
        -- with an `AnyRepr` placeholder.
        let adtRepr = C.AnyRepr
        adtRef <- readMirRef MirSliceRepr ref'
        -- In both this case and the case of plain slices, `readMirRef` gives us
        -- access to a double-wide DST pointer. In both cases, the second half
        -- holds the slice length. In our case, the first half holds a pointer
        -- to the ADT, while in the slice case, the first half holds the slice's
        -- data pointer, i.e. a pointer to the first element of the slice.
        --
        -- In both cases, though, we can safely access the first half with
        -- `getSlicePtr`.
        let adtPtr = getSlicePtr adtRef
        let sliceLen = getSliceLen adtRef
        return $ MirPlace adtRepr adtPtr (SliceMeta sliceLen)

    -- For (dynamically-sized) ADTs wrapping trait objects, with MirPlace input
    -- of the form:
    --
    --   MirPlace (*S<dyn Trait>) <expr: **S<dyn Trait> NoMeta
    --
    -- We produce output of the form:
    --
    --   MirPlace AnyRepr <expr: *S<Concrete> (DynMeta vtable)
    --
    -- Where `vtable` is the vtable for `Trait` at `Concrete`.
    doDynAdt :: M.Ty -> R.Expr MIR s MirReferenceType -> MirGenerator h s ret (MirPlace s)
    doDynAdt adtTy ref' =
      do
        -- Normally we'd use `tyToReprM adtTy` to get the ADT's representation,
        -- but that would involve computing its trait object field's
        -- representation, which will error. Because it represents an unsized
        -- value, we don't expect to check/use this type directly elsewhere, so
        -- we can get away with an `AnyRepr` placeholder.
        let adtRepr = C.AnyRepr
        dynRef <- readMirRef DynRefRepr ref'
        let adtPtr = S.getStruct dynRefDataIndex dynRef
        let vtable = S.getStruct dynRefVtableIndex dynRef
        return $ MirPlace adtRepr adtPtr (DynMeta vtable)

evalPlaceProj ty pl@(MirPlace tpr ref meta) (M.PField idx _mirTy) = do
  col <- use $ cs . collection
  case ty of
    CTyMaybeUninit _ -> do
        return $ MirPlace tpr ref NoMeta

    ty | Just adt <- tyAdtDefSkipDowncast col ty, Just tIdx <- findReprTransparentField col adt ->
        if idx == tIdx then
            -- The field's low-level representation is identical to the struct
            -- itself, due to repr(transparent).
            return pl
        else do
            -- Since `findReprTransparentField` returned `Just`, we know that
            -- fields aside from `tIdx` must be zero-sized, and thus contain no
            -- actual data.  So we can return a dummy reference here.
            --
            -- Also, for enum types, `#[repr(transparent)]` is only allowed on
            -- single-variant enums, so we know `tIdx` refers to a field of
            -- variant 0 (as with structs).
            fieldTy <- case adt ^? M.adtvariants . ix 0 . M.vfields . ix idx . M.fty of
                Just x -> return x
                Nothing -> mirFail $ "impossible: accessed out of range field " ++
                    show idx ++ " of " ++ show adt ++ "?"
            MirExp tpr' e <- initialValue fieldTy >>= \x -> case x of
                Just x -> return x
                Nothing -> mirFail $ "failed to produce dummy value of type " ++ show fieldTy
            ref <- constMirRef tpr' e
            return $ MirPlace tpr' ref NoMeta

    M.TyAdt nm _ _ -> do
        adt <- findAdt nm
        case adt^.adtkind of
            Struct -> structFieldRef adt idx ref meta
            Enum _ -> mirFail $ "tried to access field of non-downcast " ++ show ty
            Union -> mirFail $ "evalPlace (PField, Union) NYI"

    M.TyDowncast (M.TyAdt nm _ _) i -> do
        adt <- findAdt nm
        enumFieldRef adt (fromInteger i) idx ref

    M.TyTuple ts -> tupleFieldRef ts idx tpr ref
    M.TyClosure ts -> tupleFieldRef ts idx tpr ref
    _ -> mirFail $
        "tried to get field " ++ show idx ++ " of unsupported type " ++ show ty
  where
    -- | Like `tyAdtDef`, but also accepts `TyDowncast (TyAdt ...)`.
    tyAdtDefSkipDowncast :: Collection -> M.Ty -> Maybe M.Adt
    tyAdtDefSkipDowncast col (M.TyDowncast ty' _) = tyAdtDef col ty'
    tyAdtDefSkipDowncast col ty = tyAdtDef col ty
evalPlaceProj ty (MirPlace tpr ref meta) (M.Index idxVar) = case (ty, tpr, meta) of
    (M.TyArray elemTy _sz, MirVectorRepr elemTpr, NoMeta) -> do
        idx' <- getIdx idxVar
        MirPlace elemTpr <$> subindexRef elemTpr ref idx' <*> pure NoMeta

    (M.TySlice elemTy, elemTpr, SliceMeta len) -> do
        idx <- getIdx idxVar
        G.assertExpr (R.App $ usizeLt idx len)
            (S.litExpr "Index out of range for access to slice")
        MirPlace elemTpr <$> mirRef_offset ref idx <*> pure NoMeta

    _ -> mirFail $ "indexing not supported on " ++ show (ty, tpr, meta)
  where
    getIdx :: M.Var -> MirGenerator h s ret (R.Expr MIR s UsizeType)
    getIdx var = do
        MirExp tpr idx <- varExp var
        Refl <- testEqualityOrFail tpr UsizeRepr $
            "expected index to be UsizeRepr, but got " ++ show tpr
        return idx
evalPlaceProj ty (MirPlace tpr ref meta) (M.ConstantIndex idx _minLen fromEnd) = case (ty, tpr, meta) of
    -- TODO: should this check sz >= minLen?
    (M.TyArray elemTy sz, MirVectorRepr elemTpr, NoMeta) -> do
        idx' <- getIdx idx (R.App $ usizeLit $ fromIntegral sz) fromEnd
        MirPlace elemTpr <$> subindexRef elemTpr ref idx' <*> pure NoMeta

    (M.TySlice elemTy, elemTpr, SliceMeta len) -> do
        idx <- getIdx idx len fromEnd
        G.assertExpr (R.App $ usizeLt idx len)
            (S.litExpr "Index out of range for access to slice")
        MirPlace elemTpr <$> mirRef_offset ref idx <*> pure NoMeta

    _ -> mirFail $ "indexing not supported on " ++ show (ty, tpr, meta)
  where
    getIdx :: Int -> R.Expr MIR s UsizeType -> Bool ->
        MirGenerator h s ret (R.Expr MIR s UsizeType)
    getIdx idx len True = return $ R.App $ usizeSub len $ R.App $ usizeLit $ fromIntegral idx
    getIdx idx _ False = return $ R.App $ usizeLit $ fromIntegral idx
-- Downcast is a no-op - it only affects the type reported by `M.type_of`.  The
-- `PField` case above looks for `TyDowncast` to handle enum accesses.
evalPlaceProj _ pl (M.Downcast _idx) = return pl
-- Subtype is a no-op, as it is only present in the MIR to making subtyping
-- explicit during optimizations and codegen.
evalPlaceProj _ pl (M.Subtype _ty) = return pl
-- Subslicing is defined on slices and arrays. See the haddock for `Subslice`
-- for details on the semantics of `fromIndex` and `toIndex`.
evalPlaceProj ty (MirPlace tpr ref meta) (M.Subslice fromIndex toIndex fromEnd) =
  case (ty, ref, tpr, meta) of
    (M.TySlice _elemTy, headRef, elemTpr, SliceMeta len) ->
      let lastIndex = mkLastIndex len
          newLen = R.App (lastIndex `usizeSub` firstIndex)
          newMeta = SliceMeta newLen
      in MirPlace elemTpr <$> mirRef_offset headRef firstIndex <*> pure newMeta

    -- TODO: https://github.com/GaloisInc/crucible/issues/1494
    --
    -- NB: after implementing this, update `Mir.Mir.typeOfProj`, which currently
    -- declares that `Subslice` unconditionally yields a slice. This is
    -- incorrect; `Subslice` applied to an array will yield an array.
    (M.TyArray {}, _, _, _) -> mirFail
      "evalPlaceProj: subslicing not yet supported on arrays"

    _ -> mirFail $
      "evalPlaceProj: subslicing not supported on " ++ show (ty, tpr, meta)
  where
    usize = R.App . usizeLit . fromIntegral
    firstIndex = usize fromIndex
    mkLastIndex len
      | fromEnd = R.App (len `usizeSub` usize toIndex)
      | otherwise = usize toIndex
evalPlaceProj ty (MirPlace _ _ meta) proj =
    mirFail $ "projection " ++ show proj ++ " not yet implemented for " ++ show (ty, meta)

--------------------------------------------------------------------------------------
-- ** Statements
--

-- Coerce `exp` from `ty1` to `ty2`.  Returns `Nothing` if the requested
-- coercion is not legal in Rust.
-- TODO: use this to implmeent parts of `evalCast`
tryCoerce :: M.Ty -> M.Ty -> MirExp s -> Maybe (MirGenerator h s ret (MirExp s))
tryCoerce ty1 ty2 exp
  | ty1 == ty2 = Just $ return exp
tryCoerce (M.TyRef ty1 M.Mut) (M.TyRef ty2 M.Immut) exp@(MirExp tpr e)
  | ty1 == ty2 = Just $ return exp
-- Special hack: using `CTyBox` as a constructor (as `typeOf` does for the
-- `Box` nullop) produces a `TyAdt` with an invalid `DefId`.  This is because
-- we don't have a way to compute the correct hash inside the `CTyBox` ctor.
-- So we use this special case to avoid erroring on `CTyBox` assignments.  (The
-- `CTyBox` pattern ignores the bad field already.)
-- TODO: implement `Eq` to ignore the field, or else remove it entirely and use
-- a different key for `findAdt`.
tryCoerce (CTyBox ty1) (CTyBox ty2) exp
  | ty1 == ty2 = Just $ return exp
tryCoerce _ _ _ = Nothing

evalCoerce :: M.Ty -> M.Ty -> MirExp s -> MirGenerator h s ret (MirExp s)
evalCoerce ty1 ty2 exp@(MirExp tpr _)
  | Just action <- tryCoerce ty1 ty2 exp = action
  | otherwise = mirFail $ "illegal or unimplemented coercion from "
        ++ show ty1 ++ " (concretely " ++ show tpr ++ ") to " ++ show ty2

doAssignCoerce :: HasCallStack => M.Lvalue -> M.Ty -> MirExp s -> MirGenerator h s ret ()
doAssignCoerce lv ty exp =
    doAssign lv =<< evalCoerce ty (M.typeOf lv) exp

doAssign :: HasCallStack => M.Lvalue -> MirExp s -> MirGenerator h s ret ()
doAssign lv (MirExp tpr val) = do
    place <- evalPlace lv
    case place of
        MirPlace tpr' ref _ -> do
            Refl <- testEqualityOrFail tpr tpr' $
                "ill-typed assignment of " ++ show tpr ++ " to " ++ show tpr'
                    ++ " (" ++ show (M.typeOf lv) ++ ") " ++ show lv
            writeMirRef tpr ref val


transStatement :: HasCallStack => M.Statement -> MirGenerator h s ret ()
transStatement (M.Statement skind spos) = do
  setPosition spos
  transStatementKind skind

transStatementKind :: HasCallStack => M.StatementKind -> MirGenerator h s ret ()
transStatementKind (M.Assign lv rv) = do
  col <- use $ cs . collection
  -- Skip writes to zero-sized fields, as they are effectively no-ops.
  when (not $ isZeroSized col $ typeOf lv) $ do
    re <- evalRval rv
    doAssignCoerce lv (M.typeOf rv) re
transStatementKind (M.StorageLive lv) = return ()
transStatementKind (M.StorageDead lv) = return ()
transStatementKind (M.SetDiscriminant lv i) = do
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
transStatementKind M.Nop = return ()
transStatementKind M.Deinit = return ()
transStatementKind (M.StmtIntrinsic ndi) =
    case ndi of
        -- rustc uses assumptions from `assume` to optimize code. If we
        -- encounter an occurrence of `assume` in MIR code, we should check
        -- that its argument is equal to `true`, as `assume(false)` is UB.
        NDIAssume cond -> do
            MirExp tpr e <- evalOperand cond
            Refl <- testEqualityOrFail tpr C.BoolRepr "expected Assume cond to be BoolType"
            G.assertExpr (S.app $ E.BoolEq e (S.app $ E.BoolLit True)) $
                S.app $ E.StringLit $ W4.UnicodeLiteral $ "assume(false) is undefined behavior"
        NDICopyNonOverlapping srcOp destOp countOp -> do
            srcExp <- evalOperand srcOp
            destExp <- evalOperand destOp
            countExp <- evalOperand countOp
            let elemTy = M.typeOfProj M.Deref $ M.typeOf srcOp
            Some tpr <- tyToReprM elemTy
            case (srcExp, destExp, countExp) of
                ( MirExp MirReferenceRepr src,
                  MirExp MirReferenceRepr dest,
                  MirExp UsizeRepr count )
                    -> void $ copyNonOverlapping tpr src dest count
                _   -> mirFail $ unlines
                         [ "bad arguments for intrinsics::copy_nonoverlapping: "
                         , show srcExp
                         , show destExp
                         , show countExp
                         ]
-- Per the docs, this statement kind is only useful in the const eval
-- interpreter, so it is a no-op for crucible-mir's purposes.
transStatementKind M.ConstEvalCounter = return ()

-- | Add a new `BranchTransInfo` entry for the current function.  Returns the
-- index of the new entry.
recordBranchTransInfo :: BranchTransInfo -> MirGenerator h s ret Int
recordBranchTransInfo info = do
    cur <- use $ transInfo . ftiBranches
    let idx = Seq.length cur
    transInfo . ftiBranches %= (Seq.|> info)
    return idx

-- | Mark the current block as unreachable in the translation metadata.
recordUnreachable :: MirGenerator h s ret ()
recordUnreachable = do
    blkID <- G.currentBlockID
    transInfo . ftiUnreachable %= Set.insert (Text.pack $ show $ blkID)

transSwitch ::
    Text ->         -- source location
    MirExp s ->     -- thing switching over
    [Integer] ->    -- switch comparisons
    [M.BasicBlockInfo] -> -- jumps
    MirGenerator h s ret a
transSwitch _pos _ [] [targ] = jumpToBlock targ
transSwitch pos exp vals blks = do
    setPosition pos
    lm <- use labelMap
    conds <- mapM (doCompare exp) vals
    labels <- forM blks $ \b -> case Map.lookup b lm of
        Just lab -> return lab
        Nothing -> mirFail "bad jump"

    isDropFlag <- switchIsDropFlagCheck vals blks
    let info = case (exp, vals, labels) of
            (MirExp C.BoolRepr _, [0], [fd, td]) | isDropFlag -> DropFlagBranch
            (MirExp C.BoolRepr _, [0], [fd, td]) ->
                BoolBranch (labelText td) (labelText fd) pos
            (MirExp C.BoolRepr _, [1], [td, fd]) ->
                BoolBranch (labelText td) (labelText fd) pos
            _ -> IntBranch vals (map labelText labels) pos
    branchId <- recordBranchTransInfo info

    go branchId 0 conds labels
  where
    doCompare :: MirExp s -> Integer -> MirGenerator h s ret (R.Expr MIR s C.BoolType)
    doCompare (MirExp C.BoolRepr e) x = case x of
        0 -> return $ S.app $ E.Not e
        1 -> return e
        _ -> mirFail $ "invalid BoolRepr constant " ++ show x ++ " in switch"
    doCompare (MirExp C.IntegerRepr e) x =
        return $ S.app $ E.IntEq e $ S.app $ E.IntLit x
    doCompare (MirExp (C.BVRepr w) e) x =
        return $ S.app $ E.BVEq w e $ S.app $ eBVLit w x
    doCompare (MirExp tpr _) _ =
        mirFail $ "invalid input type " ++ show tpr ++ " in switch"

    go :: Int -> Int -> [R.Expr MIR s C.BoolType] -> [R.Label s] ->
        MirGenerator h s ret a
    go branchId idx [] labels =
      case labels of
        [lab] -> G.jump lab
        _ ->
          mirFail $
            "no conditional but " ++ show (length labels) ++
            " labels in switch"
    go branchId idx [cond] labels =
      case labels of
        [lab1, lab2] -> do
          setPosition $ posStr branchId idx
          G.branch cond lab1 lab2
        _ ->
          mirFail $
            "conditional with " ++ show (length labels) ++
            " labels in switch"
    go branchId idx (cond : conds) labels =
      case labels of
        lab : labs -> do
          fallthrough <- G.defineBlockLabel $ go branchId (idx + 1) conds labs
          setPosition $ posStr branchId idx
          G.branch cond lab fallthrough
        [] -> mirFail "multiple conditionals but no labels in switch"

    labelText :: R.Label s -> Text
    labelText l = Text.pack $ show $ R.LabelID l

    posStr :: Int -> Int -> Text
    posStr branchId idx =
        pos <> " #" <> Text.pack (show branchId) <> "," <> Text.pack (show idx)

-- | Check if a switch appears to be a drop flag check.  Drop flag checks look
-- like this:
--
--          switchInt(_dropflag) -> [false: bb2, otherwise: bb1];
--
--      bb1:
--          _dropflag = const false;
--          drop(_var) -> bb2;
--
--      bb2:
--          ...
--
-- This has the unusual property that the false case jumps directly to the
-- "after" block - a normal `if` expression generates blocks for both the true
-- and false cases, even when the false case is empty.
switchIsDropFlagCheck :: [Integer] -> [M.BasicBlockInfo] -> MirGenerator h s ret Bool
switchIsDropFlagCheck [0] [f, t] = do
    fn <- expectFnContext
    let optTrueBb = fn ^. fbody . mblockmap . at t
    trueBb <- case optTrueBb of
        Just x -> return $ x
        Nothing -> mirFail $ "bad switch target " ++ show t
    let stmtsOk = case map _stmtKind (trueBb ^. bbstmts) of
            [Assign (LBase _) (Use (OpConstant (Constant TyBool (ConstBool False))))] ->
                True
            _ -> False
    let termOk = case trueBb ^. bbterminator . termKind of
            Drop _ dest _ -> dest == f
            _ -> False
    return $ stmtsOk && termOk
switchIsDropFlagCheck _ _ = return False

jumpToBlock :: M.BasicBlockInfo -> MirGenerator h s ret a
jumpToBlock bbi = do
    lm <- use labelMap
    case (Map.lookup bbi lm) of
      Just lab -> G.jump lab
      _ -> mirFail "bad jump"

doReturn :: HasCallStack => C.TypeRepr ret -> MirGenerator h s ret a
doReturn tr = do
    e <- getReturnExp tr

    -- In static initializers, "local" variables stay live past the end of the
    -- function so that the initializer can return references to them.  For
    -- example, in `static R: &'static i32 = &1;`, the initializer stores `1`
    -- into a local, then returns a reference to that local.  If we clean up
    -- that local like normal, then accesses to the returned reference will
    -- fail.  So we skip the cleanup when exiting a static initializer.
    --
    -- To detect if the current function is a static initializer, we check if
    -- there's an entry in `statics` matching the current `fname`.
    fn <- expectFnContext
    let curName = fn^.fname
    isStatic <- use $ cs . collection . statics . to (Map.member curName)
    when (not isStatic) cleanupLocals

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
lookupFunction :: forall h s ret. HasCallStack => MethName ->
   MirGenerator h s ret (Maybe (MirExp s, FnSig))
lookupFunction nm = do
  db   <- use debugLevel
  when (db > 3) $
    traceM $ "**lookupFunction: trying to resolve " ++ fmt nm

  -- these  are defined at the bottom of Mir.Generator
  isImpl    <- resolveFn nm
  isCustom  <- resolveCustom nm

  -- Given a (polymorphic) function handle, turn it into an expression by
  -- instantiating the type arguments
  let mkFunExp :: FH.FnHandle a r -> MirExp s
      mkFunExp fhandle =
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
            when (db > 3) $ do
              traceM $ "**lookupFunction: " ++ fmt nm ++ " resolved as normal call"

            return $ Just $ (mkFunExp fh, fs)

       | otherwise -> do
            when (db > 1) $ do
               traceM $ "***lookupFunction: Cannot find function " ++ show nm
            return Nothing

callHandle :: HasCallStack =>
    MirExp s -> Abi -> [M.Operand] -> MirGenerator h s ret (MirExp s)
callHandle e abi cargs
  | MirExp (C.FunctionHandleRepr ifargctx ifret) polyinst <- e = do
    db    <- use debugLevel
    when (db > 3) $
       traceM $ fmtDoc (PP.fillSep ["At normal function call of",
           PP.viaShow e, "with arguments", pretty cargs,
           "abi:",pretty abi])

    let tys = map typeOf cargs
    exps <- mapM evalOperand cargs
    exps' <- case abi of
      RustCall _
        -- Empty tuples use UnitRepr instead of StructRepr
        | [selfExp, MirExp C.UnitRepr _] <- exps -> do
          return [selfExp]

        | [selfExp, tupleExp@(MirExp MirAggregateRepr _)] <- exps
        , [_, M.TyTuple tupleTys] <- tys -> do
          tupleParts <- mapM (\(i, ty) -> getTupleElemTyped tupleExp i ty) (zip [0..] tupleTys)
          return $ selfExp : tupleParts

        -- Some code in rustc_codegen_cranelift suggests that there may be
        -- RustCall functions with only a tuple (which should be unpacked) and
        -- no self/receiver argument, but so far we haven't encountered such a
        -- thing.

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

callExp :: HasCallStack =>
           M.DefId
        -> [M.Operand]
        -> MirGenerator h s ret (MirExp s)
callExp funid cargs = do
   db    <- use debugLevel
   mhand <- lookupFunction funid
   isCustom <- resolveCustom funid
   case () of
     () | Just (CustomOp op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmtDoc (PP.fillSep ["At custom function call of",
                 pretty funid, "with arguments", pretty cargs])

          ops <- mapM evalOperand cargs
          let opTys = map M.typeOf cargs
          op opTys ops

        | Just (CustomOpNamed op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmtDoc (PP.fillSep ["At custom function call of",
                 pretty funid, "with arguments", pretty cargs])

          ops <- mapM evalOperand cargs
          op funid ops

       | Just (CustomMirOp op) <- isCustom -> do
          when (db > 3) $
            traceM $ fmtDoc (PP.fillSep ["At custom function call of",
               pretty funid, "with arguments", pretty cargs])
          op cargs

       | Just (hand, sig) <- mhand -> do
         callHandle hand (sig^.fsabi) cargs

     _ -> mirFail $ "callExp: Don't know how to call " ++ fmt funid



-- regular function calls: closure calls & dynamic trait method calls handled later
doCall :: forall h s ret a. (HasCallStack) => M.DefId -> [M.Operand]
   -> Maybe (M.Lvalue, M.BasicBlockInfo) -> C.TypeRepr ret -> MirGenerator h s ret a
doCall funid cargs cdest retRepr = do
    _am    <- use $ cs.collection
    db    <- use debugLevel
    isCustom <- resolveCustom funid
    case cdest of
      (Just (dest_lv, jdest)) -> do
            ret <- callExp funid cargs
            doAssign dest_lv ret
            jumpToBlock jdest

      Nothing
         -- special case for exit function that does not return
         | Just (CustomOpExit op) <- isCustom -> do
               exps <- mapM evalOperand cargs
               msg  <- op exps
               G.reportError (S.app $ E.StringLit $ W4.UnicodeLiteral msg)

        -- other functions that don't return
        | otherwise -> do
            _ <- callExp funid cargs
            -- TODO: is this the correct behavior?
            G.reportError (S.app $ E.StringLit $ fromString "Program terminated.")

transTerminator :: HasCallStack => M.Terminator -> C.TypeRepr ret -> MirGenerator h s ret a
transTerminator (M.Terminator tkind tpos) tr = do
    setPosition tpos
    transTerminatorKind tkind tpos tr

transTerminatorKind :: HasCallStack => M.TerminatorKind -> Text -> C.TypeRepr ret -> MirGenerator h s ret a
transTerminatorKind (M.Goto bbi) _tpos _tr =
    jumpToBlock bbi
transTerminatorKind t@(M.SwitchInt swop _swty svals stargs) tpos _tr
  | all Maybe.isJust svals = do
      s <- evalOperand swop
      transSwitch tpos s (Maybe.catMaybes svals) stargs
  | otherwise =
      mirFail $ "SwitchInt with no values to compare: " ++ show (pretty t)
transTerminatorKind (M.Return) _tpos tr =
    doReturn tr
transTerminatorKind (M.Call funcOp cargs cretdest) _tpos retTy = case M.typeOf funcOp of
  M.TyFnDef defId -> do
    isCustom <- resolveCustom defId
    doCall defId cargs cretdest retTy -- cleanup ignored
  M.TyFnPtr _ -> do
    func <- evalOperand funcOp
    ret <- callHandle func RustAbi cargs
    case cretdest of
      Just (dest_lv, jdest) -> do
        doAssign dest_lv ret
        jumpToBlock jdest
      Nothing ->
        G.reportError (S.app $ E.StringLit $ fromString "Program terminated.")
  calleeTy -> mirFail $ "expected callee to be a function, but it was "<>show calleeTy
transTerminatorKind (M.Assert cond expected msg target) _tpos _tr = do
    MirExp tpr e <- evalOperand cond
    Refl <- testEqualityOrFail tpr C.BoolRepr "expected Assert cond to be BoolType"
    G.assertExpr (S.app $ E.BoolEq e (S.app $ E.BoolLit expected)) $
        S.app $ E.StringLit $ W4.UnicodeLiteral $ msg
    jumpToBlock target
transTerminatorKind (M.Resume) _tpos tr =
    doReturn tr -- resume happens when unwinding
transTerminatorKind (M.Drop dlv dt dropFn) _tpos _tr = do
    let ptrOp = M.Temp $ M.Cast M.Misc
            (M.Temp $ M.AddressOf M.Mut dlv) (M.TyRawPtr (M.typeOf dlv) M.Mut)
    maybe (return ()) (\f -> void $ callExp f [ptrOp]) dropFn
    jumpToBlock dt
transTerminatorKind M.Abort _tpos tr =
    G.reportError (S.litExpr "process abort in unwinding")
transTerminatorKind M.Unreachable _tpos tr = do
    recordUnreachable
    G.reportError (S.litExpr "Unreachable!!!!!")
transTerminatorKind M.InlineAsm _tpos _tr =
    mirFail "Inline assembly not supported"


--- translation of toplevel glue ---

-- | Allocate RefCells for all locals and populate `varMap`.  Locals are
-- default-initialized when possible using the result of `initialValue`.
initLocals :: [M.Var] -> Set.Set Text.Text -> MirGenerator h s ret ()
initLocals localVars addrTaken = forM_ localVars $ \v -> do
    let name = v ^. varname
    let ty = v ^. varty
    Some tpr <- tyToReprM ty

    optVal <- initialValue ty >>= \case
        Nothing -> return Nothing
        Just (MirExp tpr' val) -> do
            Refl <- testEqualityOrFail tpr tpr' $
                "initialValue produced " ++ show tpr' ++ " instead of " ++ show tpr
                  ++ ", for " ++ show (pretty ty)
            return $ Just val

    -- FIXME: temporary hack to put every local behind a MirReference, to work
    -- around issues with `&fn()` variables.
    varinfo <-
      if True -- if Set.member name addrTaken
        then do
          ref <- newMirRef tpr
          case optVal of
              Nothing -> return ()
              Just val -> writeMirRef tpr ref val
          reg <- G.newReg ref
          return $ Some $ VarReference tpr reg
        else do
          reg <- case optVal of
              Nothing -> G.newUnassignedReg tpr
              Just val -> G.newReg val
          return $ Some $ VarRegister reg
    varMap %= Map.insert name varinfo

-- | Deallocate RefCells for all locals in `varMap`.
cleanupLocals :: MirGenerator h s ret ()
cleanupLocals = do
    vm <- use varMap
    forM_ (Map.elems vm) $ \(Some vi) -> case vi of
        VarReference _ reg -> G.readReg reg >>= dropMirRef
        _ -> return ()

-- | Look at all of the assignments in the basic block and return
-- the set of variables that have their addresses computed
addrTakenVars :: M.BasicBlock -> Set Text.Text
addrTakenVars bb = mconcat (map (f . M._stmtKind) (M._bbstmts (M._bbdata bb)))
 where
 f (M.Assign _ (M.Ref _ lv _)) = g lv
 f _ = mempty

 g (M.LBase (M.Var nm _ _ _)) = Set.singleton nm
 g (M.LProj lv _) = g lv


buildLabelMap :: forall h s ret. M.MirBody -> MirGenerator h s ret (LabelMap s)
buildLabelMap (M.MirBody _ blocks _) = Map.fromList <$> mapM buildLabel blocks

buildLabel :: forall h s ret. M.BasicBlock -> MirGenerator h s ret (M.BasicBlockInfo, R.Label s)
buildLabel (M.BasicBlock bi _) = do
    lab <- G.newLabel
    return (bi, lab)

-- | Build the initial state for translation of functions
initFnState :: (?debug::Int,?customOps::CustomOpMap,?assertFalseOnError::Bool)
            => CollectionState
            -> FnTransContext
            -> FnState s
initFnState colState transCtxt =
  FnState { _varMap     = Map.empty,
            _transContext = transCtxt,
            _debugLevel = ?debug,
            _cs         = colState,
            _labelMap   = Map.empty,
            _customOps  = ?customOps,
            _assertFalseOnError = ?assertFalseOnError,
            _transInfo  = mempty
         }


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
genFn :: HasCallStack =>
    M.Fn ->
    C.TypeRepr ret ->
    Ctx.Assignment (R.Atom s) args ->
    MirGenerator h s ret (G.Label s)
genFn (M.Fn fname argvars sig body@(MirBody localvars blocks _)) rettype inputs = do

  lm <- buildLabelMap body
  labelMap .= lm

  let addrTaken = mconcat (map addrTakenVars blocks)
  initLocals (argvars ++ localvars) addrTaken
  let inputExps = toListFC (\atom -> MirExp (R.typeOfAtom atom) (R.AtomExpr atom)) inputs
  inputExps' <- case sig ^. M.fsabi of
    M.RustCall (M.RcSpreadArg spreadArg) -> do
      -- The Rust signature looks like `(T, (U, V))`, but the Crucible version
      -- uses the untupled form `(T, U, V)`.  `argvars` follows the tupled
      -- form, but `inputExps` follows the untupled form.  Here we convert
      -- `inputExps` to match `argvars` by tupling up some of the arguments.
      --
      -- Arguments from `splitIndex` onward need to be tupled.  Note that
      -- `spreadArg` is 1-based (it's a MIR `Local` ID, and the first argument
      -- is local `_1`), but we convert to a 0-based index for convenience.
      let splitIndex = spreadArg - 1
      when (splitIndex > length inputExps) $
        mirFail $ "split index " ++ show splitIndex ++ " out of range for "
          ++ show (fmapFC R.typeOfAtom inputs)
      let selfExps = take splitIndex inputExps
      let tupleFieldExps = drop splitIndex inputExps
      tupleFieldTys <- case map typeOf $ drop splitIndex argvars of
        [M.TyTuple tys] -> return tys
        _ -> mirFail $ "expected tuple at position " ++ show splitIndex
          ++ ", but got " ++ show argvars
      tupleExp <- case tupleFieldTys of
        [] -> return $ MirExp C.UnitRepr (R.App E.EmptyApp)
        _ -> buildTupleMaybeM tupleFieldTys (map Just tupleFieldExps)
      return $ selfExps ++ [tupleExp]
    _ -> return inputExps
  initArgs inputExps' argvars

  db <- use debugLevel
  when (db > 3) $ do
     vmm <- use varMap
     let showVar var = fmt var ++ " : " ++ fmt (M.typeOf var)
     traceM $ "-----------------------------------------------------------------------------"
     traceM $ "Generating code for: " ++ show fname
     traceM $ "Function args are: " ++ List.intercalate "," (map showVar argvars)
     traceM $ "VarMap is: " ++ fmt (Map.keys vmm)
     traceM $ "Body is:\n" ++ fmt body
     traceM $ "-----------------------------------------------------------------------------"
  blocks@(enter NE.:| _) <- case body of
    M.MirBody _mvars (enter : blocksRest) _ -> return (enter NE.:| blocks)
    _ -> mirFail $ "expected body to be MirBody, but got " ++ show body
  -- actually translate all of the blocks of the function
  mapM_ (registerBlock rettype) blocks
  let (M.BasicBlock bbi _) = enter
  lm <- use labelMap
  case (Map.lookup bbi lm) of
    Just lbl -> return lbl
    _ -> mirFail "bad thing happened"

  where
    initArgs :: HasCallStack =>
        [MirExp s] -> [M.Var] -> MirGenerator h s ret ()
    initArgs inputs vars =
        case (inputs, vars) of
            ([], []) -> return ()
            (MirExp inputTpr inputExpr : inputs', var : vars') -> do
                mvi <- use $ varMap . at (var ^. varname)
                Some vi <- case mvi of
                    Just x -> return x
                    Nothing -> mirFail $ "no varinfo for arg " ++ show (var ^. varname)
                Refl <- testEqualityOrFail inputTpr (varInfoRepr vi) $
                    "type mismatch in initialization of " ++ show (var ^. varname) ++ ": " ++
                        show inputTpr ++ " != " ++ show (varInfoRepr vi)
                case vi of
                    VarRegister reg -> G.assignReg reg inputExpr
                    VarReference tpr refReg -> do
                        ref <- G.readReg refReg
                        writeMirRef tpr ref inputExpr
                    VarAtom _ -> mirFail $ "unexpected VarAtom"
                initArgs inputs' vars'
            _ -> mirFail $ "mismatched argument count for " ++ show fname


genClosureFnPointerShim :: forall h s args ret.
  HasCallStack =>
  M.DefId ->
  C.TypeRepr ret ->
  Ctx.Assignment (R.Atom s) args ->
  MirGenerator h s ret (G.Label s)
genClosureFnPointerShim callOnceId tprRet argAtoms = do
  -- Look up `callOnceId` in the `HandleMap`.
  hm <- use $ cs . handleMap
  MirHandle _ sig (fh :: FH.FnHandle args' ret') <- case Map.lookup callOnceId hm of
    Just x -> return x
    Nothing -> mirFail $ "ClosureFnPointerShim callee " ++ show callOnceId ++ " not found"
  -- Check that the function `call_once` function signature looks like we
  -- expect, and extract the real argument types.
  --
  -- This implementation of `ClosureFnPointerShim` works for the cases we've
  -- seen so far, but hardcodes certain assumptions about the shape of the
  -- callee function `callOnceId` and duplicates a bit of the call translation
  -- from `callExp` and `callHandle`.  In the future, it might be better to
  -- turn this into a `CustomMirOp`, like `cloneShimDef` in `TransCustom`.
  -- However, currently it's not possible to obtain a function pointer to a
  -- `CustomOp` function (the `CustomOp` replaces the call instruction
  -- instead), which would need to be changed first.
  let callOnceArgTys = abiFnArgs sig
  when (sig ^. fsabi /= M.RustCall (M.RcSpreadArg 2)) $
    mirFail $ "expected " ++ show callOnceId
      ++ " to have RustCall ABI with spread_arg = 2, not " ++ show (sig ^. fsabi)
  (callOnceArgTy0, callOnceArgTys') <- case callOnceArgTys of
    x:y -> return (x, y)
    [] -> mirFail $ "expected " ++ show callOnceId ++ " to have at least one arg, but got "
      ++ show callOnceArgTys
  when (callOnceArgTy0 /= M.TyClosure []) $
    mirFail $ "expected " ++ show callOnceId ++ " arg 0 to be an empty closure, but got "
      ++ show callOnceArgTy0
  -- Build the argument values for `call_once`.
  let tprArg0 = MirAggregateRepr
  arg0 <- mirAggregate_uninit 0
  let ctxArgs = Ctx.singleton tprArg0 Ctx.<++> fmapFC (R.typeOfAtom) argAtoms
  let args = Ctx.singleton arg0 Ctx.<++> fmapFC (R.AtomExpr @MIR) argAtoms
  -- More checks, necessary for the call below to typecheck.
  Refl <- testEqualityOrFail (FH.handleArgTypes fh) ctxArgs $
    "genClosureFnPointerShim: expected " ++ show callOnceId ++ " to take "
      ++ show ctxArgs ++ ", but got " ++ show (FH.handleArgTypes fh)
  Refl <- testEqualityOrFail (FH.handleReturnType fh) tprRet $
    "genClosureFnPointerShim: expected " ++ show callOnceId ++ " to return "
      ++ show tprRet ++ ", but got " ++ show (FH.handleReturnType fh)
  -- Actually call the function.
  let funcExp = R.App $ E.HandleLit fh
  label <- G.newLabel
  G.defineBlock label $ do
    ret <- G.call funcExp args
    G.returnFromFunction ret
  return label

transCommon :: forall h.
  ( HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool
  , ?printCrucible::Bool)
  => CollectionState
  -> M.DefId
  -> FnTransContext
  -> (forall s args ret.
    C.TypeRepr ret
    -> Ctx.Assignment (R.Atom s) args
    -> MirGenerator h s ret (G.Label s))
  -> ST h (Text, Core.AnyCFG MIR, FnTransInfo)
transCommon colState name context gen = do
    MirHandle _hname _hsig (handle :: FH.FnHandle args ret) <-
        case Map.lookup name (colState^.handleMap) of
            Nothing -> error "bad handle!!"
            Just mh -> return mh
    ftiRef <- newSTRef mempty
    let rettype  = FH.handleReturnType handle
    let def :: G.FunctionDef MIR FnState args ret (ST h)
        def inputs = (s,f) where
          s = initFnState colState context
          f = do
              lbl <- gen rettype inputs
              fti <- use transInfo
              lift $ writeSTRef ftiRef fti
              G.jump lbl
    R.SomeCFG g <- defineFunctionNoAuxs handle def
    when ?printCrucible $ do
        traceM $ unwords [" =======", show name, "======="]
        traceShowM $ pretty g
        traceM $ unwords [" ======= end", show name, "======="]
    fti <- readSTRef ftiRef
    case SSA.toSSA g of
      Core.SomeCFG g_ssa -> return (M.idText name, Core.AnyCFG g_ssa, fti)

transInstance :: forall h.
  ( HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool
  , ?printCrucible::Bool)
  => CollectionState
  -> M.Intrinsic
  -> ST h (Maybe (Text, Core.AnyCFG MIR, Maybe FnTransInfo))
transInstance colState (M.Intrinsic defId (M.Instance kind origDefId _substs))
  -- If a function body is available, translate it, regardless of the `kind`.
  | Just fn <- colState ^. collection . M.functions . at defId = do
      (name, cfg, fti) <- transCommon colState defId (FnContext fn) (genFn fn)
      return $ Just (name, cfg, Just fti)
  -- For some `kind`s, we have special logic for generating a body.
  | M.IkVirtual dynTraitName methodIndex <- kind = do
      let methodId = origDefId
      (name, cfg) <- transVirtCall colState defId methodId dynTraitName methodIndex
      return $ Just (name, cfg, Nothing)
  | M.IkClosureFnPointerShim <- kind = do
      (name, cfg, fti) <- transCommon colState defId ShimContext
        (genClosureFnPointerShim origDefId)
      return $ Just (name, cfg, Just fti)
  | otherwise = return Nothing

transStatic :: forall h.
  ( HasCallStack, ?debug::Int, ?customOps::CustomOpMap, ?assertFalseOnError::Bool
  , ?printCrucible::Bool)
  => CollectionState
  -> M.Static
  -> ST h (Maybe (Text, Core.AnyCFG MIR, FnTransInfo))
transStatic colState st
  -- Statics with a `ConstVal` initializer don't need a CFG, and might not have
  -- a MIR body in `functions`.
  | Just _ <- st ^. M.sConstVal = return Nothing
  | otherwise = do
      let defId = st ^. M.sName
      fn <- case colState ^. collection . M.functions . at defId of
        Just x -> return x
        -- For each entry in `statics`, there should be a corresponding entry
        -- in `functions` giving the MIR body of the static initializer.
        Nothing -> panic "transStatic" ["function " ++ show defId ++ " not found for static"]
      (name, cfg, fti) <- transCommon colState defId (FnContext fn) (genFn fn)
      return $ Just (name, cfg, fti)


-- | Allocate method handles for each of the functions in the Collection
mkHandleMap :: (HasCallStack) => Collection -> FH.HandleAllocator -> IO HandleMap
mkHandleMap col halloc = mapM mkHandle (col^.functions) where

    mkHandle :: M.Fn -> IO MirHandle
    mkHandle (M.Fn fname _fargs fsig _fbody)  = do
      let targs = abiFnArgs fsig
          handleName = FN.functionNameFromText (M.idText fname)
      Some argctx <- case tyListToCtx col targs (Right . Some) of
         Left err -> fail ("mkHandle: " ++ err)
         Right x -> return x
      Some retrepr <- case tyToRepr col (fsig^.fsreturn_ty) of
        Left err -> fail ("mkHandle: " ++ err)
        Right x -> return x
      h <- FH.mkHandle' halloc handleName argctx retrepr
      return $ MirHandle fname fsig h

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
      | Just fn <- Map.lookup fnName (col^.functions) = do
        let shimSig = vtableShimSig vtableName fnName (fn ^. M.fsig)
            handleName = FN.functionNameFromText (vtableShimName vtableName fnName)

        Some argctx <- case tyListToCtx col (abiFnArgs shimSig) (Right . Some) of
          Left err -> fail ("mkVtableMap: " ++ err)
          Right x -> return x

        Some retrepr <- case tyToRepr col (shimSig ^. M.fsreturn_ty) of
          Left err -> fail ("mkVtableMap: " ++ err)
          Right x -> return x

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
    let implMirArg0 = case implFn ^. M.fsig . M.fsarg_tys of
                        arg_ty:_ -> arg_ty
                        [] -> die ["shim has no argument types"] in
    let implArgs = FH.handleArgTypes implFH in
    let implRet = FH.handleReturnType implFH in

    -- Peel off receiver from shim and impl arg lists
    -- NB: assignments built by `tyListToCtx` are constructed in reverse order
    elimAssignmentLeft shimArgs (die ["shim has no arguments"])
        $ \eqShimArgs@Refl shimArg0 shimArgs' ->
    elimAssignmentLeft implArgs (die ["impl has no arguments"])
        $ \eqImplArgs@Refl implArg0 implArgs' ->

    -- Check equalities over Crucible (translated) types:
    --  * Non-receiver arg types of impl and shim are equal
    (\k -> case testEquality implArgs' shimArgs' of { Just x -> k x;
        Nothing -> die ["argument type mismatch:", show implArgs, "vs", show shimArgs] })
        $ \eqArgs'@Refl ->
    --  * Return types of impl and shim are equal
    (\k -> case testEquality implRet shimRet of { Just x -> k x;
        Nothing -> die ["return type mismatch:", show implRet, "vs", show shimRet] })
        $ \eqRet@Refl ->
    --  * Shim receiver type is ANY
    (\k -> case testEquality shimArg0 C.AnyRepr of { Just x -> k x;
        Nothing -> die ["shim receiver is not ANY:", show shimArg0] }) $ \eqShimArg0Any@Refl ->

    -- Construct the shim and return it
    withBuildShim implMirArg0 implArg0 implArgs' implRet implFH $ \shimDef -> do
        R.SomeCFG g <- defineFunctionNoAuxs shimFH shimDef
        case SSA.toSSA g of
            Core.SomeCFG g_ssa -> return (vtableShimName vtableName fnName, Core.AnyCFG g_ssa)

  where
    die :: [String] -> a
    die xs = error $ dieMsg xs
    dieMsg :: [String] -> String
    dieMsg xs = unwords (["failed to generate vtable shim for", show vtableName,
            "entry", show defName, "(instance", show fnName, "):"] ++ xs)

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
        (G.FunctionDef MIR FnState (C.AnyType :<: argTys) retTy (ST h) -> r) ->
        r
    withBuildShim recvMirTy recvTy argTys retTy implFH k =
        k $ buildShim recvMirTy recvTy argTys retTy implFH

    fnState :: forall s. FnState s
    fnState = initFnState colState ShimContext

    buildShim :: forall recvTy argTys retTy .
        M.Ty -> C.TypeRepr recvTy -> C.CtxRepr argTys -> C.TypeRepr retTy ->
        FH.FnHandle (recvTy :<: argTys) retTy ->
        G.FunctionDef MIR FnState (C.AnyType :<: argTys) retTy (ST h)
    buildShim recvMirTy recvTy argTys retTy implFH
      | M.TyRef    _recvMirTy' _ <- recvMirTy = buildShimForRef recvTy argTys implFH
      | M.TyRawPtr _recvMirTy' _ <- recvMirTy = buildShimForRef recvTy argTys implFH
      | otherwise = \argsA -> (\x -> (fnState, x)) $ do
        mirFail $ dieMsg ["unsupported MIR receiver type", show recvMirTy]

    buildShimForRef :: forall recvTy argTys retTy .
        C.TypeRepr recvTy ->
        C.CtxRepr argTys ->
        FH.FnHandle (recvTy :<: argTys) retTy ->
        G.FunctionDef MIR FnState (C.AnyType :<: argTys) retTy (ST h)
    buildShimForRef recvTy argTys implFH = \argsA -> (\x -> (fnState, x)) $ do
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

-- Generate method handles for all generated shims used in the current crate.
mkShimHandleMap :: (HasCallStack) =>
    Collection -> FH.HandleAllocator -> IO HandleMap
mkShimHandleMap col halloc = mconcat <$> mapM mkHandle (Map.toList $ col ^. M.intrinsics)
  where
    mkHandle :: (M.IntrinsicName, M.Intrinsic) ->
        IO (Map M.DefId MirHandle)
    mkHandle (name, intr)
      | IkVirtual dynTraitName _ <- intr ^. M.intrInst . M.inKind =
        let methName = intr ^. M.intrInst ^. M.inDefId
            trait = lookupTrait col dynTraitName
            methSig = traitMethodSig trait methName

            handleName = FN.functionNameFromText $ M.idText $ intr ^. M.intrName
        in liftM (Map.singleton name) $ do
            Some argctx <- case tyListToCtx col (abiFnArgs methSig) (Right . Some) of
              Left err -> fail ("mkShimHandleMap: " ++ err)
              Right x -> return x
            Some retrepr <- case tyToRepr col (methSig ^. M.fsreturn_ty) of
              Left err -> fail ("mkShimHandleMap: " ++ err)
              Right x -> return x
            h <- FH.mkHandle' halloc handleName argctx retrepr
            return $ MirHandle (intr ^. M.intrName) methSig h
      | IkClosureFnPointerShim <- intr ^. M.intrInst . M.inKind = do
        let callMutId = intr ^. M.intrInst . M.inDefId
        callMutFn <- case col ^. M.functions . at callMutId of
            Just x -> return x
            Nothing -> error $ "undefined function " ++ show callMutId
              ++ " for IkClosureFnPointerShim " ++ show name
        let callMutSig = callMutFn ^. M.fsig
        untupledArgTys <- case callMutSig ^? M.fsarg_tys . ix 1 of
            Just (M.TyTuple tys) -> return tys
            x -> error $ "expected tuple for second arg of " ++ show callMutId
              ++ ", but got " ++ show x ++ ", for IkClosureFnPointerShim " ++ show name
        let returnTy = callMutSig ^. M.fsreturn_ty
        let fnPtrSig = M.FnSig untupledArgTys returnTy RustAbi
        let handleName = FN.functionNameFromText $ M.idText $ intr ^. M.intrName

        Some argCtx <- case  tyListToCtx col untupledArgTys (Right . Some) of
          Left err -> fail ("mkShimHandleMap: " ++ err)
          Right x -> return x

        Some retRepr <- case tyToRepr col returnTy of
          Left err -> fail ("mkShimHandleMap: " ++ err)
          Right x -> return x

        h <- FH.mkHandle' halloc handleName argCtx retRepr
        let mh = MirHandle (intr ^. M.intrName) fnPtrSig h
        return $ Map.singleton name mh

      | otherwise = return Map.empty
      where


-- | Provided a @&dyn@ receiver and appropriate arguments, generate a pair of
-- @(function, arguments)@ expressions representing a virtual-call shim that
-- will look up and call the right concrete method and provide it those
-- arguments. See 'doVirtTailCall' for an example of actualy calling the
-- function.
mkVirtCall
  :: HasCallStack
  => M.Collection
  -> M.TraitName
  -> Integer -- ^ The method index
  -> C.TypeRepr recvTy -- ^ The type of the method receiver (should be @&dyn Trait@)
  -> R.Expr MIR s recvTy -- ^ The method receiver (should be @&dyn Trait@)
  -> C.CtxRepr argTys -- ^ The types of the arguments (excluding the receiver)
  -> Ctx.Assignment (R.Expr MIR s) argTys -- ^ The arguments (excluding the receiver)
  -> C.TypeRepr retTy -- ^ The return type
  -> G.Generator MIR s t ret (ST h)
    ( R.Expr MIR s (C.FunctionHandleType (C.AnyType :<: argTys) retTy)
    , Ctx.Assignment (R.Expr MIR s) (C.AnyType :<: argTys))
mkVirtCall col dynTraitName methIndex recvTy recvExpr argTys argExprs retTy =
    checkEq recvTy DynRefRepr (die ["method receiver is not `&dyn`/`&mut dyn`"])
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
        $ \eqVtsRetTy@Refl -> do

    let recvData = R.App $ E.GetStruct recvExpr dynRefDataIndex MirReferenceRepr
    let recvVtable = R.App $ E.GetStruct recvExpr dynRefVtableIndex C.AnyRepr

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
            (C.FunctionHandleRepr (C.AnyRepr <: argTys) vtsRetTy)

    pure (vtsFH, (R.App (E.PackAny MirReferenceRepr recvData) <: argExprs))

  where
    die :: [String] -> a
    die words = error $ unwords
        (["failed to generate virtual-call shim for method", show methIndex,
            "of trait", show dynTraitName] ++ words)

    dynTrait = case col ^. M.traits . at dynTraitName of
        Just x -> x
        Nothing -> die ["undefined trait " ++ show dynTraitName]

    -- The type of the entire vtable.  Note `traitVtableType` wants the trait
    -- substs only, omitting the Self type.
    vtableType :: Some C.TypeRepr
    vtableType = case traitVtableType col dynTraitName dynTrait of
      Left err -> die ["vtableType: " ++ err]
      Right x -> x


-- | Use 'mkVirtCall' to create virtual-call function and argument expressions,
-- then tail-call that function on those arguments.
doVirtTailCall
  :: HasCallStack
  => M.Collection
  -> M.TraitName
  -> Integer -- ^ The method index
  -> C.TypeRepr recvTy -- ^ The type of the method receiver (should be @&dyn Trait@)
  -> R.Expr MIR s recvTy -- ^ The method receiver (should be @&dyn Trait@)
  -> C.CtxRepr argTys -- ^ The types of the arguments (excluding the receiver)
  -> Ctx.Assignment (R.Expr MIR s) argTys -- ^ The arguments (excluding the receiver)
  -> C.TypeRepr retTy -- ^ The return type
  -> G.Generator MIR s t retTy (ST h) (R.Expr MIR s retTy)
doVirtTailCall col dynTraitName methodIndex recvTy recvExpr argTys argExprs retTy = do
  (fnHandle, args) <- mkVirtCall col dynTraitName methodIndex recvTy recvExpr argTys argExprs retTy
  G.tailCall fnHandle args


-- | Use 'mkVirtCall' to create virtual-call function and argument expressions,
-- then call that function on those arguments.
--
-- Note the extra quantified variable in the return type in this vs.
-- 'doVirtTailCall', which makes this function slightly less restrictive:
--
-- > G.Generator MIR s t anyRetTy (ST h) (R.Expr MIR s retTy)
--
-- vs
--
-- > G.Generator MIR s t retTy    (ST h) (R.Expr MIR s retTy)
doVirtCall
  :: HasCallStack
  => M.Collection
  -> M.TraitName
  -> Integer -- ^ The method index
  -> C.TypeRepr recvTy -- ^ The type of the method receiver (should be @&dyn Trait@)
  -> R.Expr MIR s recvTy -- ^ The method receiver (should be @&dyn Trait@)
  -> C.CtxRepr argTys -- ^ The types of the arguments (excluding the receiver)
  -> Ctx.Assignment (R.Expr MIR s) argTys -- ^ The arguments (excluding the receiver)
  -> C.TypeRepr retTy -- ^ The return type
  -> G.Generator MIR s t anyRetTy (ST h) (R.Expr MIR s retTy)
doVirtCall col dynTraitName methodIndex recvTy recvExpr argTys argExprs retTy = do
  (fnHandle, args) <- mkVirtCall col dynTraitName methodIndex recvTy recvExpr argTys argExprs retTy
  G.call fnHandle args


-- | Translate a virtual call. The logic for looking up the right method in the
-- vtable is implemented in 'mkVirtCall'.
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
    let retTy = FH.handleReturnType methFH

        -- | This is actually a 'G.FunctionDef', but that synonym hides some
        -- types we apparently need to write out in this signature.
        withArgs ::
          Ctx.Assignment (R.Atom s) args ->
          ([s], G.Generator MIR s [] ret (ST h) (R.Expr MIR s ret))
        withArgs argsAssn =
          let (recvExpr, argExprs) = splitMethodArgs argsAssn (Ctx.size argTys)
              callExpr =
                doVirtTailCall
                  (colState ^. collection)
                  dynTraitName
                  (fromInteger methIndex)
                  recvTy
                  recvExpr
                  argTys
                  argExprs
                  retTy
          in  ([], callExpr)
      in  do
            R.SomeCFG g <- defineFunctionNoAuxs methFH withArgs
            case SSA.toSSA g of
                Core.SomeCFG g_ssa -> return (M.idText intrName, Core.AnyCFG g_ssa)

  where
    die :: [String] -> a
    die words = error $ unwords
        (["failed to generate virtual-call shim for", show methName,
            "(intrinsic", show intrName, "):"] ++ words)

    methMH = case Map.lookup intrName (colState ^. handleMap) of
        Just x -> x
        Nothing -> die ["failed to find method handle for", show intrName]

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
    | adt <- Map.elems $ col^.M.adts, Lens.is _Enum (adt^.M.adtkind) ]

-- | Gather all of the 'M.DefId's in a 'M.Collection' and construct a
-- 'crateHashesMap' from it. To accomplish this, it suffices to look at the
-- domain of each map in a 'M.Collection' (with a handful of exceptions—see
-- the comments below), which ranges over 'M.DefId's.
mkCrateHashesMap :: M.Collection -> Map Text (NonEmpty Text)
mkCrateHashesMap
    (Collection _version
                functionsM adtsM adtsOrigM traitsM
                staticsM vtablesM intrinsicsM
                -- namedTys ranges over type names, which aren't full DefIds.
                _namedTysM
                _layoutsM
                langItemsM
                -- The roots and tests are duplicates of other Maps' DefIds.
                _rootsM _testsM) =
  Map.fromList $
       f functionsM
    ++ f adtsM
    ++ f adtsOrigM
    ++ f traitsM
    ++ f staticsM
    ++ f vtablesM
    ++ f intrinsicsM
    ++ f langItemsM
  where
    f :: Map M.DefId a -> [(Text, NonEmpty Text)]
    f m = map (\did -> (did ^. M.didCrate, did ^. M.didCrateDisambig :| []))
              (Map.keys m)

---------------------------------------------------------------------------

-- | transCollection: translate a MIR collection
transCollection ::
    (HasCallStack, ?debug::Int, ?assertFalseOnError::Bool,
     ?customOps::CustomOpMap,
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
    hmap2 <- mkShimHandleMap col halloc
    let hmap = hmap1 <> hmap2

    when (?debug > 3) $ do
      forM_ (Map.toList hmap) $ \(name, mh) -> do
        MirHandle _ sig handle <- return mh
        traceM $ "function " ++ show name ++ ":"
        traceM $ "  sig = " ++ show (pretty sig)
        traceM $ "  handle = " ++ show (FH.handleType handle)

    vm <- mkVtableMap col halloc

    -- translate the statics and create the initialization code
    -- allocate references for statics
    let allocateStatic :: Static -> Map M.DefId StaticVar -> IO (Map M.DefId StaticVar)
        allocateStatic static staticMap = do
          Some staticRepr <- case tyToRepr col (static^.sTy) of
            Left err -> fail ("allocateState: " ++ err)
            Right x -> return x
          let gname =  (M.idText (static^.sName) <> "_global")
          g <- G.freshGlobalVar halloc gname staticRepr
          return $ Map.insert (static^.sName) (StaticVar g) staticMap

    sm <- foldrM allocateStatic Map.empty (col^.statics)

    let dm = mkDiscrMap col
    let chm = mkCrateHashesMap col

    let colState :: CollectionState
        colState = CollectionState hmap vm sm dm chm col

    -- translate all of the functions
    fnInfo <- Maybe.catMaybes <$>
      mapM (stToIO . transInstance colState) (Map.elems (col^.M.intrinsics))
    staticInfo <- Maybe.catMaybes <$>
      mapM (stToIO . transStatic colState) (Map.elems (col^.M.statics))
    let allInfo = fnInfo ++ [(n, c, Just i) | (n, c, i) <- staticInfo]
    let pairs1 = [(name, cfg) | (name, cfg, _) <- allInfo]
    let transInfo = Map.fromList [(name, fti) | (name, _, Just fti) <- allInfo]
    pairs2 <- mapM (stToIO . transVtable colState) (Map.elems (col^.M.vtables))

    return $ RustModule
                { _rmCS    = colState
                , _rmCFGs  = Map.fromList (pairs1 <> concat pairs2)
                , _rmTransInfo = transInfo
                }

-- | Produce a crucible CFG that initializes the global variables for the static
-- part of the crate.
--
-- Note that while static items' definitions can depend on other static items,
-- this function does not currently translate static items in a way that
-- respects dependency order in general. (See #1108.) We do make a limited
-- effort to minimize the chances of static items being translated in the wrong
-- order, however. See the comments near @constValStatics@/@nonConstValStatics@
-- below.
transStatics ::
  (?debug::Int,?customOps::CustomOpMap,?assertFalseOnError::Bool) =>
  CollectionState -> FH.HandleAllocator -> IO (Core.AnyCFG MIR)
transStatics colState halloc = do
  let sm = colState^.staticMap
  let hmap = colState^.handleMap
  let initializeStatic :: forall h s r . Static -> MirGenerator h s r ()
      initializeStatic static =
        let staticName = static^.sName in
        case Map.lookup staticName sm of
          Just (StaticVar g) ->
            let repr = G.globalType g in
            if |  Just constval <- static^.sConstVal
               -> do let constty = static^.sTy
                     Some tpr <- tyToReprM constty
                     MirExp constty' constval' <- transConstVal constty (Some tpr) constval
                     case testEquality repr constty' of
                       Just Refl -> G.writeGlobal g constval'
                       Nothing -> error $ "BUG: invalid type for constant initializer " ++ fmt staticName
                                       ++ ", expected " ++ show repr ++ ", got " ++ show constty'

               |  Just (MirHandle _ _ (handle :: FH.FnHandle init ret))
                    <- Map.lookup staticName hmap
               -> case ( testEquality repr        (FH.handleReturnType handle)
                       , testEquality (Ctx.empty) (FH.handleArgTypes handle)
                       ) of
                    (Just Refl, Just Refl) -> do
                      val <- G.call (G.App $ E.HandleLit handle) Ctx.empty
                      G.writeGlobal g val

                    _ -> error $ "BUG: invalid type for initializer function " ++ fmt staticName

               |  otherwise
               -> error $ "BUG: cannot find initializer for static " ++ fmt staticName
          Nothing -> error $ "BUG: cannot find global for " ++ fmt staticName

  -- TODO: make the name of the static initialization function configurable
  let initName = FN.functionNameFromText "static_initializer"
  initHandle <- FH.mkHandle' halloc initName Ctx.empty C.UnitRepr
  let allStatics :: [Static]
      allStatics = Map.elems (colState^.collection.statics)
  -- Partition the static items into those with constant initializer expressions
  -- (constValStatics) and those with non-constant initializer expressions
  -- (nonConstValStatics). We do this because nonConstValStatics can depend on
  -- constValStatics, but because constValStatics typically use names like
  -- {{alloc}}[0], their names are almost certain to be later alphabetically
  -- than nonConstValStatics' names. This, in turn, is liable to trigger the
  -- issues observed in #1108 when one tries to translate a nonConstValStatic
  -- before the constValStatic that it depends on.
  --
  -- To work around #1108, we deliberately translate all constValStatics before
  -- translating any nonConstValStatics. This is not a complete fix for #1108,
  -- but it does make it far less likely to appear in practice.
  let constValStatics, nonConstValStatics :: [Static]
      (constValStatics, nonConstValStatics) =
        List.partition (\s -> Maybe.isJust (s ^. sConstVal)) allStatics
  let def :: G.FunctionDef MIR FnState Ctx.EmptyCtx C.UnitType (ST w)
      def inputs = (s, f) where
          s = initFnState colState StaticContext
          f = do mapM_ initializeStatic constValStatics
                 mapM_ initializeStatic nonConstValStatics
                 return (R.App $ E.EmptyApp)
  init_cfg <- stToIO $ do
    R.SomeCFG g <- defineFunctionNoAuxs initHandle def
    case SSA.toSSA g of
        Core.SomeCFG g_ssa -> return (Core.AnyCFG g_ssa)

  return init_cfg

------------------------------------------------------------------------------------------------


--
-- Generate a loop that copies `len` elements starting at `ptr0` into a vector.
--
vectorCopy :: C.TypeRepr tp ->
              G.Expr MIR s MirReferenceType ->
              G.Expr MIR s UsizeType ->
              MirGenerator h s ret (G.Expr MIR s (C.VectorType tp))
vectorCopy tpr ptr0 len = do
  let cond = S.app $ usizeEq len $ S.app $ usizeLit 0
  c_id <- G.newLambdaLabel' (C.VectorRepr tpr)
  -- Then branch
  x_id <- G.defineBlockLabel $ do
    G.jumpToLambda c_id $ S.app $ E.VectorLit tpr mempty
  -- Else branch
  y_id <- G.defineBlockLabel $ do
    elt0 <- readMirRef tpr ptr0
    let out = S.app $ E.VectorReplicate tpr (S.app $ usizeToNat len) elt0
    iRef <- G.newRef $ S.app $ usizeLit 0
    ptrRef <- G.newRef ptr0
    outRef <- G.newRef out
    let pos = PL.InternalPos
    G.while (pos, do i <- G.readRef iRef
                     return (G.App $ usizeLt i len))
            (pos, do i <- G.readRef iRef
                     ptr <- G.readRef ptrRef
                     out <- G.readRef outRef
                     elt <- readMirRef tpr ptr
                     let i' = S.app $ usizeAdd i (S.app $ usizeLit 1)
                     ptr' <- mirRef_offset ptr (S.app $ usizeLit 1)
                     let out' = S.app $ vectorSetUsize tpr R.App out i elt
                     G.writeRef iRef i'
                     G.writeRef ptrRef ptr'
                     G.writeRef outRef out')
    out <- G.readRef outRef
    G.jumpToLambda c_id out
  G.continueLambda c_id (G.branch cond x_id y_id)

ptrCopy ::
    C.TypeRepr tp ->
    G.Expr MIR s MirReferenceType ->
    G.Expr MIR s MirReferenceType ->
    G.Expr MIR s UsizeType ->
    MirGenerator h s ret ()
ptrCopy tpr src dest len = do
    iRef <- G.newRef $ S.app $ usizeLit 0
    let pos = PL.InternalPos
    G.while (pos, do i <- G.readRef iRef
                     return (G.App $ usizeLt i len))
            (pos, do i <- G.readRef iRef
                     src' <- mirRef_offset src i
                     dest' <- mirRef_offset dest i
                     val <- readMirRef tpr src'
                     writeMirRef tpr dest' val
                     let i' = S.app $ usizeAdd i (S.app $ usizeLit 1)
                     G.writeRef iRef i')
    G.dropRef iRef

copyNonOverlapping ::
    C.TypeRepr tp ->
    R.Expr MIR s MirReferenceType ->
    R.Expr MIR s MirReferenceType ->
    R.Expr MIR s UsizeType ->
    MirGenerator h s ret (MirExp s)
copyNonOverlapping tpr src dest count = do
    -- Assert that the two regions really are nonoverlapping.
    maybeOffset <- mirRef_tryOffsetFrom dest src

    -- `count` must not exceed isize::MAX, else the overlap check
    -- will misbehave.
    let sizeBits = fromIntegral $ C.intValue (C.knownNat @SizeBits)
    let maxCount = R.App $ usizeLit (1 `shift` (sizeBits - 1))
    let countOk = R.App $ usizeLt count maxCount
    G.assertExpr countOk $ S.litExpr "count overflow in copy_nonoverlapping"

    -- If `maybeOffset` is Nothing, then src and dest definitely
    -- don't overlap, since they come from different allocations.
    -- If it's Just, the value must be >= count or <= -count to put
    -- the two regions far enough apart.
    let count' = usizeToIsize R.App count
    let destAbove = \offset -> R.App $ isizeLe count' offset
    let destBelow = \offset -> R.App $ isizeLe offset (R.App $ isizeNeg count')
    offsetOk <- G.caseMaybe maybeOffset C.BoolRepr $ G.MatchMaybe
        (\offset -> return $ R.App $ E.Or (destAbove offset) (destBelow offset))
        (return $ R.App $ E.BoolLit True)
    G.assertExpr offsetOk $ S.litExpr "src and dest overlap in copy_nonoverlapping"

    ptrCopy tpr src dest count
    return $ MirExp C.UnitRepr $ R.App E.EmptyApp

--  LocalWords:  params IndexMut FnOnce Fn IntoIterator iter impl
--  LocalWords:  tovec fromelem tmethsubst MirExp initializer callExp
--  LocalWords:  mkTraitObject mkCustomTraitObject TyClosure
--  LocalWords:  transTerminator transStatement

------------------------------------------------------------------------------------------------

-- | Define a CFG for a function, and check that there are no auxiliary
-- functions generated alongside it. This is a common pattern used throughout
-- this module.
defineFunctionNoAuxs ::
  FH.FnHandle init ret {- ^ Handle for the generated function -} ->
  G.FunctionDef MIR t init ret (ST s) {- ^ Generator action and initial state -} ->
  ST s (R.SomeCFG MIR init ret)
defineFunctionNoAuxs handle def = do
  ng <- newSTNonceGenerator
  (mainCFG, auxCFGs) <- G.defineFunction PL.InternalPos ng handle def
  unless (null auxCFGs) $
    error $ "defineFunctionNoAuxs: Expected no auxiliary functions, received "
         ++ show (length auxCFGs)
  pure mainCFG
