
-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Expr
-- Description      : Translation-time LLVM expressions
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

module Lang.Crucible.LLVM.Translation.Expr
  ( LLVMExpr(..)
  , ScalarView(..)
  , asScalar
  , asVectorWithType
  , asVector

  , pattern PointerExpr
  , pattern BitvectorAsPointerExpr
  , pointerAsBitvectorExpr

  , unpackOne
  , unpackVec
  , unpackArgs
  , zeroExpand
  , undefExpand
  , explodeVector

  , constToLLVMVal
  , transValue
  , transTypedValue
  , transTypeAndValue
  , liftConstant

  , callIsNull
  , callIntToBool
  , callAlloca
  , callPushFrame
  , callPopFrame
  , callPtrAddOffset
  , callPtrSubtract
  , callLoad
  , callStore
  ) where

import Control.Lens hiding ((:>))
import Control.Monad
import Control.Monad.Except
import qualified Data.ByteString as BS
import Data.Foldable (toList)
import qualified Data.List as List
--import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.String
import qualified Data.Vector as V
import Numeric.Natural
import GHC.Exts ( Proxy#, proxy# )

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>) )
import           Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some
import           Data.Text (Text)

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.Extension ()

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

import           What4.InterpretedFloatingPoint (X86_80Val(..))

-------------------------------------------------------------------------
-- LLVMExpr
--
-- As noted in "Lang.Crucible.LLVM.Translation.Types", this code uses
-- a polymorphic continuation-passing style to convert to
-- strongly-typed Crucible types from less-strongly-typed LLVM
-- types. As part of that, the LLVM architecture (notably the pointer
-- width) must be unified between the outer context and the
-- continuation; the 'proxy#' arguments here and below represent a
-- 'Proxy# arch' type that is used to maintain that architecture
-- definition and corresponding pointer width for the conversions.

-- | An intermediate form of LLVM expressions that retains some structure
--   that would otherwise be more difficult to retain if we translated directly
--   into crucible expressions.
data LLVMExpr s (arch :: LLVMArch) where
   BaseExpr   :: TypeRepr tp -> Expr LLVM s tp -> LLVMExpr s arch
   ZeroExpr   :: MemType -> LLVMExpr s arch
   UndefExpr  :: MemType -> LLVMExpr s arch
   VecExpr    :: MemType -> Seq (LLVMExpr s arch) -> LLVMExpr s arch
   StructExpr :: Seq (MemType, LLVMExpr s arch) -> LLVMExpr s arch

instance Show (LLVMExpr s arch) where
  show (BaseExpr ty x)  = C.showF x ++ " : " ++ show ty
  show (ZeroExpr mt)    = "<zero :" ++ show mt ++ ">"
  show (UndefExpr mt)   = "<undef :" ++ show mt ++ ">"
  show (VecExpr _mt xs) = "[" ++ List.intercalate ", " (map show (toList xs)) ++ "]"
  show (StructExpr xs)  = "{" ++ List.intercalate ", " (map f (toList xs)) ++ "}"
    where f (_mt,x) = show x


data ScalarView s (arch :: LLVMArch) where
  Scalar    :: Proxy# arch -> TypeRepr tp -> Expr LLVM s tp -> ScalarView s arch
  NotScalar :: ScalarView s arch

-- | Examine an LLVM expression and return the corresponding
--   crucible expression, if it is a scalar.
asScalar :: (?lc :: TypeContext, HasPtrWidth (ArchWidth arch))
         => LLVMExpr s arch
         -> ScalarView s arch
asScalar (BaseExpr tp xs)
  = Scalar proxy# tp xs
asScalar (ZeroExpr llvmtp)
  = let ?err = error
     in zeroExpand proxy# llvmtp $ \archProxy tpr ex -> Scalar archProxy tpr ex
asScalar (UndefExpr llvmtp)
  = let ?err = error
     in undefExpand proxy# llvmtp $ \archProxy tpr ex -> Scalar archProxy tpr ex
asScalar _ = NotScalar

-- | Turn the expression into an explicit vector.
asVectorWithType :: LLVMExpr s arch -> Maybe (MemType, Seq (LLVMExpr s arch))
asVectorWithType v =
  case v of
    ZeroExpr (VecType n t)  -> Just (t, Seq.replicate (fromIntegral n) (ZeroExpr t))
    UndefExpr (VecType n t) -> Just (t, Seq.replicate (fromIntegral n) (UndefExpr t))
    VecExpr t s             -> Just (t, s)
    _                       -> Nothing

asVector :: LLVMExpr s arch -> Maybe (Seq (LLVMExpr s arch))
asVector = fmap snd . asVectorWithType


nullPointerExpr :: (HasPtrWidth w) => Expr LLVM s (LLVMPointerType w)
nullPointerExpr = PointerExpr PtrWidth (App (NatLit 0)) (App (BVLit PtrWidth (BV.zero PtrWidth)))

pattern PointerExpr
    :: (1 <= w)
    => NatRepr w
    -> Expr LLVM s NatType
    -> Expr LLVM s (BVType w)
    -> Expr LLVM s (LLVMPointerType w)
pattern PointerExpr w blk off = App (ExtensionApp (LLVM_PointerExpr w blk off))

pattern BitvectorAsPointerExpr
    :: (1 <= w)
    => NatRepr w
    -> Expr LLVM s (BVType w)
    -> Expr LLVM s (LLVMPointerType w)
pattern BitvectorAsPointerExpr w ex = PointerExpr w (App (NatLit 0)) ex

pointerAsBitvectorExpr
    :: (1 <= w)
    => NatRepr w
    -> Expr LLVM s (LLVMPointerType w)
    -> LLVMGenerator s arch ret (Expr LLVM s (BVType w))
pointerAsBitvectorExpr _ (BitvectorAsPointerExpr _ ex) =
     return ex
pointerAsBitvectorExpr w ex =
  do ex' <- forceEvaluation ex
     let blk = App (ExtensionApp (LLVM_PointerBlock w ex'))
     let off = App (ExtensionApp (LLVM_PointerOffset w ex'))
     assertExpr (blk .== litExpr 0)
                (litExpr "Expected bitvector, but found pointer")
     return off



-- | Given a list of LLVMExpressions, "unpack" them into an assignment
--   of crucible expressions.
unpackArgs :: forall s a arch
    . (?lc :: TypeContext
      ,?err :: String -> a
      ,HasPtrWidth (ArchWidth arch)
      )
   => [LLVMExpr s arch]
   -> (forall ctx. Proxy# arch -> CtxRepr ctx -> Ctx.Assignment (Expr LLVM s) ctx -> a)
   -> a
unpackArgs = go Ctx.Empty Ctx.Empty
 where go :: CtxRepr ctx
          -> Ctx.Assignment (Expr LLVM s) ctx
          -> [LLVMExpr s arch]
          -> (forall ctx'. Proxy# arch -> CtxRepr ctx' -> Ctx.Assignment (Expr LLVM s) ctx' -> a)
          -> a
       go ctx asgn [] k = k proxy# ctx asgn
       go ctx asgn (v:vs) k = unpackOne v (\_ tyr ex -> go (ctx :> tyr) (asgn :> ex) vs k)

unpackOne
   :: (?lc :: TypeContext, ?err :: String -> a, HasPtrWidth (ArchWidth arch))
   => LLVMExpr s arch
   -> (forall tpr. Proxy# arch -> TypeRepr tpr -> Expr LLVM s tpr -> a)
   -> a
unpackOne (BaseExpr tyr ex) k = k proxy# tyr ex
unpackOne (UndefExpr tp) k = undefExpand proxy# tp k
unpackOne (ZeroExpr tp) k = zeroExpand proxy# tp k
unpackOne (StructExpr vs) k =
  unpackArgs (map snd $ toList vs) $ \archProxy struct_ctx struct_asgn ->
      k archProxy (StructRepr struct_ctx) (mkStruct struct_ctx struct_asgn)
unpackOne (VecExpr tp vs) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec proxy# tpr (toList vs) $ k proxy# (VectorRepr tpr)

unpackVec :: forall tpr s arch a
    . (?lc :: TypeContext, ?err :: String -> a
      , HasPtrWidth (ArchWidth arch)
      )
   => Proxy# arch
   -> TypeRepr tpr
   -> [LLVMExpr s arch]
   -> (Expr LLVM s (VectorType tpr) -> a)
   -> a
unpackVec _archProxy tpr = go [] . reverse
  where go :: [Expr LLVM s tpr] -> [LLVMExpr s arch] -> (Expr LLVM s (VectorType tpr) -> a) -> a
        go vs [] k = k (vectorLit tpr $ V.fromList vs)
        go vs (x:xs) k = unpackOne x $ \_archProxy' tpr' v ->
                           case testEquality tpr tpr' of
                             Just Refl -> go (v:vs) xs k
                             Nothing -> ?err $ unwords ["type mismatch in array value", show tpr, show tpr']

zeroExpand :: (?lc :: TypeContext, ?err :: String -> a, HasPtrWidth (ArchWidth arch))
           => Proxy# arch
           -> MemType
           -> (forall tp. Proxy# arch -> TypeRepr tp -> Expr LLVM s tp -> a)
           -> a
zeroExpand _proxyArch (IntType w) k =
  case mkNatRepr w of
    Some w' | Just LeqProof <- isPosNat w' ->
      k proxy# (LLVMPointerRepr w') $
         BitvectorAsPointerExpr w' $
         App $ BVLit w' (BV.zero w')

    _ -> ?err $ unwords ["illegal integer size", show w]

zeroExpand _proxyArch (StructType si) k =
   unpackArgs (map ZeroExpr tps) $ \archProxy ctx asgn -> k archProxy (StructRepr ctx) (mkStruct ctx asgn)
 where tps = map fiType $ toList $ siFields si
zeroExpand proxyArch (ArrayType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec proxyArch tpr (replicate (fromIntegral n) (ZeroExpr tp)) $ k proxyArch (VectorRepr tpr)
zeroExpand proxyArch (VecType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec proxyArch tpr (replicate (fromIntegral n) (ZeroExpr tp)) $ k proxyArch (VectorRepr tpr)
zeroExpand proxyArch (PtrType _tp) k = k proxyArch PtrRepr nullPointerExpr
zeroExpand proxyArch FloatType   k  = k proxyArch (FloatRepr SingleFloatRepr) (App (FloatLit 0))
zeroExpand proxyArch DoubleType  k  = k proxyArch (FloatRepr DoubleFloatRepr) (App (DoubleLit 0))
zeroExpand _prxyArch X86_FP80Type _ = ?err "Cannot zero expand x86_fp80 values"
zeroExpand _prxyArch MetadataType _ = ?err "Cannot zero expand metadata"

undefExpand :: (?lc :: TypeContext, ?err :: String -> a
               , HasPtrWidth (ArchWidth arch)
               )
            => Proxy# arch
            -> MemType
            -> (forall tp. Proxy# arch -> TypeRepr tp -> Expr LLVM s tp -> a)
            -> a
undefExpand _archProxy (IntType w) k =
  case mkNatRepr w of
    Some w' | Just LeqProof <- isPosNat w' ->
      k proxy# (LLVMPointerRepr w') $
         BitvectorAsPointerExpr w' $
         App $ BVUndef w'

    _ -> ?err $ unwords ["illegal integer size", show w]
undefExpand _archProxy (PtrType _tp) k =
   k proxy# PtrRepr $ BitvectorAsPointerExpr PtrWidth $ App $ BVUndef PtrWidth
undefExpand _archProxy (StructType si) k =
   unpackArgs (map UndefExpr tps) $ \archProxy ctx asgn -> k archProxy (StructRepr ctx) (mkStruct ctx asgn)
 where tps = map fiType $ toList $ siFields si
undefExpand archProxy (ArrayType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec archProxy tpr (replicate (fromIntegral n) (UndefExpr tp)) $ k proxy# (VectorRepr tpr)
undefExpand archProxy (VecType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec archProxy tpr (replicate (fromIntegral n) (UndefExpr tp)) $ k proxy# (VectorRepr tpr)
undefExpand _archProxy FloatType k =
  k proxy# (FloatRepr SingleFloatRepr) (App (FloatUndef SingleFloatRepr))
undefExpand _archProxy DoubleType k =
  k proxy# (FloatRepr DoubleFloatRepr) (App (FloatUndef DoubleFloatRepr))
undefExpand _archProxy X86_FP80Type k =
  k proxy# (FloatRepr X86_80FloatRepr) (App (FloatUndef X86_80FloatRepr))
undefExpand _archPrxy tp _ = ?err $ unwords ["cannot undef expand type:", show tp]


explodeVector :: Natural -> LLVMExpr s arch -> Maybe (Seq (LLVMExpr s arch))
explodeVector n (UndefExpr (VecType n' tp)) | n == n' = return (Seq.replicate (fromIntegral n) (UndefExpr tp))
explodeVector n (ZeroExpr (VecType n' tp)) | n == n' = return (Seq.replicate (fromIntegral n) (ZeroExpr tp))
explodeVector n (VecExpr _tp xs)
  | n == fromIntegral (length xs) = return xs
explodeVector n (BaseExpr (VectorRepr tpr) v) =
    let xs = [ BaseExpr tpr (app $ VectorGetEntry tpr v (litExpr i)) | i <- [0..n-1] ]
     in return (Seq.fromList xs)
explodeVector _ _ = Nothing


---------------------------------------------------------------------------
-- Translations

liftConstant ::
  HasPtrWidth (ArchWidth arch) =>
  LLVMConst ->
  LLVMGenerator s arch ret (LLVMExpr s arch)
liftConstant c = case c of
  ZeroConst mt ->
    return $ ZeroExpr mt
  UndefConst mt ->
    return $ UndefExpr mt
  IntConst w i ->
    return $ BaseExpr (LLVMPointerRepr w) (BitvectorAsPointerExpr w (App (BVLit w i)))
  FloatConst f ->
    return $ BaseExpr (FloatRepr SingleFloatRepr) (App (FloatLit f))
  DoubleConst d ->
    return $ BaseExpr (FloatRepr DoubleFloatRepr) (App (DoubleLit d))
  LongDoubleConst (L.FP80_LongDouble ex man) ->
    return $ BaseExpr (FloatRepr X86_80FloatRepr) (App (X86_80Lit (X86_80Val ex man)))
  StringConst bs ->
    -- TODO? Should we have a StringExpr? It seems like this case doesn't
    --  actually ever arise...
    do vs <- mapM (\b -> liftConstant (IntConst knownNat (BV.word8 b))) (BS.unpack bs)
       return (VecExpr i8 $ Seq.fromList vs)
  ArrayConst mt vs ->
    do vs' <- mapM (\c' -> liftConstant c') vs
       return (VecExpr mt $ Seq.fromList vs')
  VectorConst mt vs ->
    do vs' <- mapM (\c' -> liftConstant c') vs
       return (VecExpr mt $ Seq.fromList vs')
  StructConst si vs ->
    do vs' <- mapM (\c' -> liftConstant c') vs
       let ts = map fiType $ V.toList (siFields si)
       unless (length vs' == length ts)
              (fail "Type mismatch in structure constant")
       return (StructExpr (Seq.fromList (zip ts vs')))
  SymbolConst sym 0 ->
    do memVar <- getMemVar
       base <- extensionStmt (LLVM_ResolveGlobal ?ptrWidth memVar (GlobalSymbol sym))
       return (BaseExpr PtrRepr base)
  SymbolConst sym off ->
    do memVar <- getMemVar
       base <- extensionStmt (LLVM_ResolveGlobal ?ptrWidth memVar (GlobalSymbol sym))
       let off' = app $ BVLit ?ptrWidth (BV.mkBV ?ptrWidth off)
       ptr  <- extensionStmt (LLVM_PtrAddOffset ?ptrWidth memVar base off')
       return (BaseExpr PtrRepr ptr)

transTypeAndValue ::
  L.Typed L.Value ->
  LLVMGenerator s arch ret (MemType, LLVMExpr s arch)
transTypeAndValue v =
 do let err msg =
         malformedLLVMModule
           "Invalid value type"
           [ fromString msg ]
    tp <- either err return $ liftMemType $ L.typedType v
    (\ex -> (tp, ex)) <$> transValue tp (L.typedValue v)

transTypedValue ::
  L.Typed L.Value ->
  LLVMGenerator s arch ret (LLVMExpr s arch)
transTypedValue v = snd <$> transTypeAndValue v

-- | Translate an LLVM Value into an expression.
transValue :: forall s arch ret.
              MemType
           -> L.Value
           -> LLVMGenerator s arch ret (LLVMExpr s arch)

transValue ty L.ValUndef =
  return $ UndefExpr ty

transValue ty L.ValZeroInit =
  return $ ZeroExpr ty

transValue ty@(PtrType _) L.ValNull =
  return $ ZeroExpr ty

transValue ty@(PtrType _) (L.ValInteger 0) =
  return $ ZeroExpr ty

transValue ty@(PtrType _) v@(L.ValInteger _) =
  reportError $ fromString $ unwords ["Attempted to use integer ", show v, " as pointer: ", show ty]

transValue ty@(IntType _) L.ValNull =
  return $ ZeroExpr ty

transValue _ (L.ValString str) = do
  let eight = knownNat :: NatRepr 8
  let bv8   = LLVMPointerRepr eight
  let chars = V.fromList $ map (BitvectorAsPointerExpr eight . App . BVLit eight . BV.mkBV eight . toInteger . fromEnum) $ str
  return $ BaseExpr (VectorRepr bv8) (App $ VectorLit bv8 $ chars)

transValue _ (L.ValIdent i) = do
  m <- use identMap
  case Map.lookup i m of
    Nothing -> do
      reportError $ fromString $ "Could not find identifier " ++ show i ++ "."
    Just (Left (Some r)) -> do
      e <- readReg r
      return $ BaseExpr (typeOfReg r) e
    Just (Right (Some a)) -> do
      return $ BaseExpr (typeOfAtom a) (AtomExpr a)

transValue (IntType n) (L.ValInteger i) =
  runExceptT (intConst n i) >>= \case
    Left err -> fail err
    Right c  -> liftConstant c

transValue (IntType 1) (L.ValBool b) =
  liftConstant (boolConst b)

transValue FloatType (L.ValFloat f) =
  liftConstant (FloatConst f)

transValue DoubleType (L.ValDouble d) =
  liftConstant (DoubleConst d)

transValue (StructType _) (L.ValStruct vs) = do
     vs' <- mapM (\v -> transTypeAndValue v) vs
     return (StructExpr $ Seq.fromList $ vs')

transValue (StructType _) (L.ValPackedStruct vs) =  do
     vs' <- mapM (\v -> transTypeAndValue v) vs
     return (StructExpr $ Seq.fromList $ vs')

transValue (ArrayType _ tp) (L.ValArray _ vs) = do
     vs' <- mapM (\v -> transValue tp v) vs
     return (VecExpr tp $ Seq.fromList vs')

transValue (VecType _ tp) (L.ValVector _ vs) = do
     vs' <- mapM (\v -> transValue tp v) vs
     return (VecExpr tp $ Seq.fromList vs')

transValue _ (L.ValSymbol symbol) = do
     liftConstant (SymbolConst symbol 0)

transValue _ (L.ValConstExpr cexp) =
  do res <- runExceptT (transConstantExpr cexp)
     case res of
       Left err -> reportError $ fromString $ unlines ["Error translating constant", err]
       Right cv -> liftConstant cv

transValue ty v =
  reportError $ fromString $ unwords ["unsupported LLVM value:", show v, "of type", show ty]


callIsNull
   :: (1 <= w)
   => NatRepr w
   -> Expr LLVM s (LLVMPointerType w)
   -> LLVMGenerator s arch ret (Expr LLVM s BoolType)
callIsNull w ex = App . Not <$> callIntToBool w ex

callIntToBool
  :: (1 <= w)
  => NatRepr w
  -> Expr LLVM s (LLVMPointerType w)
  -> LLVMGenerator s arch ret (Expr LLVM s BoolType)
callIntToBool w (BitvectorAsPointerExpr _ bv) =
  case bv of
    App (BVLit _ i) -> if i == BV.zero w then return false else return true
    _ -> return (App (BVNonzero w bv))
callIntToBool w ex =
  do ex' <- forceEvaluation ex
     let blk = App (ExtensionApp (LLVM_PointerBlock w ex'))
     let off = App (ExtensionApp (LLVM_PointerOffset w ex'))
     return (blk ./= litExpr 0 .|| (App (BVNonzero w off)))

callAlloca
   :: wptr ~ ArchWidth arch
   => Expr LLVM s (BVType wptr)
   -> Alignment
   -> LLVMGenerator s arch ret (Expr LLVM s (LLVMPointerType wptr))
callAlloca sz alignment = do
   memVar <- getMemVar
   loc <- show <$> getPosition
   extensionStmt (LLVM_Alloca ?ptrWidth memVar sz alignment loc)

callPushFrame :: Text -> LLVMGenerator s arch ret ()
callPushFrame nm = do
   memVar <- getMemVar
   void $ extensionStmt (LLVM_PushFrame nm memVar)

callPopFrame :: LLVMGenerator s arch ret ()
callPopFrame = do
   memVar <- getMemVar
   void $ extensionStmt (LLVM_PopFrame memVar)

callPtrAddOffset ::
       wptr ~ ArchWidth arch
    => Expr LLVM s (LLVMPointerType wptr)
    -> Expr LLVM s (BVType wptr)
    -> LLVMGenerator s arch ret (Expr LLVM s (LLVMPointerType wptr))
callPtrAddOffset base off = do
    memVar <- getMemVar
    extensionStmt (LLVM_PtrAddOffset ?ptrWidth memVar base off)

callPtrSubtract ::
       wptr ~ ArchWidth arch
    => Expr LLVM s (LLVMPointerType wptr)
    -> Expr LLVM s (LLVMPointerType wptr)
    -> LLVMGenerator s arch ret (Expr LLVM s (BVType wptr))
callPtrSubtract x y = do
    memVar <- getMemVar
    extensionStmt (LLVM_PtrSubtract ?ptrWidth memVar x y)

callLoad :: MemType
         -> TypeRepr tp
         -> LLVMExpr s arch
         -> Alignment
         -> LLVMGenerator s arch ret (LLVMExpr s arch)
callLoad typ expectTy (asScalar -> Scalar _ PtrRepr ptr) align =
   do memVar <- getMemVar
      typ' <- toStorableType typ
      v <- extensionStmt (LLVM_Load memVar ptr expectTy typ' align)
      return (BaseExpr expectTy v)
callLoad _ _ _ _ =
  fail $ unwords ["Unexpected argument type in callLoad"]

callStore :: MemType
          -> LLVMExpr s arch
          -> LLVMExpr s arch
          -> Alignment
          -> LLVMGenerator s arch ret ()
callStore typ (asScalar -> Scalar _ PtrRepr ptr) (ZeroExpr _mt) _align =
 do memVar <- getMemVar
    typ'   <- toStorableType typ
    void $ extensionStmt (LLVM_MemClear memVar ptr (storageTypeSize typ'))

callStore typ (asScalar -> Scalar _ PtrRepr ptr) v align =
 do let ?err = fail
    unpackOne v $ \_ vtpr vexpr -> do
      memVar <- getMemVar
      typ' <- toStorableType typ
      void $ extensionStmt (LLVM_Store memVar ptr vtpr typ' align vexpr)

callStore _ _ _ _ =
  fail $ unwords ["Unexpected argument type in callStore"]
