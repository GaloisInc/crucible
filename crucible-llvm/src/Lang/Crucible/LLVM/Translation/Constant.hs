-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Constant
-- Description      : LLVM constant expression evaluation and GEPs
-- Copyright        : (c) Galois, Inc 2014-2015
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides translation-time evaluation of constant
-- expressions.  It also provides an intermediate representation
-- for GEP (getelementpointer) instructions that makes more explicit
-- the places where vectorization may occur, as well as resolving type
-- sizes and field offsets.
-----------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Translation.Constant
  ( -- * Representation of LLVM constant values
    LLVMConst(..)
  , boolConst
  , intConst

    -- * Translations from LLVM syntax to constant values
  , transConstant
  , transConstant'
  , transConstantExpr

    -- * Intermediate representation for GEP
  , GEP(..)
  , GEPResult(..)
  , translateGEP

    -- * Utility functions
  , showInstr
  ) where

import           Control.Monad
import           Control.Monad.Fail hiding (fail)
import           Data.Bits
import           Data.Traversable
import           Data.Fixed (mod')
import qualified Data.Vector as V
import           Numeric.Natural
import           GHC.TypeLits

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import           Lang.Crucible.LLVM.Bytes
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation.Types

-- | Pretty print an LLVM instruction
showInstr :: L.Instr -> String
showInstr i = show (L.ppLLVM38 (L.ppInstr i))

-- | Intermediate representation of a GEP.  
--   A @GEP n expr@ is a representation of a GEP with
--   @n@ parallel vector lanes with expressions represented
--   by @expr@ values.
data GEP (n :: Nat) (expr :: *) where
  -- | Start a GEP with a single base pointer
  GEP_scalar_base  :: expr -> GEP 1 expr

  -- | Start a GEP with a vector of base pointers
  GEP_vector_base  :: NatRepr n -> expr -> GEP n expr

  -- | Copy a scalar base vector pointwise into a
  --   vector of length n.
  GEP_scatter      :: NatRepr n -> GEP 1 expr -> GEP n expr

  -- | Add the offset corresponding to the given field
  --   pointwise to each pointer
  GEP_field        :: FieldInfo -> GEP n expr -> GEP n expr

  -- | Add an offset corresponding to indexing n*size
  --   bytes pointwise to each pointer
  GEP_index_each   :: MemType -> GEP n expr -> expr -> GEP n expr

  -- | Given a vector of offsets (whose length must match
  --   the vector of pointers), multiply each one by the
  --   type size, and add the offsets to the corresponding
  --   pointers.
  GEP_index_vector :: MemType -> GEP n expr -> expr -> GEP n expr


instance Functor (GEP n) where
  fmap = fmapDefault

instance Foldable (GEP n) where
  foldMap = foldMapDefault

instance Traversable (GEP n) where
  traverse f gep = case gep of
    GEP_scalar_base x      -> GEP_scalar_base <$> f x
    GEP_vector_base n x    -> GEP_vector_base n <$> f x
    GEP_scatter n gep'        -> GEP_scatter n <$> traverse f gep'
    GEP_field fi gep'       -> GEP_field fi <$> traverse f gep'
    GEP_index_each mt gep' idx   -> GEP_index_each mt <$> traverse f gep' <*> f idx
    GEP_index_vector mt gep' idx -> GEP_index_vector mt <$> traverse f gep' <*> f idx

-- | The result of a GEP instruction translation.  It records the number
--   of parallel vector lanes in the resulting instruction, the resulting
--   memory type of the instruction, and the sequence of sub-operations
--   required to compute the GEP instruction.
data GEPResult expr where
  GEPResult :: (1 <= n) => NatRepr n -> MemType -> GEP n expr -> GEPResult expr

instance Functor GEPResult where
  fmap = fmapDefault

instance Foldable GEPResult where
  foldMap = foldMapDefault

instance Traversable GEPResult where
  traverse f (GEPResult n mt gep) = GEPResult n mt <$> traverse f gep


-- | Given the data for an LLVM getelementpointer instruction,
--   preprocess the instruction into a @GEPResult@, checking
--   types, computing vectorization lanes, etc.
translateGEP :: forall wptr m.
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  Bool ->
  L.Typed L.Value ->
  [L.Typed L.Value] ->
  m (GEPResult (L.Typed L.Value))
translateGEP _ _ [] =
  fail "getelementpointer must have at least one index"

translateGEP inbounds base elts =
  do mt <- liftMemType (L.typedType base)
     case mt of
       VecType n (PtrType baseSymType)
         | Just baseMemType <- TyCtx.asMemType baseSymType
         , Just (Some lanes) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat lanes
         ->  let mt' = ArrayType 0 baseMemType in
             go lanes mt' (GEP_vector_base lanes base) elts
       PtrType baseSymType
         | Just baseMemType <- TyCtx.asMemType baseSymType
         ->  let mt' = ArrayType 0 baseMemType in
             go (knownNat @1) mt' (GEP_scalar_base base) elts
       _ -> badGEP
 where
 badGEP :: m a
 badGEP = fail $ unlines [ "Invalid GEP", showInstr (L.GEP inbounds base elts) ]

 go ::
   (1 <= lanes) =>
   NatRepr lanes ->
   MemType ->
   GEP lanes (L.Typed L.Value) ->
   [L.Typed L.Value] ->
   m (GEPResult (L.Typed L.Value))

 go lanes mt gep [] = return (GEPResult lanes mt gep)

 go lanes mt gep (off:xs) =
   do offt <- liftMemType (L.typedType off)
      case mt of
        ArrayType _ mt' ->
          case offt of
            IntType _
              -> go lanes mt' (GEP_index_each mt' gep off) xs
            VecType n (IntType _)
              | natValue lanes == toInteger n
              -> go lanes mt' (GEP_index_vector mt' gep off) xs
            VecType n (IntType _)
              | Just (Some n') <- someNat (toInteger n)
              , Just LeqProof <- isPosNat n'
              , Just Refl <- testEquality lanes (knownNat @1)
              -> go n' mt' (GEP_index_vector mt' (GEP_scatter n' gep) off) xs

            _ -> badGEP

        StructType si ->
          do off' <- transConstant' offt (L.typedValue off)
             case off' of
               ZeroConst (IntType _) -> goidx 0
               IntConst _ idx -> goidx idx
               VectorConst (IntType _) (i@(IntConst _ idx) : is) | all (same i) is -> goidx idx
                 where
                 same :: LLVMConst -> LLVMConst -> Bool
                 same (IntConst wx x) (IntConst wy y)
                   | Just Refl <- testEquality wx wy = x == y
                 same _ _ = False

               _ -> badGEP

            where goidx idx | 0 <= idx && idx < toInteger (V.length flds) =
                       go lanes mt' (GEP_field fi gep) xs
                     where idx' = fromInteger idx
                           flds = siFields si
                           fi   = flds V.! idx'
                           mt'  = fiType fi

                  goidx _ = badGEP

        _ -> badGEP


-- | Translation-time LLVM constant values.
data LLVMConst where
  ZeroConst     :: !MemType -> LLVMConst
  IntConst      :: (1 <= w) => !(NatRepr w) -> !Integer -> LLVMConst
  FloatConst    :: !Float -> LLVMConst
  DoubleConst   :: !Double -> LLVMConst
  ArrayConst    :: !MemType -> [LLVMConst] -> LLVMConst
  VectorConst   :: !MemType -> [LLVMConst] -> LLVMConst
  StructConst   :: !StructInfo -> [LLVMConst] -> LLVMConst
  SymbolConst   :: !L.Symbol -> !Integer -> LLVMConst
  PtrToIntConst :: !LLVMConst -> LLVMConst

-- | Create an LLVM constant value from a boolean.
boolConst :: Bool -> LLVMConst
boolConst False = IntConst (knownNat @1) 0
boolConst True = IntConst (knownNat @1) 1

-- | Create an LLVM contant of a given width.
intConst ::
  MonadFail m =>
  Natural {- ^ width of the integer constant -} ->
  Integer {- ^ value of the integer constant -} ->
  m LLVMConst
intConst n x
  | Just (Some w) <- someNat (fromIntegral n)
  , Just LeqProof <- isPosNat w
  = return (IntConst w (toUnsigned w x))
intConst n _
  = fail ("Invalid integer width: " ++ show n)

-- | Compute the constant value of an expression.  Fail if the
--   given value does not represent a constant.
transConstant ::
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  L.Typed L.Value ->
  m LLVMConst
transConstant (L.Typed tp v) =
  do mt <- liftMemType tp
     transConstant' mt v

-- | Compute the constant value of an expression.  Fail if the
--   given value does not represent a constant.
transConstant' ::
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  MemType ->
  L.Value ->
  m LLVMConst
transConstant' _tp (L.ValUndef) =
  fail "Undefined constant value"
transConstant' (IntType n) (L.ValInteger x) =
  intConst n x
transConstant' (IntType 1) (L.ValBool b) =
  return . IntConst (knownNat @1) $ if b then 1 else 0
transConstant' FloatType (L.ValFloat f) =
  return (FloatConst f)
transConstant' DoubleType (L.ValDouble d) =
  return (DoubleConst d)
transConstant' (PtrType _) (L.ValSymbol s) =
  return (SymbolConst s 0)
transConstant' tp L.ValZeroInit =
  return (ZeroConst tp)
transConstant' (PtrType stp) L.ValNull =
  return (ZeroConst (PtrType stp))
transConstant' (VecType n tp) (L.ValVector _tp xs) | n == length xs =
  VectorConst tp <$> traverse (transConstant' tp) xs
transConstant' (ArrayType n tp) (L.ValArray _tp xs) | n == length xs =
  ArrayConst tp <$> traverse (transConstant' tp) xs
transConstant' (StructType si) (L.ValStruct xs) | not (siIsPacked si) =
  StructConst si <$> traverse transConstant xs
transConstant' (StructType si) (L.ValPackedStruct xs) | siIsPacked si =
  StructConst si <$> traverse transConstant xs

transConstant' tp (L.ValConstExpr cexpr) = transConstantExpr tp cexpr

transConstant' tp val =
  fail $ unlines ["Cannot compute constant value for expression of type " ++ show tp
                 , show val
                 ]


-- | Evaluate a GEP instruction to a constant value.
evalConstGEP :: forall m wptr.
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  GEPResult LLVMConst ->
  m LLVMConst
evalConstGEP (GEPResult lanes finalMemType gep0) =
   do xs <- go gep0
      unless (toInteger (length xs) == natValue lanes)
             (fail "Unexpected vector length in result of constant GEP")
      case xs of
        [x] -> return x
        _   -> return (VectorConst (PtrType (MemType finalMemType)) xs)

  where
  dl = TyCtx.llvmDataLayout ?lc

  asOffset :: MemType -> LLVMConst -> m Integer
  asOffset _ (ZeroConst (IntType _)) = return 0
  asOffset mt (IntConst _ x) =
    do let x' = x * (bytesToInteger (memTypeSize dl mt))
       unless (x' <= maxUnsigned ?ptrWidth)
              (fail "Computed offset overflow in constant GEP")
       return x'
  asOffset _ _ =
    fail "Expected offset value in constant GEP"

  addOffset :: Integer -> LLVMConst -> m LLVMConst
  addOffset x (SymbolConst sym off) = return (SymbolConst sym (off+x))
  addOffset _ _ = fail "Expected symbol constant in constant GEP"

  go :: GEP n LLVMConst -> m [LLVMConst]
  go (GEP_scalar_base base)
    = return [base]

  go (GEP_vector_base n x)
    = asVectorOf (fromInteger (natValue n)) return x

  go (GEP_scatter n gep)
    = do ps <- go gep
         case ps of
           [p] -> return (replicate (fromInteger (natValue n)) p)
           _   -> fail "vector length mismatch in GEP scatter"

  go (GEP_field fi gep)
    = do ps <- go gep
         let i = bytesToInteger (fiOffset fi)
         traverse (addOffset i) ps

  go (GEP_index_each mt gep x)
    = do ps <- go gep
         i  <- asOffset mt x
         traverse (addOffset i) ps

  go (GEP_index_vector mt gep x)
    = do ps <- go gep
         is <- asVectorOf (length ps) (asOffset mt) x
         zipWithM addOffset is ps

evalFcmp ::
  RealFloat a =>
  L.FCmpOp ->
  a -> a -> LLVMConst
evalFcmp op x y = boolConst $ case op of
  L.Ffalse -> False
  L.Ftrue  -> True
  L.Foeq   -> ordered && x == y
  L.Fone   -> ordered && x /= y
  L.Fogt   -> ordered && x >  y
  L.Foge   -> ordered && x >= y
  L.Folt   -> ordered && x <  y
  L.Fole   -> ordered && x <= y
  L.Ford   -> ordered
  L.Fueq   -> unordered || x == y
  L.Fune   -> unordered || x /= y
  L.Fugt   -> unordered || x >  y
  L.Fuge   -> unordered || x >= y
  L.Fult   -> unordered || x <  y
  L.Fule   -> unordered || x <= y
  L.Funo   -> unordered
 where
 unordered = isNaN x || isNaN y
 ordered   = not unordered

evalIcmp ::
  (1 <= w) =>
  L.ICmpOp ->
  NatRepr w ->
  Integer -> Integer -> LLVMConst
evalIcmp op w x y = boolConst $ case op of
  L.Ieq  -> ux == uy
  L.Ine  -> ux /= uy
  L.Iugt -> ux >  uy
  L.Iuge -> ux >= uy
  L.Iult -> ux <  uy
  L.Iule -> ux <= uy
  L.Isgt -> sx >  sy
  L.Isge -> sx >= sy
  L.Islt -> sx <  sy
  L.Isle -> sx <= sy

 where
 ux = toUnsigned w x
 uy = toUnsigned w y
 sx = toSigned w x
 sy = toSigned w y

evalArith ::
  (MonadFail m, HasPtrWidth wptr) =>
  L.ArithOp ->
  MemType ->
  Arith -> Arith -> m LLVMConst
evalArith op (IntType m) (ArithI x) (ArithI y)
  | Just (Some w) <- someNat (toInteger m)
  , Just LeqProof <- isPosNat w
  = evalIarith op w x y
evalArith op FloatType (ArithF x) (ArithF y) = FloatConst <$> evalFarith op x y
evalArith op DoubleType (ArithD x) (ArithD y) = DoubleConst <$> evalFarith op x y
evalArith _ _ _ _ = fail "arithmetic arugment mistmatch"

evalFarith ::
  (RealFrac a, MonadFail m) =>
  L.ArithOp ->
  a -> a -> m a
evalFarith op x y =
  case op of
    L.FAdd -> return (x + y)
    L.FSub -> return (x - y)
    L.FMul -> return (x * y)
    L.FDiv -> return (x / y)
    L.FRem -> return (mod' x y)
    _ -> fail "Encountered integer arithmetic operation applied to floating point arguments"

evalIarith ::
  (1 <= w, MonadFail m, HasPtrWidth wptr) =>
  L.ArithOp ->
  NatRepr w ->
  ArithInt -> ArithInt -> m LLVMConst
evalIarith op w (ArithInt x) (ArithInt y)
  = IntConst w <$> evalIarith' op w x y
evalIarith op w (ArithPtr sym x) (ArithInt y)
  | Just Refl <- testEquality w ?ptrWidth
  , L.Add _ _ <- op
  = return $ PtrToIntConst $ SymbolConst sym (x+y)
  | otherwise
  = fail "Illegal operation applied to pointer argument"
evalIarith op w (ArithInt x) (ArithPtr sym y)
  | Just Refl <- testEquality w ?ptrWidth
  , L.Add _ _ <- op
  = return $ PtrToIntConst $ SymbolConst sym (x+y)
  | otherwise
  = fail "Illegal operation applied to pointer argument"
evalIarith op w (ArithPtr symx x) (ArithPtr symy y)
  | Just Refl <- testEquality w ?ptrWidth
  , symx == symy
  , L.Sub _ _ <- op
  = return $ IntConst ?ptrWidth (toUnsigned ?ptrWidth (x - y))
  | otherwise
  = fail "Illegal operation applied to pointer argument"

evalIarith' ::
  (1 <= w, MonadFail m) =>
  L.ArithOp ->
  NatRepr w ->
  Integer -> Integer -> m Integer
evalIarith' op w x y = do
  let nuwTest nuw z =
        when (nuw && toUnsigned w z > maxUnsigned w)
             (fail "Unsigned overflow in constant arithmetic operation")
  let nswTest nsw z =
        when (nsw && (toSigned w z < minSigned w || toSigned w z > maxSigned w))
             (fail "Signed overflow in constant arithmetic operation")
  case op of
    L.Add nuw nsw ->
      do let z = x + y
         nuwTest nuw z
         nswTest nsw z
         return z

    L.Sub nuw nsw ->
      do let z = x - y
         nuwTest nuw z
         nswTest nsw z
         return z

    L.Mul nuw nsw ->
      do let z = x * y
         nuwTest nuw z
         nswTest nsw z
         return z

    L.UDiv exact ->
      do when (y == 0)
              (fail "Division by 0 in constant arithmetic operation")
         let (z,r) = x `quotRem` y
         when (exact && r /= 0)
              (fail "Exact division failed in constant arithmetic operation")
         return z

    L.SDiv exact ->
      do when (y == 0)
              (fail "Division by 0 in constant arithmetic operation")
         let sx = toSigned w x
         let sy = toSigned w y
         when (sx == minSigned w && sy == -1)
              (fail "Signed division overflow in constant arithmetic operation")
         let (z,r) = sx `quotRem` sy
         when (exact && r /= 0 )
              (fail "Exact division failed in constant arithmetic operation")
         return z
    L.URem ->
      do when (y == 0)
              (fail "Division by 0 in constant arithmetic operation")
         let r = x `rem` y
         return r

    L.SRem ->
      do when (y == 0)
              (fail "Division by 0 in constant arithmetic operation")
         let sx = toSigned w x
         let sy = toSigned w y
         when (sx == minSigned w && sy == -1)
              (fail "Signed division overflow in constant arithmetic operation")
         let r = sx `rem` sy
         return r

    _ -> fail "Floating point operation applied to integer arguments"

evalBitwise ::
  (1 <= w, MonadFail m) =>
  L.BitOp ->
  NatRepr w ->
  Integer -> Integer -> m LLVMConst
evalBitwise op w x y = IntConst w <$>
  do let ux = toUnsigned w x
     let uy = toUnsigned w y
     let sx = toSigned w x
     case op of
       L.And -> return (ux .&. uy)
       L.Or  -> return (ux .|. uy)
       L.Xor -> return (ux `xor` uy)
       L.Shl nuw nsw ->
         do let z = ux `shiftL` fromInteger uy
            when (nuw && toUnsigned w z > maxUnsigned w)
                 (fail "Unsigned overflow in left shift")
            when (nsw && toSigned w z > maxUnsigned w)
                 (fail "Signed overflow in left shift")
            return z
       L.Lshr exact ->
         do let z = ux `shiftR` fromInteger uy
            when (exact && ux /= z `shiftL` fromInteger uy)
                 (fail "Exact left shift failed")
            return z
       L.Ashr exact ->
         do let z = sx `shiftR` fromInteger uy
            when (exact && ux /= z `shiftL` fromInteger uy)
                 (fail "Exact left shift failed")
            return (toUnsigned w z)

evalConv ::
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  L.ConstExpr ->
  L.ConvOp ->
  MemType ->
  LLVMConst ->
  m LLVMConst
evalConv expr op mt x = case op of
    L.FpToUi
      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , FloatConst f <- x
      -> return $ IntConst w (truncate f)

      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , DoubleConst d <- x
      -> return $ IntConst w (truncate d)

    L.FpToSi
      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , FloatConst f <- x
      -> return $ IntConst w (truncate f)

      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , DoubleConst d <- x
      -> return $ IntConst w (truncate d)

    L.UiToFp
      | FloatType <- mt
      , IntConst w i <- x
      -> return $ FloatConst (fromInteger (toUnsigned w i))

      | DoubleType <- mt
      , IntConst w i <- x
      -> return $ DoubleConst (fromInteger (toUnsigned w i))

    L.SiToFp
      | FloatType <- mt
      , IntConst w i <- x
      -> return $ FloatConst (fromInteger (toSigned w i))

      | DoubleType <- mt
      , IntConst w i <- x
      -> return $ DoubleConst (fromInteger (toSigned w i))

    L.Trunc
      | IntType n <- mt
      , IntConst w i <- x
      , Just (Some w') <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w'
      , Just LeqProof <- testLeq w' w
      -> return $ IntConst w' (toUnsigned w' i)

    L.ZExt
      | IntType n <- mt
      , IntConst w i <- x
      , Just (Some w') <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w'
      , Just LeqProof <- testLeq w w'
      -> return $ IntConst w' (toUnsigned w' i)

    L.SExt
      | IntType n <- mt
      , IntConst w i <- x
      , Just (Some w') <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w'
      , Just LeqProof <- testLeq w w'
      -> return $ IntConst w' (toSigned w' i)

    L.FpTrunc
      | DoubleType <- mt
      , DoubleConst d <- x
      -> return $ DoubleConst d

      | FloatType <- mt
      , DoubleConst d <- x
      -> return $ FloatConst (realToFrac d)

      | FloatType <- mt
      , FloatConst f <- x
      -> return $ FloatConst f

    L.FpExt
      | DoubleType <- mt
      , DoubleConst d <- x
      -> return $ DoubleConst d

      | DoubleType <- mt
      , FloatConst f <- x
      -> return $ DoubleConst (realToFrac f)

      | FloatType <- mt
      , FloatConst f <- x
      -> return $ FloatConst f

    L.IntToPtr
      | PtrToIntConst p <- x
      -> return p

      | otherwise
      -> badExp "cannot convert arbitrary constant values to pointers"

    L.PtrToInt
      | SymbolConst _ _  <- x
      -> return $ PtrToIntConst x
      | otherwise
      -> badExp "invalid pointer value"

    _ -> badExp "unexpected conversion operation"

 where badExp msg = fail $ unlines [msg, show expr]


evalBitCast ::
  MonadFail m =>
  L.ConstExpr ->  
  MemType ->
  LLVMConst ->
  MemType ->
  m LLVMConst
evalBitCast expr xty x toty =
  case (xty, toty) of
    _ | xty == toty
      -> return x

    (PtrType _, PtrType _)
      -> return x

    (IntType w, VecType n (IntType m))
      | w == (fromIntegral n) * m 
      , Just (Some w') <- someNat (toInteger m)
      , Just LeqProof <- isPosNat w'
      -> do xint <- asInt w x
            -- NB little endian assumption!
            let pieces = [ maxUnsigned w' .&. (xint `shiftR` (i * fromIntegral m))
                         | i <- [0 .. n-1] 
                         ]
            return $ VectorConst (IntType m) (map (IntConst w') pieces) 

    (VecType n (IntType m), IntType w)
      | w == fromIntegral n * m
      , Just (Some w') <- someNat (toInteger w)
      , Just LeqProof <- isPosNat w'
      -> do xs <- asVectorOf n (asInt m) x
            -- NB little endian assumption!
            let pieces = [ v `shiftL` (i * fromIntegral m)
                         | i <- [0 .. n-1]
                         | v <- xs
                         ]
            return $ IntConst w' (foldr (.|.) 0 pieces)

    _ -> badExp "illegal bitcast"
 
 where badExp msg = fail $ unlines [msg, show expr]
 
    

asVectorOf ::
  MonadFail m =>
  Int ->
  (LLVMConst -> m a) ->
  (LLVMConst -> m [a])
asVectorOf n f (ZeroConst (VecType m mt))
  | n == m
  = do x <- f (ZeroConst mt)
       return (replicate n x)
asVectorOf n f (VectorConst _ xs)
  | n == length xs
  = traverse f xs
asVectorOf n _ _
  = fail ("Expected vector constant value of length: " ++ show n)

data ArithInt where
  ArithInt :: Integer -> ArithInt
  ArithPtr :: L.Symbol -> Integer -> ArithInt

data Arith where
  ArithI :: ArithInt -> Arith
  ArithF :: Float -> Arith
  ArithD :: Double -> Arith

asArithInt ::
  (MonadFail m, HasPtrWidth wptr) =>
  Natural ->
  LLVMConst -> m ArithInt
asArithInt n (ZeroConst (IntType m))
  | n == m
  = return (ArithInt 0)
asArithInt n (IntConst w x)
  | toInteger n == natValue w
  = return (ArithInt x)
asArithInt n (PtrToIntConst (SymbolConst sym off))
  | toInteger n == natValue ?ptrWidth
  = return (ArithPtr sym off)
asArithInt _ _
  = fail "Expected integer value"

asArith ::
  (MonadFail m, HasPtrWidth wptr) =>
  MemType ->
  LLVMConst -> m Arith
asArith (IntType n) x = ArithI <$> asArithInt n x
asArith FloatType x   = ArithF <$> asFloat x
asArith DoubleType x  = ArithD <$> asDouble x
asArith _ _ = fail "Expected arithmetic type"

asInt ::
  MonadFail m =>
  Natural ->
  LLVMConst -> m Integer
asInt n (ZeroConst (IntType m))
  | n == m
  = return 0
asInt n (IntConst w x)
  | toInteger n == natValue w
  = return x
asInt n _
  = fail ("Expected integer constant of size " ++ show n)

asFloat ::
  MonadFail m =>
  LLVMConst -> m Float
asFloat (ZeroConst FloatType) = return 0
asFloat (FloatConst x) = return x
asFloat _ = fail "Expected floating point constant"

asDouble ::
  MonadFail m =>
  LLVMConst -> m Double
asDouble (ZeroConst DoubleType) = return 0
asDouble (DoubleConst x) = return x
asDouble _ = fail "Expected double constant"


-- | Compute the value of a constant expression.  Fails if
--   the expression does not actually represent a constant value.
transConstantExpr ::
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  MemType ->
  L.ConstExpr ->
  m LLVMConst
transConstantExpr _mt expr = case expr of
  L.ConstGEP _ _ [] -> badExp "Constant GEP must have at least two arguments"
  L.ConstGEP inbounds _ (base:exps) ->
    do gep <- translateGEP inbounds base exps
       gep' <- traverse transConstant gep
       evalConstGEP gep'

  L.ConstSelect b x y ->
    do b' <- transConstant b
       x' <- transConstant x
       y' <- transConstant y
       case b' of
         IntConst _w v
           | v /= 0    -> return x'
           | otherwise -> return y'
         _ -> badExp "Expected boolean value in constant select"

  L.ConstBlockAddr _ _ ->
    badExp "constant block addresses not supported"

  L.ConstFCmp op a b ->
    do mt <- liftMemType (L.typedType a)
       case mt of
         VecType n FloatType ->
           do a' <- asVectorOf n asFloat =<< transConstant a
              b' <- asVectorOf n asFloat =<< transConstant b
              return $ VectorConst (IntType 1) $ zipWith (evalFcmp op) a' b'
         VecType n DoubleType ->
           do a' <- asVectorOf n asDouble =<< transConstant a
              b' <- asVectorOf n asDouble =<< transConstant b
              return $ VectorConst (IntType 1) $ zipWith (evalFcmp op) a' b'
         FloatType ->
           do a' <- asFloat =<< transConstant a
              b' <- asFloat =<< transConstant b
              return $ evalFcmp op a' b'
         DoubleType ->
           do a' <- asDouble =<< transConstant a
              b' <- asDouble =<< transConstant b
              return $ evalFcmp op a' b'
         _ -> badExp "Expected floating point arguments"

  L.ConstICmp op a b ->
    do mt <- liftMemType (L.typedType a)
       case mt of
         VecType n (IntType m)
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asVectorOf n (asInt m) =<< transConstant a
                 b' <- asVectorOf n (asInt m) =<< transConstant b
                 return $ VectorConst (IntType 1) $ zipWith (evalIcmp op w) a' b'
         IntType m
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asInt m =<< transConstant a
                 b' <- asInt m =<< transConstant b
                 return $ evalIcmp op w a' b'
         _ -> badExp "Expected integer arguments"

  L.ConstArith op (L.Typed tp a) b ->
    do mt <- liftMemType tp
       case mt of
          VecType n tp' ->
            do a' <- asVectorOf n (asArith tp') =<< transConstant' mt a
               b' <- asVectorOf n (asArith tp') =<< transConstant' mt b
               VectorConst tp' <$> zipWithM (evalArith op tp') a' b'
          tp' ->
            do a' <- asArith tp' =<< transConstant' mt a
               b' <- asArith tp' =<< transConstant' mt b
               evalArith op tp' a' b'

  L.ConstBit op (L.Typed tp a) b ->
    do mt <- liftMemType tp
       case mt of
         VecType n (IntType m)
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asVectorOf n (asInt m) =<< transConstant' mt a
                 b' <- asVectorOf n (asInt m) =<< transConstant' mt b
                 VectorConst (IntType m) <$> zipWithM (evalBitwise op w) a' b'
         IntType m
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asInt m =<< transConstant' mt a
                 b' <- asInt m =<< transConstant' mt b
                 evalBitwise op w a' b'
         _ -> badExp "Expected integer arguments"

  L.ConstConv L.BitCast (L.Typed tp x) outty ->
   do toty <- liftMemType outty
      xty  <- liftMemType tp
      x' <- transConstant' xty x
      evalBitCast expr xty x' toty

  L.ConstConv op x outty ->
    do mt <- liftMemType outty
       x' <- transConstant x
       case mt of
         VecType n mt' ->
           do xs <- asVectorOf n return x'
              VectorConst mt' <$> traverse (evalConv expr op mt') xs

         _ -> evalConv expr op mt x'

 where badExp msg = fail $ unlines [msg, show expr]
