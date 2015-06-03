{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMExpr
  (-- * LLVM Expressions
    LLVMExprF(..)
  , LLVMExpr
  , ppLLVMExpr
  , lssTypeOfLLVMExpr
  , updateLLVMExprType
  , isPtrLLVMExpr
  , isArgLLVMExpr
    -- * Logic expressions
  , LogicExpr
  -- , logicExprLLVMExprs
  , useLogicExpr
  , mkLogicExpr
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , LLVMActualType
  , lssTypeOfActual
  , isActualPtr
  , isPrimitiveType
  , logicTypeOfActual
  , ppActualType
  , SymbolLocation (..)
  ) where

-- Imports {{{2

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif
-- import Data.Set (Set)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Verifier.LLVM.Codebase as LSS

import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Utils

data SymbolLocation
   = Block LSS.SymBlockID
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

-- LLVMExpr {{{1

-- NB: the types listed in each of these should be the type of the
-- entire expression. So "Deref v tp" means "*v has type tp".
data LLVMExprF v
  = Arg Int LSS.Ident LLVMActualType
  | Global LSS.Symbol LLVMActualType
  | Deref v LLVMActualType
  | StructField v LSS.StructInfo Int LLVMActualType
  | ReturnValue LLVMActualType
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable LLVMExprF where
  fequal (Arg i _ _)(Arg j _ _) = i == j
  fequal (Global x _)(Global y _) = x == y
  fequal (Deref e _) (Deref e' _) = e == e'
  fequal (StructField xr _ xi _) (StructField yr _ yi _) = xi == yi && (xr == yr)
  fequal (ReturnValue _) (ReturnValue _) = True
  fequal _ _ = False

instance CC.OrdFoldable LLVMExprF where
  Arg i _ _  `fcompare` Arg i' _ _   = i `compare` i'
  Arg _ _ _  `fcompare` _            = LT
  _          `fcompare` Arg _ _ _    = GT
  Global n _ `fcompare` Global n' _  = n `compare` n'
  Global _ _ `fcompare` _            = LT
  _          `fcompare` Global _ _   = GT
  Deref e _  `fcompare` Deref e' _   = e `compare` e'
  Deref _ _  `fcompare` _            = LT
  _          `fcompare` Deref _ _    = GT
  StructField r1 _ f1 _ `fcompare` StructField r2 _ f2 _ =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r
  StructField _ _ _ _ `fcompare` _           = LT
  _          `fcompare` StructField _ _ _ _ = GT
  (ReturnValue _) `fcompare` (ReturnValue _) = EQ

instance CC.ShowFoldable LLVMExprF where
  fshow (Arg _ nm _) = show nm
  fshow (Global nm _) = show nm
  fshow (Deref e _) = "*(" ++ show e ++ ")"
  fshow (StructField r _ f _) = show r ++ "." ++ show f
  fshow (ReturnValue _) = "return"

-- | Typechecked LLVMExpr
type LLVMExpr = CC.Term LLVMExprF

-- | Pretty print a LLVM expression.
ppLLVMExpr :: LLVMExpr -> Doc
ppLLVMExpr (CC.Term exprF) =
  case exprF of
    Arg _ nm _ -> text (show nm)
    Global nm _ -> LSS.ppSymbol nm
    Deref e _ -> char '*' <> parens (ppLLVMExpr e)
    StructField r _ f _ -> ppLLVMExpr r <> char '.' <> text (show f)
    ReturnValue _ -> text "return"

-- | Returns LSS Type of LLVMExpr
lssTypeOfLLVMExpr :: LLVMExpr -> LSS.MemType
lssTypeOfLLVMExpr (CC.Term exprF) =
  case exprF of
    Arg _ _ tp -> tp
    Global _ tp -> tp
    Deref _ tp -> tp
    StructField _ _ _ tp -> tp
    ReturnValue tp -> tp

updateLLVMExprType :: LLVMExpr -> LSS.MemType -> LLVMExpr
updateLLVMExprType (CC.Term exprF) tp = CC.Term $
  case exprF of
    Arg i n _ -> Arg i n tp
    Global n _ -> Global n tp
    Deref e _ -> Deref e tp
    StructField r si i _ -> StructField r si i tp
    ReturnValue _ -> ReturnValue tp

-- | Returns true if expression is a pointer.
isPtrLLVMExpr :: LLVMExpr -> Bool
isPtrLLVMExpr e =
  case lssTypeOfLLVMExpr e of
    LSS.PtrType _ -> True
    _ -> False

isArgLLVMExpr :: LLVMExpr -> Bool
isArgLLVMExpr (CC.Term (Arg _ _ _)) = True
isArgLLVMExpr _ = False

-- LogicExpr {{{1

newtype LogicExpr = LogicExpr (SharedTerm SAWCtx)
  deriving (Show)

mkLogicExpr :: SharedTerm SAWCtx -> LogicExpr
mkLogicExpr = LogicExpr

useLogicExpr :: SharedContext SAWCtx -> LogicExpr -> IO (SharedTerm SAWCtx)
useLogicExpr _ (LogicExpr t) = return t

{-
-- | Return type of a typed expression.
typeOfLogicExpr :: SharedContext s -> LogicExpr s -> IO (SharedTerm s)
typeOfLogicExpr = scTypeOf
-}

{-
-- | Return java expressions in logic expression.
logicExprLLVMExprs :: LogicExpr -> Set LLVMExpr
logicExprLLVMExprs = flip impl Set.empty
  where impl (Apply _ args) s = foldr impl s args
        impl (JavaValue e _ _) s = Set.insert e s
        impl _ s = s
-}

{-
-- | Returns names of variables appearing in typedExpr.
logicExprVarNames :: LogicExpr -> Set String
logicExprVarNames = flip impl Set.empty
  where impl (Apply _ args) s = foldr impl s args
        impl (Var nm _) s = Set.insert nm s
        impl _ s = s
-}

-- MixedExpr {{{1

-- | A logic or LLVM expression.
data MixedExpr
  = LogicE LogicExpr
  | LLVME LLVMExpr
  deriving (Show)

-- | Identifies concrete type of a LLVM expression. We can use normal
-- LLVM types to encode precise, actual types.
type LLVMActualType = LSS.MemType

isPrimitiveType :: LLVMActualType -> Bool
isPrimitiveType (LSS.IntType _) = True
isPrimitiveType LSS.FloatType = True
isPrimitiveType LSS.DoubleType = True
isPrimitiveType _ = False

instance Eq LSS.MemType where
  (LSS.IntType bw) == (LSS.IntType bw') = bw == bw'
  (LSS.PtrType (LSS.MemType mt)) == (LSS.PtrType (LSS.MemType mt')) = mt == mt'
  LSS.FloatType == LSS.FloatType = True
  LSS.DoubleType == LSS.DoubleType = True
  (LSS.ArrayType n t) == (LSS.ArrayType n' t') = n == n' && (t == t')
  (LSS.VecType n t) == (LSS.VecType n' t') = n == n' && (t == t')
  (LSS.StructType si) == (LSS.StructType si') = si == si'
  _ == _ = False

-- FIXME: not sure this is really the right way to go
instance Eq LSS.StructInfo where
  si == si' = LSS.siFields si == LSS.siFields si'

instance Eq LSS.FieldInfo where
  fi == fi' = LSS.fiOffset fi == LSS.fiOffset fi' &&
              LSS.fiType fi == LSS.fiType fi' &&
              LSS.fiPadding fi == LSS.fiPadding fi'

-- | Returns true if this represents a reference.
isActualPtr :: LLVMActualType -> Bool
isActualPtr (LSS.PtrType _) = True
isActualPtr (LSS.ArrayType _ _) = True
isActualPtr _ = False

-- | Returns LLVM symbolic simulator type that actual type represents.
lssTypeOfActual :: LLVMActualType -> LSS.MemType
lssTypeOfActual = id

-- | Returns logical type of actual type if it is an array or primitive type.
logicTypeOfActual :: SharedContext s -> LLVMActualType
                  -> IO (Maybe (SharedTerm s))
logicTypeOfActual sc (LSS.IntType w) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral w)
  Just <$> scVecType sc lTm bType
logicTypeOfActual sc LSS.FloatType = Just <$> scPrelude_Float sc
logicTypeOfActual sc LSS.DoubleType = Just <$> scPrelude_Double sc
logicTypeOfActual sc (LSS.ArrayType n ty) = do
  melTyp <- logicTypeOfActual sc ty
  case melTyp of
    Just elTyp -> do
      lTm <- scNat sc (fromIntegral n)
      Just <$> scVecType sc lTm elTyp
    Nothing -> return Nothing
logicTypeOfActual sc (LSS.PtrType _) =
  -- TODO: this is hardcoded to 32-bit pointers
  Just <$> scBitvector sc (4 * 8)
logicTypeOfActual _ _ = return Nothing

ppActualType :: LLVMActualType -> Doc
ppActualType = LSS.ppMemType
