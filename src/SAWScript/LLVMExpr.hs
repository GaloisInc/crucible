{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
module SAWScript.LLVMExpr
  (-- * Java Expressions
    LLVMExprF(..)
  , LLVMExpr
  , ppLLVMExpr
  , lssTypeOfLLVMExpr
  , isPtrLLVMExpr
    -- * Logic expressions
  , LogicExpr
  , logicExprLLVMExprs
  , useLogicExpr
  , mkLogicExpr
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , LLVMActualType(..)
  , lssTypeOfActual
  , isActualPtr
  , isPrimitiveType
  , logicTypeOfActual
  --, isActualSubtype
  , ppActualType
  , SymbolLocation (..)
  ) where

-- Imports {{{2

import Control.Applicative ((<$>))
import Control.Monad.Error (Error(..))
import Data.Set (Set)
import Text.PrettyPrint.Leijen

import qualified Verifier.LLVM.Codebase as LSS
import qualified Verifier.LLVM.Codebase.DataLayout as LSS

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Utils

data SymbolLocation
   = Block LSS.SymBlockID
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

-- JavaExpr {{{1

data LLVMExprF v
  = Local String LSS.Ident LLVMActualType
  | StructField v String Int LLVMActualType
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable LLVMExprF where
  fequal (Local _ i _)(Local _ j _) = i == j
  fequal (StructField xr _ xi _) (StructField yr _ yi _) = xi == yi && (xr == yr)
  fequal _ _ = False

instance CC.OrdFoldable LLVMExprF where
  Local _ i _ `fcompare` Local _ i' _ = i `compare` i'
  Local _ _ _ `fcompare` _           = LT
  _           `fcompare` Local _ _ _ = GT
  StructField r1 _ f1 _ `fcompare` StructField r2 _ f2 _ =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r

instance CC.ShowFoldable LLVMExprF where
  fshow (Local nm _ _) = nm
  fshow (StructField r f _ _) = show r ++ "." ++ f

-- | Typechecked LLVMExpr
type LLVMExpr = CC.Term LLVMExprF

instance Error LLVMExpr where
  noMsg = error "noMsg called with TC.JavaExpr"

-- | Pretty print a LLVM expression.
ppLLVMExpr :: LLVMExpr -> Doc
ppLLVMExpr (CC.Term exprF) =
  case exprF of
    Local nm _ _ -> text nm
    StructField r f _ _ -> ppLLVMExpr r <> char '.' <> text f

-- | Returns LSS Type of LLVMExpr
lssTypeOfLLVMExpr :: LLVMExpr -> LSS.MemType
lssTypeOfLLVMExpr (CC.Term exprF) =
  case exprF of
    Local _ _ tp      -> tp
    StructField _ _ _ tp -> tp

-- | Returns true if expression is a pointer.
isPtrLLVMExpr :: LLVMExpr -> Bool
isPtrLLVMExpr e =
  case lssTypeOfLLVMExpr e of
    LSS.PtrType _ -> True
    _ -> False

-- LogicExpr {{{1

newtype LogicExpr = LogicExpr (SharedTerm SAWCtx)
  deriving (Termlike, Show)

mkLogicExpr :: SharedTerm SAWCtx -> LogicExpr
mkLogicExpr = LogicExpr

useLogicExpr :: SharedContext LSSCtx -> LogicExpr -> IO (SharedTerm LSSCtx)
useLogicExpr sc (LogicExpr t) = scImport sc t

{-
-- | Return type of a typed expression.
typeOfLogicExpr :: SharedContext s -> LogicExpr s -> IO (SharedTerm s)
typeOfLogicExpr = scTypeOf
-}

-- | Return java expressions in logic expression.
logicExprLLVMExprs :: LogicExpr -> Set LLVMExpr
logicExprLLVMExprs = error "logicExprLLVMExprs" --FIXME
  {- flip impl Set.empty
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

-- | A logic or Java expression.
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

-- | Returns Java symbolic simulator type that actual type represents.
lssTypeOfActual :: LLVMActualType -> LSS.MemType
lssTypeOfActual = id

-- | Returns logical type of actual type if it is an array or primitive type.
logicTypeOfActual :: SharedContext s -> LLVMActualType
                  -> IO (Maybe (SharedTerm s))
logicTypeOfActual _ _ = undefined -- FIXME
{-
logicTypeOfActual _ (ClassInstance _) = return Nothing
logicTypeOfActual sc (ArrayInstance l tp) = do
  elTy <- scBitvector sc (fromIntegral (JSS.stackWidth tp))
  lTm <- scNat sc (fromIntegral l)
  Just <$> scVecType sc lTm elTy
logicTypeOfActual sc (PrimitiveType tp) = do
  Just <$> scBitvector sc (fromIntegral (JSS.stackWidth tp))
-}

ppActualType :: LLVMActualType -> Doc
ppActualType = LSS.ppMemType
