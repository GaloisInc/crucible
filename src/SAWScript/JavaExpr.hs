{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.JavaExpr
  (-- * Java Expressions
    JavaExprF(..)
  , JavaExpr
  , thisJavaExpr
  , returnJavaExpr
  , ppJavaExpr
  , jssTypeOfJavaExpr
  , isRefJavaExpr
  , isClassJavaExpr
    -- * Logic expressions
  , LogicExpr
  , logicExprJavaExprs
  , useLogicExpr
  , mkMixedExpr
  , scJavaValue
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , JavaActualType(..)
  , jssTypeOfActual
  , isActualRef
  , logicTypeOfActual
  , cryptolTypeOfActual
  , typeOfLogicExpr
  , ppActualType
  , MethodLocation (..)
  , JavaType(..)
  ) where

-- Imports {{{2

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Data.Map (Map)
import qualified Data.Map as Map

import Language.JVM.Common (ppFldId)

import qualified Verifier.Java.Codebase as JSS
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Utils

import qualified Cryptol.TypeCheck.AST as Cryptol

data MethodLocation
   = PC Integer
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

-- JavaExpr {{{1

data JavaExprF v
  = Local String JSS.LocalVariableIndex JSS.Type
  | InstanceField v JSS.FieldId
  | StaticField JSS.FieldId
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable JavaExprF where
  fequal (Local _ i _)(Local _ j _) = i == j
  fequal (InstanceField xr xf) (InstanceField yr yf) = xf == yf && (xr == yr)
  fequal (StaticField xf) (StaticField yf) = xf == yf
  fequal _ _ = False

instance CC.OrdFoldable JavaExprF where
  Local _ i _ `fcompare` Local _ i' _ = i `compare` i'
  Local _ _ _ `fcompare` _           = LT
  _           `fcompare` Local _ _ _ = GT
  InstanceField r1 f1 `fcompare` InstanceField r2 f2 =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r
  StaticField f1 `fcompare` StaticField f2 = f1 `compare` f2
  StaticField _ `fcompare` _ = GT
  _ `fcompare` StaticField _ = LT

instance CC.ShowFoldable JavaExprF where
  fshow (Local nm _ _) = nm
  fshow (InstanceField r f) = show r ++ "." ++ JSS.fieldIdName f
  fshow (StaticField f) = ppFldId f

-- | Typechecked JavaExpr
type JavaExpr = CC.Term JavaExprF

thisJavaExpr :: JSS.Class -> JavaExpr
thisJavaExpr cl = CC.Term (Local "this" 0 (JSS.ClassType (JSS.className cl)))

returnJavaExpr :: JSS.Method -> Maybe (JavaExpr)
returnJavaExpr meth =
  (CC.Term . Local "return" maxBound) <$> JSS.methodReturnType meth

-- | Pretty print a Java expression.
ppJavaExpr :: JavaExpr -> String
ppJavaExpr (CC.Term exprF) =
  case exprF of
    Local nm _ _ -> nm
    InstanceField r f -> ppJavaExpr r ++ "." ++ JSS.fieldIdName f
    StaticField f -> ppFldId f

asJavaExpr :: SharedTerm SAWCtx -> Maybe String
asJavaExpr (STApp _ (FTermF (ExtCns ec))) = Just (ecName ec)
asJavaExpr _ = Nothing

-- | Returns JSS Type of JavaExpr
jssTypeOfJavaExpr :: JavaExpr -> JSS.Type
jssTypeOfJavaExpr (CC.Term exprF) =
  case exprF of
    Local _ _ tp      -> tp
    InstanceField _ f -> JSS.fieldIdType f
    StaticField f -> JSS.fieldIdType f

isRefJavaExpr :: JavaExpr -> Bool
isRefJavaExpr = JSS.isRefType . jssTypeOfJavaExpr

isClassJavaExpr :: JavaExpr -> Bool
isClassJavaExpr = isClassType . jssTypeOfJavaExpr
  where isClassType (JSS.ClassType _) = True
        isClassType _ = False

-- LogicExpr {{{1

data LogicExpr =
  LogicExpr { -- | A term, possibly function type, which does _not_
              -- contain any external constant subexpressions.
              _leTerm :: SharedTerm SAWCtx
              -- | The Java expressions, if any, that the term should
              -- be applied to
            , leJavaArgs :: [JavaExpr]
            }
  deriving (Show)

scJavaValue :: SharedContext s -> SharedTerm s -> String -> IO (SharedTerm s)
scJavaValue sc ty name = do
  scFreshGlobal sc name ty

mkMixedExpr :: Map String JavaExpr
            -> SharedContext SAWCtx
            -> SharedTerm SAWCtx
            -> IO MixedExpr
mkMixedExpr m _ (asJavaExpr -> Just s) =
  case Map.lookup s m of
    Nothing -> fail $ "Java expression not found: " ++ s
    Just je -> return (JE je)
mkMixedExpr m sc t = do
  let exts = getAllExts t
      extNames = map ecName exts
      findWithMsg msg k m' = maybe (fail msg) return (Map.lookup k m')
  javaExprs <- mapM
               (\n -> findWithMsg ("Unknown Java expression: " ++ n) n m)
               extNames
  le <- LogicExpr <$> scAbstractExts sc exts t <*> pure javaExprs
  return (LE le)

-- | Return java expressions in logic expression.
logicExprJavaExprs :: LogicExpr -> [JavaExpr]
logicExprJavaExprs = leJavaArgs

useLogicExpr :: SharedContext SAWCtx -> LogicExpr -> [SharedTerm SAWCtx]
             -> IO (SharedTerm SAWCtx)
useLogicExpr sc (LogicExpr t _) args = scApplyAll sc t args

-- | Return type of a typed expression.
typeOfLogicExpr :: SharedContext SAWCtx -> LogicExpr -> IO (SharedTerm SAWCtx)
typeOfLogicExpr sc (LogicExpr t _) = scTypeOf sc t

-- MixedExpr {{{1

-- | A logic or Java expression.
data MixedExpr
  = LE LogicExpr
  | JE JavaExpr
  deriving (Show)

-- | Identifies concrete type of a Java expression.
data JavaActualType
  = ClassInstance JSS.Class
  | ArrayInstance Int JSS.Type
  | PrimitiveType JSS.Type
  deriving (Show)

instance Eq JavaActualType where
  ClassInstance c1 == ClassInstance c2 = JSS.className c1 == JSS.className c2
  ArrayInstance l1 tp1 == ArrayInstance l2 tp2 = l1 == l2 && tp1 == tp2
  PrimitiveType tp1 == PrimitiveType tp2 = tp1 == tp2
  _ == _ = False

-- | Returns true if this represents a reference.
isActualRef :: JavaActualType -> Bool
isActualRef ClassInstance{} = True
isActualRef ArrayInstance{} = True
isActualRef PrimitiveType{} = False

-- | Returns Java symbolic simulator type that actual type represents.
jssTypeOfActual :: JavaActualType -> JSS.Type
jssTypeOfActual (ClassInstance x) = JSS.ClassType (JSS.className x)
jssTypeOfActual (ArrayInstance _ tp) = JSS.ArrayType tp
jssTypeOfActual (PrimitiveType tp) = tp

-- | Returns logical type of actual type if it is an array or primitive type.
logicTypeOfActual :: SharedContext s -> JavaActualType
                  -> IO (Maybe (SharedTerm s))
logicTypeOfActual _ (ClassInstance _) = return Nothing
logicTypeOfActual sc (ArrayInstance l tp) = do
  elTy <- scBitvector sc (fromIntegral (JSS.stackWidth tp))
  lTm <- scNat sc (fromIntegral l)
  Just <$> scVecType sc lTm elTy
logicTypeOfActual sc (PrimitiveType tp) = do
  Just <$> scBitvector sc (fromIntegral (JSS.stackWidth tp))

cryptolTypeOfActual :: JavaActualType -> Maybe Cryptol.Type
cryptolTypeOfActual (ClassInstance _) = Nothing
cryptolTypeOfActual (ArrayInstance l (JSS.stackWidth -> n)) =
  Just $ Cryptol.tSeq (Cryptol.tNum l) (Cryptol.tSeq (Cryptol.tNum n) Cryptol.tBit)
cryptolTypeOfActual (PrimitiveType (JSS.stackWidth -> n)) = do
  Just $ Cryptol.tSeq (Cryptol.tNum n) Cryptol.tBit

ppActualType :: JavaActualType -> String
ppActualType (ClassInstance x) = JSS.slashesToDots (JSS.className x)
ppActualType (ArrayInstance l tp) = show tp ++ "[" ++ show l ++ "]"
ppActualType (PrimitiveType tp) = show tp

-- JavaType {{{1

-- | Adapted from type 'JavaType' in Java.sawcore.
data JavaType
  = JavaBoolean
  | JavaByte
  | JavaChar
  | JavaShort
  | JavaInt
  | JavaLong
  | JavaFloat
  | JavaDouble
  | JavaArray Int JavaType
  | JavaClass String
  deriving Eq
