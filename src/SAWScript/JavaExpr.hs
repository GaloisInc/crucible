{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.JavaExpr
  (-- * Java Expressions
    JavaExprF(..)
  , JavaExpr
  , asJavaExpr
  , thisJavaExpr
  , ppJavaExpr
  , jssTypeOfJavaExpr
  , isRefJavaExpr
  , isClassJavaExpr
    -- * Logic expressions
  , LogicExpr
  , logicExprJavaExprs
  , useLogicExpr
  , mkLogicExpr
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , JavaActualType(..)
  , jssTypeOfActual
  , isActualRef
  , logicTypeOfActual
  , ppActualType
  , MethodLocation (..)
  , JavaType(..)
  ) where

-- Imports {{{2

import Control.Applicative ((<$>))
import Control.Monad.Error (Error(..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Language.JVM.Common (ppFldId)

import qualified Verifier.Java.Codebase as JSS

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Utils

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

instance Error JavaExpr where
  noMsg = error "noMsg called with TC.JavaExpr"

thisJavaExpr :: JSS.Class -> JavaExpr
thisJavaExpr cl = CC.Term (Local "this" 0 (JSS.ClassType (JSS.className cl)))

-- | Pretty print a Java expression.
ppJavaExpr :: JavaExpr -> String
ppJavaExpr (CC.Term exprF) =
  case exprF of
    Local nm _ _ -> nm
    InstanceField r f -> ppJavaExpr r ++ "." ++ JSS.fieldIdName f
    StaticField f -> ppFldId f

asJavaExpr :: Map String JavaExpr -> LogicExpr -> Maybe JavaExpr
asJavaExpr m (LogicExpr t) = asJavaExpr' m t

asJavaExpr' :: Map String JavaExpr -> SharedTerm SAWCtx -> Maybe JavaExpr
asJavaExpr' m (asCtor -> Just (i, [e])) =
  case e of
    (asStringLit -> Just s) | i == parseIdent "Java.mkValue" -> Map.lookup s m
    _ -> Nothing
asJavaExpr' _ _ = Nothing

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

newtype LogicExpr = LogicExpr (SharedTerm SAWCtx)
  deriving (Show)

mkLogicExpr :: SharedTerm SAWCtx -> LogicExpr
mkLogicExpr = LogicExpr

useLogicExpr :: SharedContext JSSCtx -> LogicExpr -> IO (SharedTerm JSSCtx)
useLogicExpr sc (LogicExpr t) = scImport sc t

{-
-- | Return type of a typed expression.
typeOfLogicExpr :: SharedContext s -> LogicExpr s -> IO (SharedTerm s)
typeOfLogicExpr = scTypeOf
-}

-- | Return java expressions in logic expression.
logicExprJavaExprs :: Map String JavaExpr -> LogicExpr -> Set JavaExpr
logicExprJavaExprs m (LogicExpr t) = logicExprJavaExprs' m t

logicExprJavaExprs' :: Map String JavaExpr -> SharedTerm SAWCtx -> Set JavaExpr
logicExprJavaExprs' m (STApp _ tf) = CC.foldMap impl tf
  where impl = maybe Set.empty Set.singleton . asJavaExpr' m

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
