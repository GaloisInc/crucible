{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWScript.JavaExpr
  (-- * Java Expressions
    JavaExprF(..)
  , JavaExpr
  , thisJavaExpr
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
  , ppActualType
  , MethodLocation (..)
  , JavaType(..)
  ) where

-- Imports {{{2

import Control.Applicative
import Control.Monad
import Control.Monad.Error (Error(..))
import Data.Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Language.JVM.Common (ppFldId)

import qualified Verifier.Java.Codebase as JSS
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
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

thisJavaExpr :: JSS.Class -> JavaExpr
thisJavaExpr cl = CC.Term (Local "this" 0 (JSS.ClassType (JSS.className cl)))

-- | Pretty print a Java expression.
ppJavaExpr :: JavaExpr -> String
ppJavaExpr (CC.Term exprF) =
  case exprF of
    Local nm _ _ -> nm
    InstanceField r f -> ppJavaExpr r ++ "." ++ JSS.fieldIdName f
    StaticField f -> ppFldId f

asJavaExpr :: SharedTerm SAWCtx -> Maybe String
asJavaExpr t =
  case asApplyAll t of
    (asGlobalDef -> Just "Java.mkValue", [_, asStringLit -> s]) -> s
    _ -> Nothing

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
              -- contain any @Java.mkValue@ subexpressions.
              leTerm :: SharedTerm SAWCtx
              -- | The Java expressions, if any, that the term should
              -- be applied to
            , leJavaArgs :: [JavaExpr]
            }
  deriving (Show)

scJavaValue :: SharedContext s -> SharedTerm s -> String -> IO (SharedTerm s)
scJavaValue sc ty name = do
  s <- scString sc name
  ty' <- scRemoveBitvector sc ty
  mkValue <- scGlobalDef sc (parseIdent "Java.mkValue")
  scApplyAll sc mkValue [ty', s]

mkMixedExpr :: Map String JavaExpr
            -> Map JavaExpr JavaActualType
            -> SharedContext SAWCtx
            -> SharedTerm SAWCtx
            -> IO MixedExpr
mkMixedExpr m _ _ (asJavaExpr -> Just s) =
  case Map.lookup s m of
    Nothing -> fail $ "Java expression not found: " ++ s
    Just je -> return (JE je)
mkMixedExpr m tys sc t = do
  let javaExprNames = Set.toList (termJavaExprs t)
      findWithMsg msg k m = maybe (fail msg) return (Map.lookup k m)
  -- print javaExprNames
  localVars <- mapM (scLocalVar sc) $ reverse [0..length javaExprNames - 1]
  r <- forM (zip javaExprNames localVars) $ \(name, var) -> do
    jexp <- findWithMsg ("Unknown Java expression: " ++ name) name m
    aty <- findWithMsg ("No type for Java expression: " ++ name) jexp tys
    mlty <- logicTypeOfActual sc aty
    case mlty of
      Just lty -> do
        jval <- scJavaValue sc lty name
        -- print $ "Rule: " ++ show jval ++ " -> " ++ show var
        return (jexp, (name, lty), ruleOfTerms jval var)
      Nothing -> fail $ "Can't convert actual type to logic type: " ++ show aty
  let (javaExprs, args, rules) = unzip3 r
  basics <- basic_ss sc
  let ss = addRules rules basics
  t' <- rewriteSharedTerm sc ss t
  le <- LogicExpr <$> scLambdaList sc args t' <*> pure javaExprs
  return (LE le)

-- | Return java expressions in logic expression.
logicExprJavaExprs :: LogicExpr -> [JavaExpr]
logicExprJavaExprs = leJavaArgs

termJavaExprs :: SharedTerm SAWCtx -> Set String
termJavaExprs = snd . impl (Set.empty, Set.empty)
  where impl a@(seen, exprs) t@(STApp idx tf)
          | Set.member idx seen = a
          | otherwise =
            case asJavaExpr t of
              Just s -> (Set.insert idx seen, Set.insert s exprs)
              Nothing -> foldl' impl (Set.insert idx seen, exprs) tf

useLogicExpr :: SharedContext JSSCtx -> LogicExpr -> [SharedTerm JSSCtx]
             -> IO (SharedTerm JSSCtx)
useLogicExpr sc (LogicExpr t _) args = do
  t' <- scImport sc t
  t'' <- scApplyAll sc t' args
  -- _ty <- scTypeCheckError sc t''
  return t''

{-
-- | Return type of a typed expression.
typeOfLogicExpr :: SharedContext s -> LogicExpr s -> IO (SharedTerm s)
typeOfLogicExpr = scTypeOf
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
