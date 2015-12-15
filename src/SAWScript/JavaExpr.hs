{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  , asJavaExpr
  , ppJavaExpr
  , jeVarName
  , exprType
  , exprDepth
  , isScalarExpr
  , isReturnExpr
  , containsReturn
  , isArg
  , maxArg
  , isRefJavaExpr
  , isClassJavaExpr
    -- * Logic expressions
  , LogicExpr(..)
  , logicExprJavaExprs
  , useLogicExpr
  , scJavaValue
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , JavaActualType(..)
  , jssTypeOfActual
  , javaTypeToActual
  , isActualRef
  , narrowTypeOfActual
  , logicTypeOfActual
  , logicTypeOfJSSType
  , cryptolTypeOfActual
  , typeOfLogicExpr
  , ppActualType
  , parseJavaExpr
  , MethodLocation (..)
  , JavaType(..)
  ) where

-- Imports {{{2

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import Language.JVM.Common (ppFldId)

import Data.List (intercalate)
import Data.List.Split
import qualified Data.Vector as V
import Text.Read

import Verifier.Java.Codebase as JSS
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
  = ReturnVal JSS.Type
  | Local String JSS.LocalVariableIndex JSS.Type
  | InstanceField v JSS.FieldId
  | StaticField JSS.FieldId
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable JavaExprF where
  fequal (ReturnVal _) (ReturnVal _) = True
  fequal (Local _ i _)(Local _ j _) = i == j
  fequal (InstanceField xr xf) (InstanceField yr yf) = xf == yf && (xr == yr)
  fequal (StaticField xf) (StaticField yf) = xf == yf
  fequal _ _ = False

instance CC.OrdFoldable JavaExprF where
  ReturnVal _ `fcompare` ReturnVal _  = EQ
  ReturnVal _ `fcompare` _            = LT
  _           `fcompare` ReturnVal _  = GT
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
  fshow (ReturnVal _) = "return"
  fshow (Local nm _ _) = nm
  fshow (InstanceField r f) = show r ++ "." ++ JSS.fieldIdName f
  fshow (StaticField f) = ppFldId f

-- | Typechecked JavaExpr
type JavaExpr = CC.Term JavaExprF

thisJavaExpr :: JSS.Class -> JavaExpr
thisJavaExpr cl = CC.Term (Local "this" 0 (JSS.ClassType (JSS.className cl)))

returnJavaExpr :: JSS.Method -> Maybe (JavaExpr)
returnJavaExpr meth =
  (CC.Term . ReturnVal) <$> JSS.methodReturnType meth

isReturnExpr :: JavaExpr -> Bool
isReturnExpr (CC.Term (ReturnVal _)) = True
isReturnExpr _ = False

containsReturn :: JavaExpr -> Bool
containsReturn (CC.Term e) =
  case e of
    ReturnVal _ -> True
    InstanceField e' _ -> containsReturn e'
    _ -> False

-- | Pretty print a Java expression.
ppJavaExpr :: JavaExpr -> String
ppJavaExpr (CC.Term exprF) =
  case exprF of
    ReturnVal _ -> "return"
    Local nm _ _ -> nm
    InstanceField r f -> ppJavaExpr r ++ "." ++ JSS.fieldIdName f
    StaticField f -> ppFldId f

-- | Turn a Java expression into a valid SAWCore variable name.
jeVarName :: JavaExpr -> String
jeVarName = map dotToUnderscore . ppJavaExpr
  where dotToUnderscore '.' = '_'
        dotToUnderscore c = c

asJavaExpr :: SharedTerm s -> Maybe String
asJavaExpr (STApp _ (FTermF (ExtCns ec))) = Just (ecName ec)
asJavaExpr _ = Nothing

isRefJavaExpr :: JavaExpr -> Bool
isRefJavaExpr = JSS.isRefType . exprType

isClassJavaExpr :: JavaExpr -> Bool
isClassJavaExpr = isClassType . exprType
  where isClassType (JSS.ClassType _) = True
        isClassType _ = False

maxArg :: JSS.Method -> Int
maxArg meth = length (JSS.methodParameterTypes meth) - 1

isArg :: JSS.Method -> JavaExpr -> Bool
isArg meth (CC.Term (Local _ idx _)) =
  idx <= JSS.localIndexOfParameter meth (maxArg meth)
isArg _ _ = False

exprType :: JavaExpr -> JSS.Type
exprType (CC.Term (ReturnVal ty)) = ty
exprType (CC.Term (Local _ _ ty)) = ty
exprType (CC.Term (InstanceField _ f)) = JSS.fieldIdType f
exprType (CC.Term (StaticField f)) = JSS.fieldIdType f

exprDepth :: JavaExpr -> Int
exprDepth (CC.Term (InstanceField e _)) = 1 + exprDepth e
exprDepth _ = 1

isScalarExpr :: JavaExpr -> Bool
isScalarExpr = JSS.isPrimitiveType . exprType

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
  -- TODO: eventually change JSS.Type to JavaActualType, for more flexibility
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

javaTypeToActual :: JSS.Type -> Maybe JavaActualType
javaTypeToActual tp
  | JSS.isPrimitiveType tp = Just (PrimitiveType tp)
  | otherwise = Nothing

narrowTypeOfActual :: SharedContext s -> JavaActualType
                  -> IO (Maybe (SharedTerm s))
narrowTypeOfActual _ (ClassInstance _) = return Nothing
narrowTypeOfActual sc (ArrayInstance l tp) = do
  elTy <- scBitvector sc (fromIntegral (JSS.stackWidth tp))
  lTm <- scNat sc (fromIntegral l)
  Just <$> scVecType sc lTm elTy
narrowTypeOfActual sc (PrimitiveType JSS.BooleanType) =
  Just <$> scBitvector sc 1
narrowTypeOfActual sc (PrimitiveType JSS.ByteType) =
  Just <$> scBitvector sc 8
narrowTypeOfActual sc (PrimitiveType JSS.ShortType) =
  Just <$> scBitvector sc 16
narrowTypeOfActual sc (PrimitiveType JSS.IntType) =
  Just <$> scBitvector sc 32
narrowTypeOfActual sc (PrimitiveType JSS.LongType) =
  Just <$> scBitvector sc 64
narrowTypeOfActual _ ty =
  fail $ "Unsupported Java type " ++ show ty

-- | Returns logical type of actual type if it is an array or primitive type.
logicTypeOfActual :: SharedContext s -> JavaActualType
                  -> IO (Maybe (SharedTerm s))
logicTypeOfActual _ (ClassInstance _) = return Nothing
logicTypeOfActual sc (ArrayInstance l tp) = do
  elTy <- scBitvector sc (fromIntegral (JSS.stackWidth tp))
  lTm <- scNat sc (fromIntegral l)
  Just <$> scVecType sc lTm elTy
logicTypeOfActual sc (PrimitiveType tp) =
  logicTypeOfJSSType sc tp

logicTypeOfJSSType :: SharedContext s -> JSS.Type
                   -> IO (Maybe (SharedTerm s))
logicTypeOfJSSType _ (JSS.ArrayType _) = return Nothing
logicTypeOfJSSType _ (JSS.ClassType _) = return Nothing
logicTypeOfJSSType sc tp = do
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

parseJavaExpr :: JSS.Codebase -> JSS.Class -> JSS.Method -> String
              -> IO JavaExpr
parseJavaExpr cb cls meth estr = do
  sr <- parseStaticParts cb eparts
  case sr of
    Just e -> return e
    Nothing -> parseParts eparts
  where parseParts :: [String] -> IO JavaExpr
        parseParts [] = fail "empty Java expression"
        parseParts [s] =
          case s of
            "this" | JSS.methodIsStatic meth ->
                     fail $ "Can't use 'this' in static method " ++
                            JSS.methodName meth
                   | otherwise -> return (thisJavaExpr cls)
            "return" -> case returnJavaExpr meth of
                          Just e -> return e
                          Nothing ->
                            fail $ "No return value for " ++ methodName meth
            ('a':'r':'g':'s':'[':rest) -> do
              let num = fst (break (==']') rest)
              case readMaybe num of
                Just (n :: Int) -> do
                  let i = localIndexOfParameter meth n
                      mlv = lookupLocalVariableByIdx meth 0 i
                      paramTypes = V.fromList .
                                   methodKeyParameterTypes .
                                   methodKey $
                                   meth
                  case mlv of
                    Nothing
                      | n < V.length paramTypes ->
                        return (CC.Term (Local s i (paramTypes V.! (fromIntegral n))))
                      | otherwise ->
                        fail $ "(Zero-based) local variable index " ++ show i ++
                               " for parameter " ++ show n ++ " doesn't exist"
                    Just lv -> return (CC.Term (Local s i (localType lv)))
                Nothing -> fail $ "bad Java expression syntax: " ++ s
            _ | hasDebugInfo meth -> do
                  let mlv = lookupLocalVariableByName meth 0 s
                  case mlv of
                    Nothing -> fail $ "local " ++ s ++ " doesn't exist, expected one of: " ++
                                 unwords (map localName (localVariableEntries meth 0))
                    Just lv -> return (CC.Term (Local s i ty))
                      where i = JSS.localIdx lv
                            ty = JSS.localType lv
              | otherwise ->
                  fail $ "variable " ++ s ++
                         " referenced by name, but no debug info available"
        parseParts (f:rest) = do
          e <- parseParts rest
          let jt = exprType e
              pos = PosInternal "FIXME" -- TODO
          fid <- findField cb pos jt f
          return (CC.Term (InstanceField e fid))
        eparts = reverse (splitOn "." estr)

parseStaticParts :: Codebase -> [String] -> IO (Maybe JavaExpr)
parseStaticParts cb (fname:rest) = do
  let cname = intercalate "/" (reverse rest)
  mc <- tryLookupClass cb cname
  case mc of
    Just c ->
      case filter ((== fname) . fieldName) (classFields c) of
        [f] -> return (Just (CC.Term fld))
          where fld =  StaticField (FieldId cname fname (fieldType f))
        _ -> return Nothing
    Nothing -> return Nothing
parseStaticParts _ _ = return Nothing

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
