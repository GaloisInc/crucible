{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.JavaExpr
  (-- * Java Expressions
    JavaExprF(..)
  , JavaExpr
  , thisJavaExpr
  , ppJavaExpr
  , jssTypeOfJavaExpr
  , isRefJavaExpr
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
  , isActualSubtype
  , ppActualType
  , MethodLocation (..)
  ) where

-- Imports {{{2

import Control.Applicative ((<$>))
import Control.Monad.Error (Error(..))
import Data.Set (Set)

import qualified Verifier.Java.Codebase as JSS

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm

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
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable JavaExprF where
  fequal (Local _ i _)(Local _ j _) = i == j
  fequal (InstanceField xr xf) (InstanceField yr yf) = xf == yf && (xr == yr)
  fequal _ _ = False

instance CC.OrdFoldable JavaExprF where
  Local _ i _ `fcompare` Local _ i' _ = i `compare` i'
  Local _ _ _ `fcompare` _           = LT
  _           `fcompare` Local _ _ _ = GT
  InstanceField r1 f1 `fcompare` InstanceField r2 f2 =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r

instance CC.ShowFoldable JavaExprF where
  fshow (Local nm _ _) = nm
  fshow (InstanceField r f) = show r ++ "." ++ JSS.fieldIdName f

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

-- | Returns JSS Type of JavaExpr
jssTypeOfJavaExpr :: JavaExpr -> JSS.Type
jssTypeOfJavaExpr (CC.Term exprF) =
  case exprF of
    Local _ _ tp      -> tp
    InstanceField _ f -> JSS.fieldIdType f

-- | Returns true if expression is a Boolean.
isRefJavaExpr :: JavaExpr -> Bool
isRefJavaExpr = JSS.isRefType . jssTypeOfJavaExpr

-- LogicExpr {{{1

newtype LogicExpr = LogicExpr (SharedTerm SAWCtx)
  deriving (Termlike, Show)

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
logicExprJavaExprs :: LogicExpr -> Set JavaExpr
logicExprJavaExprs = error "logicExprJavaExprs" --FIXME
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

-- @isActualSubtype cb x y@ returns True if @x@ is a subtype of @y@.
isActualSubtype :: JSS.Codebase -> JavaActualType -> JavaActualType -> IO Bool
isActualSubtype cb (ArrayInstance lx ex) (ArrayInstance ly ey)
  | lx == ly = JSS.isSubtype cb ex ey
  | otherwise = return False
isActualSubtype cb x y 
  = JSS.isSubtype cb (jssTypeOfActual x) (jssTypeOfActual y)

ppActualType :: JavaActualType -> String
ppActualType (ClassInstance x) = JSS.slashesToDots (JSS.className x)
ppActualType (ArrayInstance l tp) = show tp ++ "[" ++ show l ++ "]"
ppActualType (PrimitiveType tp) = show tp

-- SawTI {{{1

{-
type SawTI s = TI IO (TCConfig s)

getMethodInfo :: SawTI s MethodInfo
getMethodInfo = do
  maybeMI <- gets methodInfo
  case maybeMI of
    Nothing -> error $ 
      "internal: getMethodInfo called when parsing outside a method declaration"
    Just p -> return p

-- | Check argument count matches expected length
checkArgCount :: Pos -> String -> [a] -> Int -> SawTI s ()
checkArgCount pos nm (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    typeErr pos $ ftext $ "Incorrect number of arguments to \'" ++ nm ++ "\'.  "
                        ++ show expectedCnt ++ " arguments were expected, but "
                        ++ show foundOpCnt ++ " arguments were found."

-- Core expression typechecking {{{1

getActualType :: Pos -> JavaExpr -> SawTI s JavaActualType
getActualType p je = do
  mmi <- gets methodInfo
  case mmi of
    Nothing ->
      let msg = "The Java value \'" ++ ppJavaExpr je ++ "\' appears in a global context."
          res = "Java values may not be references outside method declarations."
       in typeErrWithR p (ftext msg) res
    Just mi -> do
      case miJavaExprType mi je of
        Nothing -> 
          let msg = "The Java value \'" ++ ppJavaExpr je ++ "\' has not been declared."
              res = "Please explicitly declare Java expressions before referring to them."
           in typeErrWithR p (ftext msg) res
        Just at -> return at

-- | Verify that type is supported by SAWScript.
checkIsSupportedType :: Pos -> JSS.Type -> SawTI s ()
checkIsSupportedType pos tp =
  case tp of
    JSS.DoubleType -> throwFloatUnsupported
    JSS.FloatType  -> throwFloatUnsupported
    JSS.ArrayType eltType -> do
      when (JSS.isFloatType eltType) $ throwFloatUnsupported
      when (JSS.isRefType eltType) $ do
        let msg = "SAWScript does not support arrays of references."
         in typeErr pos (ftext msg)
    _ -> return ()
 where throwFloatUnsupported =
         let msg = "SAWScript does not support floating point types."
          in typeErr pos (ftext msg)

-- | Create a Java expression representing a local variable.
mkLocalVariable :: Pos -> JSS.LocalVariableTableEntry -> SawTI s JavaExpr
mkLocalVariable pos e = do
  let tp = JSS.localType e
  checkIsSupportedType pos tp
  return $ CC.Term $ Local (JSS.localName e) (JSS.localIdx e) tp
-}
