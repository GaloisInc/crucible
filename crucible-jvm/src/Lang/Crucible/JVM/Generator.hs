{- |
Module           : Lang.Crucible.JVM.Generator
Description      : Translation of JVM AST into Crucible control-flow graph
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -haddock #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Lang.Crucible.JVM.Generator where

-- base
import           Data.Semigroup
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Control.Monad.State.Strict
import           Control.Lens hiding (op, (:>))

-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr as NR


-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic

-- crucible-jvm
import           Lang.Crucible.JVM.Types

----------------------------------------------------------------------
-- Registers and Frame

data JVMReg s
  = DReg (Reg s JVMDoubleType)
  | FReg (Reg s JVMFloatType)
  | IReg (Reg s JVMIntType)
  | LReg (Reg s JVMLongType)
  | RReg (Reg s JVMRefType)
   deriving (Show)

data JVMFrame v
  = JVMFrame
    { _operandStack :: ![v]
    , _localVariables :: !(Map J.LocalVariableIndex v)
    }

instance Functor JVMFrame where
  fmap f (JVMFrame os lv) = JVMFrame (fmap f os) (fmap f lv)

instance Foldable JVMFrame where
  foldr f z (JVMFrame os lv) = foldr f (foldr f z lv) os

instance Traversable JVMFrame where
  traverse f (JVMFrame os lv) = JVMFrame <$> traverse f os <*> traverse f lv

operandStack :: Simple Lens (JVMFrame v) [v]
operandStack = lens _operandStack (\s v -> s{ _operandStack = v})

localVariables :: Simple Lens (JVMFrame v) (Map J.LocalVariableIndex v)
localVariables = lens _localVariables (\s v -> s{ _localVariables = v})

type JVMExprFrame s = JVMFrame (JVMValue s)
type JVMRegisters s = JVMFrame (JVMReg s)

----------------------------------------------------------------------
-- | JVMContext
-- 
-- Contains information about crucible Function handles and Global variables
-- that is statically known during the class translation.
-- 

data JVMHandleInfo where
  JVMHandleInfo :: J.MethodKey -> FnHandle init ret -> JVMHandleInfo

data JVMContext = JVMContext
  { methodHandles :: Map (J.ClassName, J.MethodKey) JVMHandleInfo
      -- ^ map from static & dynamic methods to Crucible function handles      
  , staticFields :: Map (J.ClassName, String) (GlobalVar JVMValueType)
      -- ^ map from static field names to Crucible global variables
      -- we know about these fields at translation time so we can allocate
      -- global variables to store them
  , classTable :: Map J.ClassName J.Class
      -- ^ map from class names to their declarations
      -- this contains all of the information about class declarations at
      -- translation time
  , dynamicClassTable :: GlobalVar JVMClassTableType
      -- ^ a global variable storing information about the class that can be
      -- used at runtime: includes initialization status, superclass (if any),
      -- and a map from method names to their handles for dynamic dispatch                      
  }

-- left-biased merge of two contexts
-- NOTE: There should only ever be one dynamic class table global variable. 
instance Semigroup JVMContext where
  c1 <> c2 =
    JVMContext
    { methodHandles     = Map.union (methodHandles   c1) (methodHandles   c2)
    , staticFields      = Map.union (staticFields c1) (staticFields c2)
    , classTable        = Map.union (classTable  c1) (classTable  c2)
    , dynamicClassTable = dynamicClassTable c1
    }

------------------------------------------------------------------------
-- JVMState

data JVMState ret s
  = JVMState
  { _jsLabelMap :: !(Map J.BBId (Label s))
  , _jsFrameMap :: !(Map J.BBId (JVMFrame (JVMReg s)))
  , _jsCFG      :: J.CFG
  , jsRetType   :: TypeRepr ret
  , jsContext   :: JVMContext
  }

jsLabelMap :: Simple Lens (JVMState ret s) (Map J.BBId (Label s))
jsLabelMap = lens _jsLabelMap (\s v -> s { _jsLabelMap = v })

jsFrameMap :: Simple Lens (JVMState ret s) (Map J.BBId (JVMFrame (JVMReg s)))
jsFrameMap = lens _jsFrameMap (\s v -> s { _jsFrameMap = v })

jsCFG :: Simple Lens (JVMState ret s) J.CFG
jsCFG = lens _jsCFG (\s v -> s { _jsCFG = v })

-- | Build the initial JVM generator state upon entry to the entry
-- point of a method.
initialState :: JVMContext -> J.Method -> TypeRepr ret -> JVMState ret s
initialState ctx method ret =
  JVMState {
    _jsLabelMap = Map.empty,
    _jsFrameMap = Map.empty,
    _jsCFG = methodCFG method,
    jsRetType = ret,
    jsContext = ctx
  }

methodCFG :: J.Method -> J.CFG
methodCFG method =
  case J.methodBody method of
    J.Code _ _ cfg _ _ _ _ -> cfg
    _                      -> error ("Method " ++ show method ++ " has no body")  

------------------------------------------------------------------------
-- 
-- Generator to construct a CFG from sequence of monadic actions:
-- See [Lang.Crucible.CFG.Generator]
--
-- 'h' is parameter from underlying ST monad
-- 's' is phantom to prevent mixing constructs from different CFGs
-- 'ret' is return type of CFG

type JVMGenerator h s ret = Generator JVM h s (JVMState ret) ret

-- | Indicate that CFG generation failed due to ill-formed JVM code.
jvmFail :: String -> JVMGenerator h s ret a
jvmFail msg = fail msg

-- | lookup the information that the generator has about a class
-- (i.e. methods, fields, superclass)
lookupClass :: J.ClassName -> JVMGenerator h s ret J.Class
lookupClass cName = do
  ctx <- gets jsContext
  case Map.lookup cName (classTable ctx) of
    Just cls -> return cls
    Nothing  -> jvmFail $ "no information about class " ++ J.unClassName cName

------------------------------------------------------------------


projectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s (VariantType ctx) ->
  JVMGenerator h s ret (Expr JVM s tp)
projectVariant tag var =
  do let mx = App (ProjectVariant knownRepr tag var)
     assertedJustExpr mx "incorrect variant"

injectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s tp ->
  Expr JVM s (VariantType ctx)
injectVariant tag val = App (InjectVariant knownRepr tag val)


fromJVMDynamic :: J.Type -> Expr JVM s JVMValueType -> JVMGenerator h s ret (JVMValue s)
fromJVMDynamic ty dyn =
  case ty of
    J.BooleanType -> IValue <$> projectVariant tagI dyn
    J.ArrayType _ -> RValue <$> projectVariant tagR dyn
    J.ByteType    -> IValue <$> projectVariant tagI dyn
    J.CharType    -> IValue <$> projectVariant tagI dyn
    J.ClassType _ -> RValue <$> projectVariant tagR dyn
    J.DoubleType  -> DValue <$> projectVariant tagD dyn
    J.FloatType   -> FValue <$> projectVariant tagF dyn
    J.IntType     -> IValue <$> projectVariant tagI dyn
    J.LongType    -> LValue <$> projectVariant tagL dyn
    J.ShortType   -> IValue <$> projectVariant tagI dyn

toJVMDynamic :: J.Type -> JVMValue s -> JVMGenerator h s ret (Expr JVM s JVMValueType)
toJVMDynamic ty val =
  case ty of
    J.BooleanType -> injectVariant tagI <$> fmap boolFromInt (fromIValue val)
    J.ArrayType _ -> injectVariant tagR <$> fromRValue val
    J.ByteType    -> injectVariant tagI <$> fmap byteFromInt (fromIValue val)
    J.CharType    -> injectVariant tagI <$> fmap charFromInt (fromIValue val)
    J.ClassType _ -> injectVariant tagR <$> fromRValue val
    J.DoubleType  -> injectVariant tagD <$> fromDValue val
    J.FloatType   -> injectVariant tagF <$> fromFValue val
    J.IntType     -> injectVariant tagI <$> fromIValue val
    J.LongType    -> injectVariant tagL <$> fromLValue val
    J.ShortType   -> injectVariant tagI <$> fmap shortFromInt (fromIValue val)


boolFromInt :: JVMInt s -> JVMInt s
boolFromInt x = App (BVZext w32 w1 (App (BVTrunc w1 w32 x)))

byteFromInt :: JVMInt s -> JVMInt s
byteFromInt i = App (BVSext w32 w8 (App (BVTrunc w8 w32 i)))

charFromInt :: JVMInt s -> JVMInt s
charFromInt i = App (BVZext w32 w16 (App (BVTrunc w16 w32 i)))

shortFromInt :: JVMInt s -> JVMInt s
shortFromInt i = App (BVSext w32 w16 (App (BVTrunc w16 w32 i)))

------------------------------------------------------------------------



fromIValue :: JVMValue s -> JVMGenerator h s ret (JVMInt s)
fromIValue (IValue v) = return v
fromIValue _ = jvmFail "fromIValue"

fromLValue :: JVMValue s -> JVMGenerator h s ret (JVMLong s)
fromLValue (LValue v) = return v
fromLValue _ = jvmFail "fromLValue"

fromDValue :: JVMValue s -> JVMGenerator h s ret (JVMDouble s)
fromDValue (DValue v) = return v
fromDValue _ = jvmFail "fromDValue"

fromFValue :: JVMValue s -> JVMGenerator h s ret (JVMFloat s)
fromFValue (FValue v) = return v
fromFValue _ = jvmFail "fromFValue"

fromRValue :: JVMValue s -> JVMGenerator h s ret (JVMRef s)
fromRValue (RValue v) = return v
fromRValue _ = jvmFail "fromRValue"


------------------------------------------------------------------

gen_isNothing :: (IsSyntaxExtension p, KnownRepr TypeRepr tp) =>
  Expr p s (MaybeType tp)
  -> Generator p h s ret k (Expr p s BoolType)
gen_isNothing expr =
  caseMaybe expr knownRepr
  MatchMaybe
  { onNothing = return $ App $ BoolLit True
  , onJust    = \_ -> return $ App $ BoolLit False
  }

gen_isJust :: (IsSyntaxExtension p, KnownRepr TypeRepr tp) =>
  Expr p s (MaybeType tp)
           -> Generator p h s ret k (Expr p s BoolType)
gen_isJust expr =
  caseMaybe expr knownRepr
  MatchMaybe
  { onNothing = return $ App $ BoolLit False
  , onJust    = \_ -> return $ App $ BoolLit True
  }
