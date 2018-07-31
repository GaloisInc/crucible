{- |
Module           : Lang.Crucible.JVM.Types
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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -haddock #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lang.Crucible.JVM.Types where

-- jvm-parser
import qualified Language.JVM.Parser as J

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some

-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.Types

----------------------------------------------------------------------
-- | JVM extension tag

newtype JVM = JVM () 
type instance ExprExtension JVM = EmptyExprExtension
type instance StmtExtension JVM = EmptyStmtExtension
instance IsSyntaxExtension JVM


---------------------------------------------------------------------------------
-- | Type abbreviations for expressions

type JVMBool       s = Expr JVM s BoolType
type JVMDouble     s = Expr JVM s JVMDoubleType
type JVMFloat      s = Expr JVM s JVMFloatType
type JVMInt        s = Expr JVM s JVMIntType
type JVMLong       s = Expr JVM s JVMLongType
type JVMRef        s = Expr JVM s JVMRefType

type JVMString     s = Expr JVM s StringType


type JVMClassTable s = Expr JVM s JVMClassTableType
type JVMClass      s = Expr JVM s JVMClassType
type JVMInitStatus s = Expr JVM s JVMInitStatusType

type JVMArray      s = Expr JVM s JVMArrayType
type JVMObject     s = Expr JVM s JVMObjectType

----------------------------------------------------------------------
-- | JVM type definitions
--
-- These are the types of values manipulated by the simulator

type JVMDoubleType = FloatType DoubleFloat
type JVMFloatType  = FloatType SingleFloat
type JVMIntType    = BVType 32
type JVMLongType   = BVType 64
type JVMRefType    = MaybeType (ReferenceType JVMObjectType)

-- | A JVM value is either a double, float, int, long, or reference. If we were
-- to define these types in Haskell, they'd look something like this
--
--  data Value = Double Double | Float Float | Int Int32 | Long Int64 | Ref (Maybe (IORef Object))
--
--  data Object   = Instance { fields :: Map String Value, class :: Class }
--                | Array    { length :: Int32, values :: Vector Value }
--
type JVMValueType = VariantType JVMValueCtx

type JVMValueCtx =
  EmptyCtx
  ::> JVMDoubleType
  ::> JVMFloatType
  ::> JVMIntType
  ::> JVMLongType
  ::> JVMRefType

-- | A class instance contains a table of fields
-- and an (immutable) pointer to the class (object).
type JVMInstanceType =
  StructType (EmptyCtx ::> StringMapType JVMValueType ::> JVMClassType)

-- | An array is a length paired with a vector of values.
type JVMArrayType =
  StructType (EmptyCtx ::> JVMIntType ::> VectorType JVMValueType)

-- | An object is either a class instance or an array.
type JVMObjectImpl =
  VariantType (EmptyCtx ::> JVMInstanceType ::> JVMArrayType)

type JVMObjectType = RecursiveType "JVM_object" EmptyCtx

instance IsRecursiveType "JVM_object" where
  type UnrollType "JVM_object" ctx = JVMObjectImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMObjectImpl

-- | A class initialization state is
--
--      data Initialization Status = NotStarted | Started | Initialized | Erroneous
--
-- We encode this type in Crucible using 2 bits
--
type JVMInitStatusType = BVType 2

type JVMMethodTableType = StringMapType AnyType

-- | An entry in the class table contains information about a loaded class:
--
--   data Class = MkClass { className   :: String
--                        , initStatus  :: InitStatus
--                        , superClass  :: Maybe Class
--                        , methodTable :: Map String Any    --- function handles are dynamically typed
--                        }
--
--   type ClassTable = Map String Class

type JVMClassType  = RecursiveType "JVM_class"  EmptyCtx

type JVMClassImpl =
  StructType (EmptyCtx ::> StringType
              ::> JVMInitStatusType
              ::> MaybeType JVMClassType
              ::> JVMMethodTableType)

instance IsRecursiveType "JVM_class" where
  type UnrollType "JVM_class" ctx = JVMClassImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMClassImpl

-- | The dynamic class table is a data structure that can be queried at runtime
-- for information about loaded classes
type JVMClassTableType = StringMapType JVMClassType

---------------------------------------------------------------------------------
-- | Translation between Java and Crucible Types

-- | Type reprs for the Crucible image of Java types
refRepr    :: TypeRepr JVMRefType
refRepr    = knownRepr 
intRepr    :: TypeRepr JVMIntType
intRepr    = knownRepr 
longRepr   :: TypeRepr JVMLongType
longRepr   = knownRepr 
doubleRepr :: TypeRepr JVMDoubleType
doubleRepr = knownRepr 
floatRepr  :: TypeRepr JVMFloatType
floatRepr  = knownRepr 

-- | Number reprs
w1 :: NatRepr 1
w1 = knownNat

w8 :: NatRepr 8
w8 = knownNat

w16 :: NatRepr 16
w16 = knownNat

w32 :: NatRepr 32
w32 = knownNat

w64 :: NatRepr 64
w64 = knownNat

-- | Translate a single Java type to a Crucible type
javaTypeToRepr :: J.Type -> Some TypeRepr
javaTypeToRepr t =
  case t of
    (J.ArrayType _) -> Some refRepr
    J.BooleanType   -> Some intRepr
    J.ByteType      -> Some intRepr
    J.CharType      -> Some intRepr
    (J.ClassType _) -> Some refRepr
    J.DoubleType    -> Some doubleRepr
    J.FloatType     -> Some floatRepr
    J.IntType       -> Some intRepr
    J.LongType      -> Some longRepr
    J.ShortType     -> Some intRepr

-- | Translate a sequence of Java types to a Crucible context
javaTypesToCtxRepr :: [J.Type] -> Some CtxRepr
javaTypesToCtxRepr [] = Some (knownRepr :: CtxRepr Ctx.EmptyCtx)
javaTypesToCtxRepr (ty:args) =
  case (javaTypeToRepr ty, javaTypesToCtxRepr args) of
    (Some t1, Some ctx) -> Some (ctx `Ctx.extend` t1)

---------------------------------------------------------------------------------
-- | Working with JVM values

-- NOTE: we could switch the below to "type JVMValue s = Expr JVM s
-- JVMValueType" However, that would give the translator less
-- information. With the type below, the translator can branch on the
-- variant. This is important for translating stack manipulations such
-- as popType1 and popType2
data JVMValue s
  = DValue (JVMDouble s)
  | FValue (JVMFloat s)
  | IValue (JVMInt s)
  | LValue (JVMLong s)
  | RValue (JVMRef s)
  deriving Show

-- | Returns a default value for given type, suitable for initializing
-- fields and arrays.
defaultValue :: J.Type -> JVMValue s
defaultValue (J.ArrayType _tp) = RValue $ App $ NothingValue knownRepr
defaultValue J.BooleanType     = IValue $ App $ BVLit knownRepr 0
defaultValue J.ByteType        = IValue $ App $ BVLit knownRepr 0
defaultValue J.CharType        = IValue $ App $ BVLit knownRepr 0
defaultValue (J.ClassType _st) = RValue $ App $ NothingValue knownRepr
defaultValue J.DoubleType      = DValue $ App $ DoubleLit 0.0
defaultValue J.FloatType       = FValue $ App $ FloatLit 0.0
defaultValue J.IntType         = IValue $ App $ BVLit knownRepr 0
defaultValue J.LongType        = LValue $ App $ BVLit knownRepr 0
defaultValue J.ShortType       = IValue $ App $ BVLit knownRepr 0

valueToExpr :: JVMValue s -> Expr JVM s JVMValueType
valueToExpr (DValue x) = App $ InjectVariant knownRepr tagD x
valueToExpr (FValue x) = App $ InjectVariant knownRepr tagF x
valueToExpr (IValue x) = App $ InjectVariant knownRepr tagI x
valueToExpr (LValue x) = App $ InjectVariant knownRepr tagL x
valueToExpr (RValue x) = App $ InjectVariant knownRepr tagR x

-- Index values for sums and products

tagD :: Ctx.Index JVMValueCtx JVMDoubleType
tagD = Ctx.i1of5

tagF :: Ctx.Index JVMValueCtx JVMFloatType
tagF = Ctx.i2of5

tagI :: Ctx.Index JVMValueCtx JVMIntType
tagI = Ctx.i3of5

tagL :: Ctx.Index JVMValueCtx JVMLongType
tagL = Ctx.i4of5

tagR :: Ctx.Index JVMValueCtx JVMRefType
tagR = Ctx.i5of5
