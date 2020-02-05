{- |
Module           : Lang.Crucible.JVM.Types
Description      : Type definitions for JVM->Crucible translation
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : sweirich@galois.com
Stability        : provisional
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -haddock #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


module Lang.Crucible.JVM.Types where

import           Prelude hiding (pred)

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
-- | JVM extension tag.

newtype JVM = JVM ()
type instance ExprExtension JVM = EmptyExprExtension
type instance StmtExtension JVM = EmptyStmtExtension

instance IsSyntaxExtension JVM

type Verbosity = Int

----------------------------------------------------------------------
-- * JVM type definitions
--
-- Crucible types for values manipulated by the simulator


-- ** Values
--
-- | A JVM value is either a double, float, int, long, or reference. If we were
-- to define these types in Haskell, they'd look something like this:
--
-- @
--  data Value = Double Double | Float Float | Int Int32
--             | Long Int64 | Ref (Maybe (IORef Object))
--
--  data Object   = Instance { fields :: Map String Value, class :: Class }
--                | Array    { length :: Int32, values :: Vector Value }
-- @
--
type JVMValueType = VariantType JVMValueCtx

type JVMValueCtx =
  EmptyCtx
  ::> JVMDoubleType
  ::> JVMFloatType
  ::> JVMIntType
  ::> JVMLongType
  ::> JVMRefType

type JVMDoubleType = FloatType DoubleFloat
type JVMFloatType  = FloatType SingleFloat
type JVMIntType    = BVType 32
type JVMLongType   = BVType 64
type JVMRefType    = MaybeType (ReferenceType JVMObjectType)


-- ** Objects and Arrays

-- | A class instance contains a table of fields
-- and an (immutable) pointer to the class (object).
type JVMInstanceType =
  StructType (EmptyCtx ::> StringMapType JVMValueType ::> JVMClassType)

-- | An array value is a length, a vector of values,
-- and an element type.
type JVMArrayType =
  StructType (EmptyCtx ::> JVMIntType ::> VectorType JVMValueType ::> JVMTypeRepType)

-- | An object is either a class instance or an array.
type JVMObjectImpl =
  VariantType (EmptyCtx ::> JVMInstanceType ::> JVMArrayType)

type JVMObjectType = RecursiveType "JVM_object" EmptyCtx

instance IsRecursiveType "JVM_object" where
  type UnrollType "JVM_object" ctx = JVMObjectImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMObjectImpl

-- ** JVM type representations
--
-- @
--   data Type = ArrayType Type
--             | ClassType Class
--             | Primitive Int    -- ints represent different primitives
-- @
-- We need to know the type of an array at runtime in order to do
-- an instance-of or checked cast for arrays.

type JVMTypeRepType = RecursiveType "JVM_TypeRep" EmptyCtx
instance IsRecursiveType "JVM_TypeRep" where
  type UnrollType "JVM_TypeRep" ctx = JVMTypeRepImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMTypeRepImpl

type JVMTypeRepImpl =
  VariantType (EmptyCtx ::> JVMTypeRepType ::> JVMClassType ::> JVMIntType)


-- ** Classes

-- | An entry in the class table contains information about a loaded class:
--
-- @
--   data Class = MkClass { className   :: String
--                        , initStatus  :: InitStatus
--                        , superClass  :: Maybe Class
--                        , methodTable :: Map String Any
--                        , interfaces  :: Vector String
--                        }
--
--   type ClassTable = Map String Class
-- @
--
type JVMClassType  = RecursiveType "JVM_class"  EmptyCtx

type JVMClassImpl =
  StructType (EmptyCtx
              ::> StringType Unicode -- TODO should be Char16
              ::> JVMInitStatusType
              ::> MaybeType JVMClassType
              ::> JVMMethodTableType
              ::> VectorType (StringType Unicode)) -- TODO Should be Char16

instance IsRecursiveType "JVM_class" where
  type UnrollType "JVM_class" ctx = JVMClassImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMClassImpl

-- | A class initialization state is:
--
-- @
--      data Initialization Status = NotStarted | Started | Initialized | Erroneous
-- @
--
-- We encode this type in Crucible using 2 bits.
--
type JVMInitStatusType = BVType 2

-- | The method table is dynamically typed.
type JVMMethodTableType = StringMapType AnyType

-- | The dynamic class table is a data structure that can be queried at runtime
-- for information about loaded classes.
type JVMClassTableType = StringMapType JVMClassType


---------------------------------------------------------------------------------
-- * Type representations

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

objectRepr :: TypeRepr JVMObjectType
objectRepr = knownRepr

arrayRepr :: TypeRepr JVMArrayType
arrayRepr = knownRepr

instanceRepr :: TypeRepr JVMInstanceType
instanceRepr = knownRepr

showJVMType :: TypeRepr a -> String
showJVMType x
  | Just Refl <- testEquality x refRepr    = "JVMRef"
  | Just Refl <- testEquality x intRepr    = "JVMInt"
  | Just Refl <- testEquality x longRepr   = "JVMLong"
  | Just Refl <- testEquality x doubleRepr = "JVMDouble"
  | Just Refl <- testEquality x floatRepr  = "JVMFloat"
  | otherwise = show x

showJVMArgs :: Ctx.Assignment TypeRepr x -> String
showJVMArgs x =
  case x of
    Ctx.Empty -> ""
    Ctx.Empty Ctx.:> ty -> showJVMType ty
    y Ctx.:> ty -> showJVMArgs y ++ ", "  ++ showJVMType ty


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

---------------------------------------------------------
-- * Translation between Java and Crucible Types


-- | Translate a single Java type to a Crucible type.
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

-- | Translate a sequence of Java types to a Crucible context.
javaTypesToCtxRepr :: [J.Type] -> Some CtxRepr
javaTypesToCtxRepr [] = Some (knownRepr :: CtxRepr Ctx.EmptyCtx)
javaTypesToCtxRepr (ty:args) =
  case (javaTypeToRepr ty, javaTypesToCtxRepr args) of
    (Some t1, Some ctx) -> Some (ctx `Ctx.extend` t1)

---------------------------------------------------------------------------------
-- * Index values for sums and products

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

---------------------------------------------------------------------------------
-- * Type abbreviations for expressions

-- | Symbolic booleans.
type JVMBool       s = Expr JVM s BoolType
-- | Symbolic double precision float.
type JVMDouble     s = Expr JVM s JVMDoubleType
-- | Symbolic single precision  float.
type JVMFloat      s = Expr JVM s JVMFloatType
-- | Symbolic 32-bit signed integers.
type JVMInt        s = Expr JVM s JVMIntType
-- | Symbolic 64-bit signed integers.
type JVMLong       s = Expr JVM s JVMLongType
-- | Symbolic references.
type JVMRef        s = Expr JVM s JVMRefType
-- | Symbolic strings.
type JVMString     s = Expr JVM s (StringType Unicode) -- TODO, should be Char16
-- | Symbolic class table.
type JVMClassTable s = Expr JVM s JVMClassTableType
-- | Symbolic data structure for class information.
type JVMClass      s = Expr JVM s JVMClassType
-- | Symbolic class initialization.
type JVMInitStatus s = Expr JVM s JVMInitStatusType
-- | Symbolic Java-encdoed array, includes type.
type JVMArray      s = Expr JVM s JVMArrayType
-- | Symbolic array or class instance.
type JVMObject     s = Expr JVM s JVMObjectType
-- | Symbolic representation of Java type.
type JVMTypeRep    s = Expr JVM s JVMTypeRepType
