-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Type
-- Description      : Representation of storable types used by the memory model
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Lang.Crucible.LLVM.MemModel.Type
  ( -- * Storable types
    Type(..)
  , TypeF(..)
  , bitvectorType
  , floatType
  , doubleType
  , x86_fp80Type
  , arrayType
  , structType
  , mkStructType
  , mkType
  , typeEnd
  , Field
  , fieldVal
  , fieldPad
  , fieldOffset
  , mkField

  )  where

import Control.Exception (assert)
import Control.Lens
import Control.Monad.State
import Data.Typeable
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word

import Lang.Crucible.LLVM.Bytes

data Field v =
  Field
  { fieldOffset :: Offset
  , _fieldVal   :: v
  , fieldPad    :: Bytes
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable)

fieldVal :: Lens (Field a) (Field b) a b
fieldVal = lens _fieldVal (\s v -> s { _fieldVal = v })

mkField :: Offset -> v -> Bytes -> Field v
mkField = Field

data TypeF v
  = Bitvector Bytes -- ^ Size of bitvector in bytes (must be > 0).
  | Float
  | Double
  | X86_FP80
  | Array Word64 v
  | Struct (Vector (Field v))
  deriving (Eq, Ord, Show, Typeable)

-- | Represents the storage type of an LLVM value. A 'Type' specifies
-- how a value is represented as bytes in memory.
data Type =
  Type
  { typeF :: TypeF Type
  , typeSize :: Bytes
  }
  deriving (Eq, Ord, Typeable)

instance Show Type where
  showsPrec p t = showParen (p >= 10) $
    case typeF t of
      Bitvector w -> showString "bitvectorType " . shows w
      Float -> showString "float"
      Double -> showString "double"
      X86_FP80 -> showString "long double"
      Array n tp -> showString "arrayType " . shows n . showString " " . showsPrec 10 tp
      Struct v -> showString "mkStructType " . shows (V.toList (fldFn <$> v))
        where fldFn f = (f^.fieldVal, fieldPad f)

mkType :: TypeF Type -> Type
mkType tf = Type tf $
  case tf of
    Bitvector w -> w
    Float -> 4
    Double -> 8
    X86_FP80 -> 10
    Array n e -> (Bytes n) * typeSize e
    Struct flds -> assert (V.length flds > 0) (fieldEnd (V.last flds))

bitvectorType :: Bytes -> Type
bitvectorType w = Type (Bitvector w) w

floatType :: Type
floatType = mkType Float

doubleType :: Type
doubleType = mkType Double

x86_fp80Type :: Type
x86_fp80Type = mkType X86_FP80

arrayType :: Word64 -> Type -> Type
arrayType n e = Type (Array n e) ((Bytes n) * typeSize e)

structType :: V.Vector (Field Type) -> Type
structType flds = assert (V.length flds > 0) $
  Type (Struct flds) (fieldEnd (V.last flds))

mkStructType :: V.Vector (Type, Bytes) -> Type
mkStructType l = structType (evalState (traverse fldFn l) 0)
  where
    fldFn (tp,p) =
      do o <- get
         put $! o + typeSize tp + p
         return Field { fieldOffset = o
                      , _fieldVal = tp
                      , fieldPad = p
                      }

-- | Returns end of actual type bytes (excluded padding from structs).
typeEnd :: Addr -> Type -> Addr
typeEnd a tp = seq a $
  case typeF tp of
    Bitvector w -> a + w
    Float -> a + 4
    Double -> a + 8
    X86_FP80 -> a + 10
    Array n etp -> typeEnd (a + Bytes (n-1) * (typeSize etp)) etp
    Struct flds -> typeEnd (a + fieldOffset f) (f^.fieldVal)
      where f = V.last flds

-- | Returns end of field including padding bytes.
fieldEnd :: Field Type -> Bytes
fieldEnd f = fieldOffset f + typeSize (f^.fieldVal) + fieldPad f
