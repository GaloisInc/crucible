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

module Lang.Crucible.LLVM.MemModel.Type
  ( -- * Storable types
    StorageType(..)
  , StorageTypeF(..)
  , bitvectorType
  , floatType
  , doubleType
  , x86_fp80Type
  , arrayType
  , structType
  , mkStructType
  , mkStorageType
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
import Numeric.Natural

import Lang.Crucible.LLVM.Bytes

data Field v =
  Field
  { fieldOffset :: !Offset -- ^ Field offset from the beginning of the struct
  , _fieldVal   :: !v
  , fieldPad    :: !Bytes  -- ^ Number of padding bytes that follow this field
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable)

fieldVal :: Lens (Field a) (Field b) a b
fieldVal = lens _fieldVal (\s v -> s { _fieldVal = v })

mkField :: Offset -> v -> Bytes -> Field v
mkField = Field

data StorageTypeF v
  = Bitvector !Bytes -- ^ Size of bitvector in bytes (must be > 0).
  | Float
  | Double
  | X86_FP80
  | Array !Natural !v -- ^ Number of elements and element type
  | Struct !(Vector (Field v))
  deriving (Eq, Ord, Show, Typeable)

-- | Represents the storage type of an LLVM value. A 'Type' specifies
-- how a value is represented as bytes in memory.
data StorageType =
  StorageType
  { storageTypeF :: !(StorageTypeF StorageType)
  , storageTypeSize :: !Bytes
  }
  deriving (Eq, Ord, Typeable)

instance Show StorageType where
  showsPrec p t = showParen (p >= 10) $
    case storageTypeF t of
      Bitvector w -> showString "bitvectorType " . shows w
      Float -> showString "float"
      Double -> showString "double"
      X86_FP80 -> showString "long double"
      Array n tp -> showString "arrayType " . shows n . showString " " . showsPrec 10 tp
      Struct v -> showString "mkStructType " . shows (V.toList (fldFn <$> v))
        where fldFn f = (f^.fieldVal, fieldPad f)

mkStorageType :: StorageTypeF StorageType -> StorageType
mkStorageType tf = StorageType tf $
  case tf of
    Bitvector w -> w
    Float -> 4
    Double -> 8
    X86_FP80 -> 10
    Array n e -> toBytes n * storageTypeSize e
    Struct flds -> assert (V.length flds > 0) (fieldEnd (V.last flds))

bitvectorType :: Bytes -> StorageType
bitvectorType w = StorageType (Bitvector w) w

floatType :: StorageType
floatType = mkStorageType Float

doubleType :: StorageType
doubleType = mkStorageType Double

x86_fp80Type :: StorageType
x86_fp80Type = mkStorageType X86_FP80

arrayType :: Natural -> StorageType -> StorageType
arrayType n e = StorageType (Array n e) (toBytes n * storageTypeSize e)

structType :: V.Vector (Field StorageType) -> StorageType
structType flds = assert (V.length flds > 0) $
  StorageType (Struct flds) (fieldEnd (V.last flds))

mkStructType :: V.Vector (StorageType, Bytes) -> StorageType
mkStructType l = structType (evalState (traverse fldFn l) 0)
  where
    fldFn (tp,p) =
      do o <- get
         put $! o + storageTypeSize tp + p
         return Field { fieldOffset = o
                      , _fieldVal = tp
                      , fieldPad = p
                      }

-- | Returns end of actual type bytes (excluded padding from structs).
typeEnd :: Addr -> StorageType -> Addr
typeEnd a tp = seq a $
  case storageTypeF tp of
    Bitvector w -> a + w
    Float -> a + 4
    Double -> a + 8
    X86_FP80 -> a + 10
    Array n etp -> typeEnd (a + toBytes (n-1) * (storageTypeSize etp)) etp
    Struct flds -> typeEnd (a + fieldOffset f) (f^.fieldVal)
      where f = V.last flds

-- | Returns end of field including padding bytes.
fieldEnd :: Field StorageType -> Bytes
fieldEnd f = fieldOffset f + storageTypeSize (f^.fieldVal) + fieldPad f
