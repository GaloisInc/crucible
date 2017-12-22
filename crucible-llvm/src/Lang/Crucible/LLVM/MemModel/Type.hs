-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Common
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
  ( -- * Bytes
    Bytes(..)
  , Addr
  , Size
  , Offset
  , bytesToBits
  , bytesToInteger
  , toBytes
  , bitsToBytes

    -- * Storable types
  , Type(..)
  , TypeF(..)
  , bitvectorType
  , floatType
  , doubleType
  , arrayType
  , mkStruct
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

-- | A newtype for expressing numbers of bytes.
--   This newtype is explicitly introduced to avoid confusion
--   between widths expressed as numbers of bits vs numbers of bytes.
newtype Bytes = Bytes { unBytes :: Word64 }
  deriving (Eq, Ord, Num, Show)

bytesToBits :: Bytes -> Integer
bytesToBits (Bytes n) = 8 * toInteger n

bytesToInteger :: Bytes -> Integer
bytesToInteger (Bytes n) = toInteger n

toBytes :: Integral a => a -> Bytes
toBytes = Bytes . fromIntegral

bitsToBytes :: Integral a => a -> Bytes
bitsToBytes n = Bytes ( (fromIntegral n + 7) `div` 8 )

type Addr = Bytes
type Size = Bytes
type Offset = Bytes

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
  | Array Word64 v
  | Struct (Vector (Field v))
  deriving (Eq, Ord, Show, Typeable)

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
      Array n tp -> showString "arrayType " . shows n . showString " " . showsPrec 10 tp
      Struct v -> showString "mkStruct " . shows (V.toList (fldFn <$> v))
        where fldFn f = (f^.fieldVal, fieldPad f)

mkType :: TypeF Type -> Type
mkType tf = Type tf $
  case tf of
    Bitvector w -> w
    Float -> 4
    Double -> 8
    Array n e -> (Bytes n) * typeSize e
    Struct flds -> assert (V.length flds > 0) (fieldEnd (V.last flds))

bitvectorType :: Bytes -> Type
bitvectorType w = Type (Bitvector w) w

floatType :: Type
floatType = mkType Float

doubleType :: Type
doubleType = mkType Double

arrayType :: Word64 -> Type -> Type
arrayType n e = Type (Array n e) ((Bytes n) * typeSize e)

structType :: V.Vector (Field Type) -> Type
structType flds = assert (V.length flds > 0) $
  Type (Struct flds) (fieldEnd (V.last flds))

mkStruct :: V.Vector (Type,Bytes) -> Type
mkStruct l = structType (evalState (traverse fldFn l) 0)
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
    Array n etp -> typeEnd (a + Bytes (n-1) * (typeSize etp)) etp
    Struct flds -> typeEnd (a + fieldOffset f) (f^.fieldVal)
      where f = V.last flds

-- | Returns end of field including padding bytes.
fieldEnd :: Field Type -> Bytes
fieldEnd f = fieldOffset f + typeSize (f^.fieldVal) + fieldPad f
