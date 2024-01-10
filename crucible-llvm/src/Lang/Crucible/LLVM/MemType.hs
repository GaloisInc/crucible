------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemType
-- Description      : Basic datatypes for describing LLVM types
-- Copyright        : (c) Galois, Inc 2011-2013
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.MemType
  ( -- * Type information.
    SymType(..)
  , MemType(..)
  , memTypeAlign
  , memTypeSize
  , ppSymType
  , ppMemType
  , memTypeBitwidth
  , isPointerMemType
    -- ** Function type information.
  , FunDecl(..)
  , RetType
  , voidFunDecl
  , funDecl
  , varArgsFunDecl
  , ppFunDecl
  , ppRetType
    -- ** Struct type information.
  , StructInfo
  , siIsPacked
  , mkStructInfo
  , siFieldCount
  , FieldInfo
  , fiOffset
  , fiType
  , fiPadding
  , siFieldInfo
  , siFieldTypes
  , siFieldOffset
  , siFields
  , siIndexOfOffset
    -- ** Common memory types.
  , i1, i8, i16, i32, i64
  , i8p, i16p, i32p, i64p
    -- * Re-exports
  , L.Ident(..)
  , ppIdent
  ) where

import Control.Lens
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural
import qualified Text.LLVM as L
import Prettyprinter

import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.PrettyPrint as LPP
import Lang.Crucible.LLVM.PrettyPrint hiding (ppIdent, ppType)
import Lang.Crucible.Panic ( panic )

-- | Performs a binary search on a range of ints.
binarySearch :: (Int -> Ordering)
             -> Int -- ^ Lower bound (included in range)
             -> Int -- ^ Upper bound (excluded from range)
             -> Maybe Int
binarySearch f = go
  where go l h | l == h = Nothing
               | otherwise = case f i of
                               -- Index is less than one f is searching for
                               LT -> go (i+1) h
                               EQ -> Just i
                               -- Index is greater than one f is searching for.
                               GT -> go l i
          where i = l + (h - l) `div` 2

ppIdent :: L.Ident -> Doc ann
ppIdent = viaShow . LPP.ppIdent
-- TODO: update if llvm-pretty switches to prettyprinter

-- | LLVM types supported by symbolic simulator.
data SymType
  = MemType MemType
  | Alias L.Ident
  | FunType FunDecl
  | VoidType
    -- | A type that LLVM does not know the structure of such as
    -- a struct that is declared, but not defined.
  | OpaqueType
    -- | A type not supported by the symbolic simulator.
  | UnsupportedType L.Type
  deriving (Eq, Ord)

instance Show SymType where
  show = show . ppSymType

instance Pretty SymType where
  pretty = ppSymType

-- | Pretty-print a 'SymType'.
ppSymType :: SymType -> Doc ann
ppSymType (MemType tp) = ppMemType tp
ppSymType (Alias i) = ppIdent i
ppSymType (FunType d) = ppFunDecl d
ppSymType VoidType = pretty "void"
ppSymType OpaqueType = pretty "opaque"
ppSymType (UnsupportedType tp) = viaShow (LPP.ppType tp)
-- TODO: update if llvm-pretty switches to prettyprinter

-- | LLVM types supported by simulator with a defined size and alignment.
data MemType
  = IntType Natural
  | PtrType SymType
    -- ^ A pointer with an explicit pointee type, corresponding to LLVM's
    -- 'L.PtrTo'.
  | PtrOpaqueType
    -- ^ An opaque pointer type, corresponding to LLVM's 'L.PtrOpaque'.
  | FloatType
  | DoubleType
  | X86_FP80Type
  | ArrayType Natural MemType
  | VecType Natural MemType
  | StructType StructInfo
  | MetadataType
  deriving (Eq, Ord)

instance Show MemType where
  show = show . ppMemType

instance Pretty MemType where
  pretty = ppMemType

-- | Pretty-print a 'MemType'.
ppMemType :: MemType -> Doc ann
ppMemType mtp =
  case mtp of
    IntType w -> ppIntType w
    FloatType -> pretty "float"
    DoubleType -> pretty "double"
    X86_FP80Type -> pretty "long double"
    PtrType tp -> ppPtrType (ppSymType tp)
    PtrOpaqueType -> pretty "ptr"
    ArrayType n tp -> ppArrayType n (ppMemType tp)
    VecType n tp  -> ppVectorType n (ppMemType tp)
    StructType si -> ppStructInfo si
    MetadataType -> pretty "metadata"

-- | 1-bit integer type.
i1 :: MemType
i1 = IntType 1

-- | 8-bit integer type.
i8 :: MemType
i8 = IntType 8

-- | 16-bit integer type.
i16 :: MemType
i16 = IntType 16

-- | 32-bit integer type.
i32 :: MemType
i32 = IntType 32

-- | 64-bit integer type.
i64 :: MemType
i64 = IntType 64

-- | Pointer to 8-bit integer.
i8p :: MemType
i8p = PtrType (MemType i8)

-- | Pointer to 16-bit integer.
i16p :: MemType
i16p = PtrType (MemType i16)

-- | Pointer to 32-bit integer.
i32p :: MemType
i32p = PtrType (MemType i32)

-- | Pointer to 64-bit integer.
i64p :: MemType
i64p = PtrType (MemType i64)

-- | An LLVM function type.
data FunDecl = FunDecl { fdRetType  :: !RetType
                       , fdArgTypes :: ![MemType]
                       , fdVarArgs  :: !Bool
                       }
 deriving (Eq, Ord)

-- | Return the number of bits that represent the given memtype, which
--   must be either integer types, floating point types or vectors of
--   the same.
memTypeBitwidth :: MemType -> Maybe Natural
memTypeBitwidth (IntType w)  = Just w
memTypeBitwidth FloatType    = Just 32
memTypeBitwidth DoubleType   = Just 64
memTypeBitwidth X86_FP80Type = Just 80
memTypeBitwidth (VecType n tp) = (fromIntegral n *) <$> memTypeBitwidth tp
memTypeBitwidth _ = Nothing

-- | Returns 'True' if this is a pointer type.
isPointerMemType :: MemType -> Bool
isPointerMemType (PtrType _)   = True
isPointerMemType PtrOpaqueType = True
isPointerMemType _             = False

-- | Return type if any.
type RetType = Maybe MemType

-- | Declare function that returns void.
voidFunDecl :: [MemType] -> FunDecl
voidFunDecl tps = FunDecl { fdRetType = Nothing
                          , fdArgTypes = tps
                          , fdVarArgs = False
                          }

-- | Declare function that returns a value.
funDecl :: MemType -> [MemType] -> FunDecl
funDecl rtp tps = FunDecl { fdRetType = Just rtp
                          , fdArgTypes = tps
                          , fdVarArgs = False
                          }

-- | Declare function that returns a value.
varArgsFunDecl :: MemType -> [MemType] -> FunDecl
varArgsFunDecl rtp tps = FunDecl { fdRetType = Just rtp
                                 , fdArgTypes = tps
                                 , fdVarArgs = True
                                 }

-- | Pretty-print a function type.
ppFunDecl :: FunDecl -> Doc ann
ppFunDecl (FunDecl rtp args va) = rdoc <> parens (commas (fmap ppMemType args ++ vad))
  where rdoc = maybe (pretty "void") ppMemType rtp
        vad = if va then [pretty "..."] else []

-- | Pretty print a return type.
ppRetType :: RetType -> Doc ann
ppRetType = maybe (pretty "void") ppMemType

-- | Returns size of a 'MemType' in bytes.
memTypeSize :: DataLayout -> MemType -> Bytes
memTypeSize dl mtp =
  case mtp of
    IntType w -> intWidthSize w
    FloatType -> 4
    DoubleType -> 8
    X86_FP80Type -> 10
    PtrType{} -> dl ^. ptrSize
    PtrOpaqueType{} -> dl ^. ptrSize
    ArrayType n tp -> natBytesMul n (memTypeSize dl tp)
    VecType n tp -> natBytesMul n (memTypeSize dl tp)
    StructType si -> structSize si
    MetadataType -> 0

memTypeSizeInBits :: DataLayout -> MemType -> Natural
memTypeSizeInBits dl tp = bytesToBits (memTypeSize dl tp)

-- | Returns ABI byte alignment constraint in bytes.
memTypeAlign :: DataLayout -> MemType -> Alignment
memTypeAlign dl mtp =
  case mtp of
    IntType w -> integerAlignment dl (fromIntegral w)
    FloatType -> case floatAlignment dl 32 of
                   Just a -> a
                   Nothing -> panic "crucible-llvm:memTypeAlign.float32"
                              [ "Invalid 32-bit float alignment from datalayout" ]
    DoubleType -> case floatAlignment dl 64 of
                    Just a -> a
                    Nothing -> panic "crucible-llvm:memTypeAlign.float64"
                               [ "Invalid 64-bit float alignment from datalayout" ]
    X86_FP80Type -> case floatAlignment dl 80 of
                      Just a -> a
                      Nothing -> panic "crucible-llvm:memTypeAlign.float80"
                                 [ "Invalid 80-bit float alignment from datalayout" ]
    PtrType{} -> dl ^. ptrAlign
    PtrOpaqueType{} -> dl ^. ptrAlign
    ArrayType _ tp -> memTypeAlign dl tp
    VecType _n _tp -> vectorAlignment dl (memTypeSizeInBits dl mtp)
    StructType si  -> structAlign si
    MetadataType   -> noAlignment

-- | Information about size, alignment, and fields of a struct.
data StructInfo = StructInfo
  { siIsPacked   :: !Bool
  , structSize   :: !Bytes -- ^ Size in bytes.
  , structAlign  :: !Alignment
  , siFields     :: !(V.Vector FieldInfo)
  }
  deriving (Eq, Ord, Show)

data FieldInfo = FieldInfo
  { fiOffset    :: !Offset  -- ^ Byte offset of field relative to start of struct.
  , fiType      :: !MemType -- ^ Type of field.
  , fiPadding   :: !Bytes   -- ^ Number of bytes of padding at end of field.
  }
  deriving (Eq, Ord, Show)


-- | Constructs a function for obtaining target-specific size/alignment
-- information about structs.  The function produced corresponds to the
-- @StructLayout@ object constructor in TargetData.cpp.
mkStructInfo :: DataLayout
             -> Bool -- ^ @True@ = packed, @False@ = unpacked
             -> [MemType] -- ^ Field types
             -> StructInfo
mkStructInfo dl packed tps0 = go [] 0 a0 tps0
  where a0 | packed    = noAlignment
           | otherwise = nextAlign noAlignment tps0 `max` aggregateAlignment dl
        -- Padding after each field depends on the alignment of the
        -- type of the next field, if there is one. Padding after the
        -- last field depends on the alignment of the whole struct
        -- (i.e. the maximum alignment of any field). Alignment value
        -- of n means to align on 2^n byte boundaries.
        nextAlign :: Alignment -> [MemType] -> Alignment
        nextAlign _ _ | packed = noAlignment
        nextAlign maxAlign [] = maxAlign
        nextAlign _ (tp:_) = memTypeAlign dl tp

        -- Process fields
        go :: [FieldInfo] -- ^ Fields so far in reverse order.
           -> Bytes       -- ^ Total size so far (aligned to next element)
           -> Alignment   -- ^ Maximum alignment so far
           -> [MemType]   -- ^ Field types to process
           -> StructInfo

        go flds sz maxAlign (tp:tpl) =
          go (fi:flds) sz' (max maxAlign fieldAlign) tpl

          where
            fi = FieldInfo
                   { fiOffset  = sz
                   , fiType    = tp
                   , fiPadding = sz' - e
                   }

            -- End of field for tp
            e = sz + memTypeSize dl tp

            -- Alignment of next field
            fieldAlign = nextAlign maxAlign tpl

            -- Size of field at alignment for next thing.
            sz' = padToAlignment e fieldAlign

        go flds sz maxAlign [] =
            StructInfo { siIsPacked = packed
                       , structSize = sz
                       , structAlign = maxAlign
                       , siFields = V.fromList (reverse flds)
                       }

-- | The types of a struct type's fields.
siFieldTypes :: StructInfo -> Vector MemType
siFieldTypes si = fiType <$> siFields si

-- | Number of fields in a struct type.
siFieldCount :: StructInfo -> Int
siFieldCount = V.length . siFields

-- | Returns information for field with given index, if it is defined.
siFieldInfo :: StructInfo -> Int -> Maybe FieldInfo
siFieldInfo si i = siFields si V.!? i

-- | Returns offset of field with given index, if it is defined.
siFieldOffset :: StructInfo -> Int -> Maybe Offset
siFieldOffset si i = fiOffset <$> siFieldInfo si i

-- | Returns index of field at the given byte offset (if any).
siIndexOfOffset :: StructInfo -> Offset -> Maybe Int
siIndexOfOffset si o = binarySearch f 0 (V.length flds)
  where flds = siFields si
        f i | e <= o = LT -- Index too low if field ends before offset.
            | o < s  = GT -- Index too high if field starts after offset.
            | otherwise = EQ
         where s = fiOffset (flds V.! i)
               e | i+1 == V.length flds = structSize si
                 | otherwise = fiOffset (flds V.! i)

commas :: [Doc ann] -> Doc ann
commas = hsep . punctuate (pretty ',')

structBraces :: Bool -> Doc ann -> Doc ann
structBraces False b = pretty '{' <+> b <+> pretty '}'
structBraces True  b = pretty "<{" <+> b <+> pretty "}>"

-- | Pretty print struct info.
ppStructInfo :: StructInfo -> Doc ann
ppStructInfo si = structBraces (siIsPacked si) $ commas (V.toList fields)
  where fields = ppMemType <$> siFieldTypes si
