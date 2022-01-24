------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.DataLayout
-- Description      : Basic datatypes for describing memory layout and alignment
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.DataLayout
  ( -- * Alignments
    Alignment
  , noAlignment
  , padToAlignment
  , toAlignment
  , fromAlignment
  , exponentToAlignment
  , alignmentToExponent
    -- * Data layout declarations.
  , DataLayout
  , EndianForm(..)
  , intLayout
  , maxAlignment
  , ptrSize
  , ptrAlign
  , ptrBitwidth
  , defaultDataLayout
  , parseDataLayout
  , integerAlignment
  , vectorAlignment
  , floatAlignment
  , aggregateAlignment
  , intWidthSize
  ) where

import Control.Lens
import Control.Monad.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Word (Word32)
import qualified Text.LLVM as L
import Numeric.Natural

import What4.Utils.Arithmetic
import Lang.Crucible.LLVM.Bytes


------------------------------------------------------------------------
-- Data layout

-- | An @Alignment@ represents a number of bytes that must be a power of two.
newtype Alignment = Alignment Word32
  deriving (Eq, Ord, Show)
-- The representation just stores the exponent. E.g., @Alignment 3@
-- indicates alignment to a 2^3-byte boundary.

-- | 1-byte alignment, which is the minimum possible.
noAlignment :: Alignment
noAlignment = Alignment 0

-- | @padToAlignment x a@ returns the smallest value greater than or
-- equal to @x@ that is aligned to @a@.
padToAlignment :: Bytes -> Alignment -> Bytes
padToAlignment x (Alignment n) = toBytes (nextPow2Multiple (bytesToNatural x) (fromIntegral n))

-- | Convert a number of bytes into an alignment, if it is a power of 2.
toAlignment :: Bytes -> Maybe Alignment
toAlignment (Bytes x)
  | isPow2 x = Just (Alignment (fromIntegral (lg x)))
  | otherwise = Nothing

-- | Convert an alignment to a number of bytes.
fromAlignment :: Alignment -> Bytes
fromAlignment (Alignment n) = Bytes (2 ^ n)

-- | Convert an exponent @n@ to an alignment of @2^n@ bytes.
exponentToAlignment :: Natural -> Alignment
exponentToAlignment n = Alignment (fromIntegral n)

alignmentToExponent :: Alignment -> Natural
alignmentToExponent (Alignment n) = fromIntegral n

newtype AlignInfo = AT (Map Natural Alignment)
  deriving (Eq, Ord)

-- | Make alignment info containing no alignments.
emptyAlignInfo :: AlignInfo
emptyAlignInfo = AT Map.empty

-- | Return alignment exactly at point if any.
findExact :: Natural -> AlignInfo -> Maybe Alignment
findExact w (AT t) = Map.lookup w t

-- | Get alignment for the integer type of the specified bitwidth,
-- using LLVM's rules for integer types: "If no match is found, and
-- the type sought is an integer type, then the smallest integer type
-- that is larger than the bitwidth of the sought type is used. If
-- none of the specifications are larger than the bitwidth then the
-- largest integer type is used."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
integerAlignment :: DataLayout -> Natural -> Alignment
integerAlignment dl w =
  case Map.lookupGE w t of
    Just (_, a) -> a
    Nothing ->
      case Map.toDescList t of
        ((_, a) : _) -> a
        _ -> noAlignment
  where AT t = dl^.integerInfo

-- | Get alignment for a vector type of the specified bitwidth, using
-- LLVM's rules for vector types: "If no match is found, and the type
-- sought is a vector type, then the largest vector type that is
-- smaller than the sought vector type will be used as a fall back."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
vectorAlignment :: DataLayout -> Natural -> Alignment
vectorAlignment dl w =
  case Map.lookupLE w t of
    Just (_, a) -> a
    Nothing -> noAlignment
  where AT t = dl^.vectorInfo

-- | Get alignment for a float type of the specified bitwidth.
floatAlignment :: DataLayout -> Natural -> Maybe Alignment
floatAlignment dl w = Map.lookup w t
  where AT t = dl^.floatInfo

-- | Get the basic alignment for aggregate types.
aggregateAlignment :: DataLayout -> Alignment
aggregateAlignment dl =
  fromMaybe noAlignment (findExact 0 (dl^.aggInfo))

-- | Return maximum alignment constraint stored in tree.
maxAlignmentInTree :: AlignInfo -> Alignment
maxAlignmentInTree (AT t) = foldrOf folded max noAlignment t

-- | Update alignment tree
updateAlign :: Natural
            -> AlignInfo
            -> Maybe Alignment
            -> AlignInfo
updateAlign w (AT t) ma = AT (Map.alter (const ma) w t)

type instance Index AlignInfo = Natural
type instance IxValue AlignInfo = Alignment

instance Ixed AlignInfo where
  ix k = at k . traverse

instance At AlignInfo where
  at k f m = updateAlign k m <$> indexed f k (findExact k m)

-- | Flags byte orientation of target machine.
data EndianForm = BigEndian | LittleEndian
  deriving (Eq, Ord, Show)

-- | Parsed data layout
data DataLayout
   = DL { _intLayout :: EndianForm
        , _stackAlignment :: !Alignment
        , _ptrSize     :: !Bytes
        , _ptrAlign    :: !Alignment
        , _integerInfo :: !AlignInfo
        , _vectorInfo  :: !AlignInfo
        , _floatInfo   :: !AlignInfo
        , _aggInfo     :: !AlignInfo
        , _stackInfo   :: !AlignInfo
        , _layoutWarnings :: [L.LayoutSpec]
        }
  deriving (Eq, Ord)

instance Show DataLayout where
   show _ = "<<DataLayout>>"

intLayout :: Lens' DataLayout EndianForm
intLayout = lens _intLayout (\s v -> s { _intLayout = v})

stackAlignment :: Lens' DataLayout Alignment
stackAlignment = lens _stackAlignment (\s v -> s { _stackAlignment = v})

-- | Size of pointers in bytes.
ptrSize :: Lens' DataLayout Bytes
ptrSize = lens _ptrSize (\s v -> s { _ptrSize = v})

-- | ABI pointer alignment in bytes.
ptrAlign :: Lens' DataLayout Alignment
ptrAlign = lens _ptrAlign (\s v -> s { _ptrAlign = v})

integerInfo :: Lens' DataLayout AlignInfo
integerInfo = lens _integerInfo (\s v -> s { _integerInfo = v})

vectorInfo :: Lens' DataLayout AlignInfo
vectorInfo = lens _vectorInfo (\s v -> s { _vectorInfo = v})

floatInfo :: Lens' DataLayout AlignInfo
floatInfo = lens _floatInfo (\s v -> s { _floatInfo = v})

-- | Information about aggregate size.
aggInfo :: Lens' DataLayout AlignInfo
aggInfo = lens _aggInfo (\s v -> s { _aggInfo = v})

-- | Layout constraints on a stack object with the given size.
stackInfo :: Lens' DataLayout AlignInfo
stackInfo = lens _stackInfo (\s v -> s { _stackInfo = v})

-- | Layout specs that could not be parsed.
layoutWarnings :: Lens' DataLayout [L.LayoutSpec]
layoutWarnings = lens _layoutWarnings (\s v -> s { _layoutWarnings = v})

ptrBitwidth :: DataLayout -> Natural
ptrBitwidth dl = bytesToBits (dl^.ptrSize)

-- | Reduce the bit level alignment to a byte value, and error if it is not
-- a multiple of 8.
fromBits :: Int -> Either String Alignment
fromBits a | w <= 0 = Left $ "Alignment must be a positive number."
           | r /= 0 = Left $ "Alignment specification must occupy a byte boundary."
           | not (isPow2 w) = Left $ "Alignment must be a power of two."
           | otherwise = Right $ Alignment (fromIntegral (lg w))
  where (w,r) = toInteger a `divMod` 8

-- | Insert alignment into spec.
setAt :: Lens' DataLayout AlignInfo -> Natural -> Alignment -> State DataLayout ()
setAt f sz a = f . at sz ?= a

-- | The default data layout if no spec is defined. From the LLVM
-- Language Reference: "When constructing the data layout for a given
-- target, LLVM starts with a default set of specifications which are
-- then (possibly) overridden by the specifications in the datalayout
-- keyword." <http://llvm.org/docs/LangRef.html#langref-datalayout>
defaultDataLayout :: DataLayout
defaultDataLayout = execState defaults dl
  where dl = DL { _intLayout = BigEndian
                , _stackAlignment = noAlignment
                , _ptrSize  = 8 -- 64 bit pointers = 8 bytes
                , _ptrAlign = Alignment 3 -- 64 bit alignment: 2^3=8 byte boundaries
                , _integerInfo = emptyAlignInfo
                , _floatInfo   = emptyAlignInfo
                , _vectorInfo  = emptyAlignInfo
                , _aggInfo     = emptyAlignInfo
                , _stackInfo   = emptyAlignInfo
                , _layoutWarnings = []
                }
        defaults = do
          -- Default integer alignments
          setAt integerInfo  1 noAlignment -- 1-bit values aligned on byte addresses.
          setAt integerInfo  8 noAlignment -- 8-bit values aligned on byte addresses.
          setAt integerInfo 16 (Alignment 1) -- 16-bit values aligned on 2 byte addresses.
          setAt integerInfo 32 (Alignment 2) -- 32-bit values aligned on 4 byte addresses.
          setAt integerInfo 64 (Alignment 3) -- 64-bit values aligned on 8 byte addresses.
          -- Default float alignments
          setAt floatInfo  16 (Alignment 1) -- Half is aligned on 2 byte addresses.
          setAt floatInfo  32 (Alignment 2) -- Float is aligned on 4 byte addresses.
          setAt floatInfo  64 (Alignment 3) -- Double is aligned on 8 byte addresses.
          setAt floatInfo 128 (Alignment 4) -- Quad is aligned on 16 byte addresses.
          -- Default vector alignments.
          setAt vectorInfo  64 (Alignment 3) -- 64-bit vector is 8 byte aligned.
          setAt vectorInfo 128 (Alignment 4) -- 128-bit vector is 16 byte aligned.
          -- Default aggregate alignments.
          setAt aggInfo  0 noAlignment  -- Aggregates are 1-byte aligned.

-- | Maximum alignment for any type (used by malloc).
maxAlignment :: DataLayout -> Alignment
maxAlignment dl =
  maximum [ dl^.stackAlignment
          , dl^.ptrAlign
          , maxAlignmentInTree (dl^.integerInfo)
          , maxAlignmentInTree (dl^.vectorInfo)
          , maxAlignmentInTree (dl^.floatInfo)
          , maxAlignmentInTree (dl^.aggInfo)
          , maxAlignmentInTree (dl^.stackInfo)
          ]

fromSize :: Int -> Natural
fromSize i | i < 0 = error $ "Negative size given in data layout."
           | otherwise = fromIntegral i

-- | Insert alignment into spec.
setAtBits :: Lens' DataLayout AlignInfo -> L.LayoutSpec -> Int -> Int -> State DataLayout ()
setAtBits f spec sz a =
  case fromBits a of
    Left{} -> layoutWarnings %= (spec:)
    Right w -> f . at (fromSize sz) .= Just w

-- | Insert alignment into spec.
setBits :: Lens' DataLayout Alignment -> L.LayoutSpec -> Int -> State DataLayout ()
setBits f spec a =
  case fromBits a of
    Left{} -> layoutWarnings %= (spec:)
    Right w -> f .= w

-- | Add information from layout spec into parsed data layout.
addLayoutSpec :: L.LayoutSpec -> State DataLayout ()
addLayoutSpec ls =
  -- TODO: Check that sizes and alignment is using bits versus bytes consistently.
    case ls of
      L.BigEndian    -> intLayout .= BigEndian
      L.LittleEndian -> intLayout .= LittleEndian
      L.PointerSize n sz a _
           -- Currently, we assume that only default address space (0) is used.
           -- We use that address space as the sole arbiter of what pointer
           -- size to use, and we ignore all other PointerSize layout specs.
           -- See doc/limitations.md for more discussion.
        |  n == 0
        -> case fromBits a of
             Right a' | r == 0 -> do ptrSize .= fromIntegral w
                                     ptrAlign .= a'
             _ -> layoutWarnings %= (ls:)
        |  otherwise
        -> return ()
       where (w,r) = sz `divMod` 8
      L.IntegerSize    sz a _ -> setAtBits integerInfo ls sz a
      L.VectorSize     sz a _ -> setAtBits vectorInfo  ls sz a
      L.FloatSize      sz a _ -> setAtBits floatInfo   ls sz a
      L.AggregateSize  sz a _ -> setAtBits aggInfo     ls sz a
      L.StackObjSize   sz a _ -> setAtBits stackInfo   ls sz a
      L.NativeIntSize _ -> return ()
      L.StackAlign a    -> setBits stackAlignment ls a
      L.Mangling _      -> return ()

-- | Create parsed data layout from layout spec AST.
parseDataLayout :: L.DataLayout -> DataLayout
parseDataLayout dl = execState (mapM_ addLayoutSpec dl) defaultDataLayout

-- | The size of an integer of the given bitwidth, in bytes.
intWidthSize :: Natural -> Bytes
intWidthSize w = bitsToBytes w
