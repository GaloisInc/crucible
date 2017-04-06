------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.DataLayout
-- Description      : Basic datatypes for describing memory layout and alignment
-- Copyright        : (c) Galois, Inc 2011-2013
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.LLVM.DataLayout
  ( Size
  , Offset
  , Alignment
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
import Data.Word (Word32, Word64)
import qualified Text.LLVM as L

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
import Data.Monoid (Monoid(..))
#endif

import Lang.MATLAB.Utils.Nat
import Lang.Crucible.Utils.Arithmetic


------------------------------------------------------------------------
-- Data layout

-- | Size is in bytes unless bits is explicitly stated.
type Size = Word64

type Offset = Word64

-- | Alignments must be a power of two, so we just store the exponent.
-- e.g., alignment value of 3 indicates the pointer must align on 2^3-byte boundaries.
type Alignment = Word32

newtype AlignInfo = AT (Map Nat Alignment)
  deriving (Eq)

-- | Make alignment info containing no alignments.
emptyAlignInfo :: AlignInfo
emptyAlignInfo = AT Map.empty

-- | Return alignment exactly at point if any.
findExact :: Nat -> AlignInfo -> Maybe Alignment
findExact w (AT t) = Map.lookup w t

-- | Get alignment for the integer type of the specified bitwidth,
-- using LLVM's rules for integer types: "If no match is found, and
-- the type sought is an integer type, then the smallest integer type
-- that is larger than the bitwidth of the sought type is used. If
-- none of the specifications are larger than the bitwidth then the
-- largest integer type is used."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
integerAlignment :: DataLayout -> Nat -> Alignment
integerAlignment dl w =
  case Map.lookupGE w t of
    Just (_, a) -> a
    Nothing ->
      case Map.toDescList t of
        ((_, a) : _) -> a
        _ -> 0
  where AT t = dl^.integerInfo

-- | Get alignment for a vector type of the specified bitwidth, using
-- LLVM's rules for vector types: "If no match is found, and the type
-- sought is a vector type, then the largest vector type that is
-- smaller than the sought vector type will be used as a fall back."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
vectorAlignment :: DataLayout -> Nat -> Alignment
vectorAlignment dl w =
  case Map.lookupLE w t of
    Just (_, a) -> a
    Nothing -> 0
  where AT t = dl^.vectorInfo

-- | Get alignment for a float type of the specified bitwidth.
floatAlignment :: DataLayout -> Nat -> Maybe Alignment
floatAlignment dl w = Map.lookup w t
  where AT t = dl^.floatInfo

-- | Get the basic alignment for aggregate types.
aggregateAlignment :: DataLayout -> Alignment
aggregateAlignment dl = dl^.aggAlign

-- | Return maximum alignment constraint stored in tree.
maxAlignmentInTree :: AlignInfo -> Alignment
maxAlignmentInTree (AT t) = foldrOf folded max 0 t

-- | Update alignment tree
updateAlign :: Nat
            -> AlignInfo
            -> Maybe Alignment
            -> AlignInfo
updateAlign w (AT t) ma = AT (Map.alter (const ma) w t)

type instance Index AlignInfo = Nat
type instance IxValue AlignInfo = Alignment

instance Ixed AlignInfo where
  ix k = at k . traverse

instance At AlignInfo where
  at k f m = updateAlign k m <$> indexed f k (findExact k m)

-- | Flags byte orientation of target machine.
data EndianForm = BigEndian | LittleEndian
  deriving (Eq)

-- | Parsed data layout
data DataLayout
   = DL { _intLayout      :: EndianForm
        , _stackAlignment :: !Alignment
        , _ptrSize        :: !Size
        , _ptrAlign       :: !Alignment
        , _aggAlign       :: !Alignment
        , _integerInfo    :: !AlignInfo
        , _vectorInfo     :: !AlignInfo
        , _floatInfo      :: !AlignInfo
        , _stackInfo      :: !AlignInfo
        , _layoutWarnings :: [L.LayoutSpec]
        }

instance Show DataLayout where
   show _ = "<<DataLayout>>"

intLayout :: Simple Lens DataLayout EndianForm
intLayout = lens _intLayout (\s v -> s { _intLayout = v})

stackAlignment :: Simple Lens DataLayout Alignment
stackAlignment = lens _stackAlignment (\s v -> s { _stackAlignment = v})

-- | Size of pointers in bytes.
ptrSize :: Simple Lens DataLayout Size
ptrSize = lens _ptrSize (\s v -> s { _ptrSize = v})

-- | ABI pointer alignment in bytes.
ptrAlign :: Simple Lens DataLayout Alignment
ptrAlign = lens _ptrAlign (\s v -> s { _ptrAlign = v})

integerInfo :: Simple Lens DataLayout AlignInfo
integerInfo = lens _integerInfo (\s v -> s { _integerInfo = v})

vectorInfo :: Simple Lens DataLayout AlignInfo
vectorInfo = lens _vectorInfo (\s v -> s { _vectorInfo = v})

floatInfo :: Simple Lens DataLayout AlignInfo
floatInfo = lens _floatInfo (\s v -> s { _floatInfo = v})

-- | Information about aggregate alignment.
aggAlign :: Simple Lens DataLayout Alignment
aggAlign = lens _aggAlign (\s v -> s { _aggAlign = v})

-- | Layout constraints on a stack object with the given size.
stackInfo :: Simple Lens DataLayout AlignInfo
stackInfo = lens _stackInfo (\s v -> s { _stackInfo = v})

-- | Layout specs that could not be parsed.
layoutWarnings :: Simple Lens DataLayout [L.LayoutSpec]
layoutWarnings = lens _layoutWarnings (\s v -> s { _layoutWarnings = v})

ptrBitwidth :: DataLayout -> Nat
ptrBitwidth dl = 8 * fromIntegral (dl^.ptrSize)

-- | Reduce the bit level alignment to a byte value, and error if it is not
-- a multiple of 8.
fromBits :: Int -> Either String Alignment
fromBits a | w <= 0 = Left $ "Alignment must be a positive number."
           | r /= 0 = Left $ "Alignment specification must occupy a byte boundary."
           | not (isPow2 w) = Left $ "Alignment must be a power of two."
           | otherwise = Right $ fromIntegral (lg w)
  where (w,r) = toInteger a `divMod` 8

-- | Insert alignment into spec.
setAt :: Simple Lens DataLayout AlignInfo -> Nat -> Alignment -> State DataLayout ()
setAt f sz a = f . at sz ?= a

-- | The default data layout if no spec is defined. From the LLVM
-- Language Reference: "When constructing the data layout for a given
-- target, LLVM starts with a default set of specifications which are
-- then (possibly) overridden by the specifications in the datalayout
-- keyword." <http://llvm.org/docs/LangRef.html#langref-datalayout>
defaultDataLayout :: DataLayout
defaultDataLayout = execState defaults dl
  where dl = DL { _intLayout      = BigEndian
                , _stackAlignment = 1
                , _ptrSize        = 8 -- 64 bit pointers = 8 bytes
                , _ptrAlign       = 3 -- 64 bit alignment: 2^3=8 byte boundaries
                , _aggAlign       = 0 -- 8 bit alignment: 1-byte boundaries
                , _integerInfo    = emptyAlignInfo
                , _floatInfo      = emptyAlignInfo
                , _vectorInfo     = emptyAlignInfo
                , _stackInfo      = emptyAlignInfo
                , _layoutWarnings = []
                }
        defaults = do
          -- Default integer alignments
          setAt integerInfo  1 0 -- 1-bit values aligned on byte addresses.
          setAt integerInfo  8 0 -- 8-bit values aligned on byte addresses.
          setAt integerInfo 16 1 -- 16-bit values aligned on 2 byte addresses.
          setAt integerInfo 32 2 -- 32-bit values aligned on 4 byte addresses.
          setAt integerInfo 64 2 -- 64-bit values aligned on 4 byte addresses.
          -- Default float alignments
          setAt floatInfo  16 1 -- Half is aligned on 2 byte addresses.
          setAt floatInfo  32 2 -- Float is aligned on 4 byte addresses.
          setAt floatInfo  64 3 -- Double is aligned on 8 byte addresses.
          setAt floatInfo 128 4 -- Quad is aligned on 16 byte addresses.
          -- Default vector alignments.
          setAt vectorInfo  64 3 -- 64-bit vector is 8 byte aligned.
          setAt vectorInfo 128 4  -- 128-bit vector is 16 byte aligned.

-- | Maximum alignment for any type (used by malloc).
maxAlignment :: DataLayout -> Alignment
maxAlignment dl =
  maximum [ dl^.stackAlignment
          , dl^.ptrAlign
          , dl^.aggAlign
          , maxAlignmentInTree (dl^.integerInfo)
          , maxAlignmentInTree (dl^.vectorInfo)
          , maxAlignmentInTree (dl^.floatInfo)
          , maxAlignmentInTree (dl^.stackInfo)
          ]

fromSize :: Int -> Nat
fromSize i | i < 0 = error $ "Negative size given in data layout."
           | otherwise = fromIntegral i

-- | Insert alignment into spec.
setAtBits :: Simple Lens DataLayout AlignInfo -> L.LayoutSpec -> Int -> Int -> State DataLayout ()
setAtBits f spec sz a =
  case fromBits a of
    Left{} -> layoutWarnings %= (spec:)
    Right w -> f . at (fromSize sz) .= Just w

-- | Insert alignment into spec.
setBits :: Simple Lens DataLayout Alignment -> L.LayoutSpec -> Int -> State DataLayout ()
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
      L.PointerSize _n sz a _ ->
         case fromBits a of
           Right a' | r == 0 -> do ptrSize .= w
                                   ptrAlign .= a'
           _ -> layoutWarnings %= (ls:)
       where (w,r) = fromIntegral sz `divMod` 8
      L.IntegerSize    sz a _ -> setAtBits integerInfo ls sz a
      L.VectorSize     sz a _ -> setAtBits vectorInfo  ls sz a
      L.FloatSize      sz a _ -> setAtBits floatInfo   ls sz a
      L.StackObjSize   sz a _ -> setAtBits stackInfo   ls sz a
      L.NativeIntSize _ -> return ()
      L.AggregateSize a _ -> setBits aggAlign ls a
      L.StackAlign a    -> setBits stackAlignment ls a
      L.Mangling _      -> return ()

-- | Create parsed data layout from layout spec AST.
parseDataLayout :: L.DataLayout -> DataLayout
parseDataLayout dl =
  execState (mapM_ addLayoutSpec dl) defaultDataLayout

-- | The size of an integer of the given bitwidth, in bytes.
intWidthSize :: Nat -> Size
intWidthSize w = (fromIntegral w + 7) `div` 8
