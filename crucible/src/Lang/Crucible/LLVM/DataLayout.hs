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
    -- * Utilities
  , structBraces
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
  , memTypeAlign
  , memTypeSize
    -- * Type information.
  , SymType(..)
  , ppSymType
    -- ** MemType
  , MemType(..)
  , ppMemType
  , i1, i8, i16, i32, i64
  , i8p, i16p, i32p, i64p
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
  , siDropLastField
    -- * Re-exports
  , L.Ident(..)
  , ppIdent
  ) where

import Control.Lens
import Control.Monad.State.Strict
import qualified Data.FingerTree as FT
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word32, Word64)
import qualified Text.LLVM as L
import qualified Text.LLVM.PP as L
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
import Data.Monoid (Monoid(..))
#endif

import Lang.MATLAB.Utils.Nat
import Lang.Crucible.LLVM.PrettyPrint
import Lang.Crucible.Utils.Arithmetic


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

------------------------------------------------------------------------
-- Data layout


ppIdent :: L.Ident -> Doc
ppIdent = text . show . L.ppIdent


-- | Size is in bytes unless bits is explicitly stated.
type Size = Word64

type Offset = Word64

-- | Alignment's must be a power of two, so we just store the exponent.
-- e.g., alignment value of 3 indicates the pointer must align on 2^3-byte boundaries.
type Alignment = Word32


newtype BW = BW Word64
  deriving (Eq, Ord, Num)

instance Monoid BW where
  mempty                = BW 0
  mappend (BW a) (BW b) = BW (max a b)

data AlignSpec =
  AlignSpec { -- Size in bits
              asBitWidth :: Nat
              -- Alignment in bytes (this is the ABI value).
            , asAlign    :: Alignment
            }
 deriving( Eq )

instance FT.Measured BW AlignSpec where
  measure = fromIntegral . asBitWidth

newtype AlignTree = AT (FT.FingerTree BW AlignSpec)
 deriving( Eq )

-- | Make alignment tree from sorted list.
emptyAlignTree :: AlignTree
emptyAlignTree = AT FT.empty

-- | Return alignment exactly at point if any.
findExact :: Nat -> AlignTree -> Maybe Alignment
findExact w (AT t) =
    case FT.viewl mge of
     e FT.:< _ | asBitWidth e == w -> Just (asAlign e)
     _ -> Nothing
  where mge = snd $ FT.split (>= fromIntegral w) t

-- | Find match for alignment using LLVM's rules for integer types.
findIntMatch :: Nat -> AlignTree -> Maybe Alignment
findIntMatch w (AT t) =
    case FT.viewl mge of
     e FT.:< _ -> Just (asAlign e)
     FT.EmptyL ->
       case FT.viewr lt of
         _ FT.:> e -> Just (asAlign e)
         FT.EmptyR -> Nothing
  where (lt, mge) = FT.split (>= fromIntegral w) t

-- | Return maximum alignment constriant stored in tree.
maxAlignmentInTree :: AlignTree -> Alignment
maxAlignmentInTree (AT t) = foldrOf folded (max . asAlign) 0 t

-- | Update alignment tree
updateAlign :: Nat
            -> AlignTree
            -> Maybe Alignment
            -> AlignTree
updateAlign w (AT t) ma = AT $
    case FT.split (> fromIntegral w) t of
      (FT.viewr -> lt FT.:> ml, gt) | asBitWidth ml == w -> merge lt gt
      (mle, gt) -> merge mle gt
  where merge l r = (FT.><) l (maybe r (\a -> AlignSpec w a FT.<| r) ma)

type instance Index AlignTree = Nat
type instance IxValue AlignTree = Alignment

instance Ixed AlignTree where
  ix k = at k . traverse

instance At AlignTree where
  at k f m = updateAlign k m <$> indexed f k (findExact k m)

-- | Flags byte orientation of target machine.
data EndianForm = BigEndian | LittleEndian
 deriving( Eq )

-- | Parsed data layout
data DataLayout
   = DL { _intLayout :: EndianForm
        , _stackAlignment :: !Alignment
        , _ptrSize     :: !Size
        , _ptrAlign    :: !Alignment
        , _integerInfo :: !AlignTree
        , _vectorInfo  :: !AlignTree
        , _floatInfo   :: !AlignTree
        , _aggInfo     :: !AlignTree
        , _stackInfo   :: !AlignTree
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

integerInfo :: Simple Lens DataLayout AlignTree
integerInfo = lens _integerInfo (\s v -> s { _integerInfo = v})

vectorInfo :: Simple Lens DataLayout AlignTree
vectorInfo = lens _vectorInfo (\s v -> s { _vectorInfo = v})

floatInfo :: Simple Lens DataLayout AlignTree
floatInfo = lens _floatInfo (\s v -> s { _floatInfo = v})

-- | Information about aggregate size.
aggInfo :: Simple Lens DataLayout AlignTree
aggInfo = lens _aggInfo (\s v -> s { _aggInfo = v})

-- | Layout constraints on a stack object with the given size.
stackInfo :: Simple Lens DataLayout AlignTree
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
setAt :: Simple Lens DataLayout AlignTree -> Nat -> Alignment -> State DataLayout ()
setAt f sz a = f . at sz ?= a

-- | Get default data layout if no spec is defined.
defaultDataLayout :: DataLayout
defaultDataLayout = execState defaults dl
  where dl = DL { _intLayout = BigEndian
                , _stackAlignment = 1
                , _ptrSize  = 8 -- 64 bit pointers = 8 bytes
                , _ptrAlign = 3 -- 64 bit alignment: 2^3=8 byte boundaries
                , _integerInfo = emptyAlignTree
                , _floatInfo   = emptyAlignTree
                , _vectorInfo  = emptyAlignTree
                , _aggInfo     = emptyAlignTree
                , _stackInfo   = emptyAlignTree
                , _layoutWarnings = []
                }
        defaults = do
          -- Default integer alignments
          setAt integerInfo  1 0 -- 1-bit values aligned on byte addresses.
          setAt integerInfo  8 0 -- 8-bit values aligned on byte addresses.
          setAt integerInfo 16 1 -- 16-bit values aligned on 2 byte addresses.
          setAt integerInfo 32 2 -- 32-bit values aligned on 4 byte addresses.
          setAt integerInfo 64 2 -- 64-bit balues aligned on 4 byte addresses.
          -- Default float alignments
          setAt floatInfo  16 1 -- Half is aligned on 2 byte addresses.
          setAt floatInfo  32 2 -- Float is aligned on 4 byte addresses.
          setAt floatInfo  64 3 -- Double is aligned on 8 byte addresses.
          setAt floatInfo 128 4 -- Quad is aligned on 16 byte addresses.
          -- Default vector alignments.
          setAt vectorInfo  64 3 -- 64-bit vector is 8 byte aligned.
          setAt vectorInfo 128 4  -- 128-bit vector is 16 byte aligned.
          -- Default aggregate alignments.
          setAt aggInfo  0 3  -- Aggregates are 8 byte aligned.

-- | Maximum aligment for any type (used by malloc).
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

fromSize :: Int -> Nat
fromSize i | i < 0 = error $ "Negative size given in data layout."
           | otherwise = fromIntegral i

-- | Insert alignment into spec.
setAtBits :: Simple Lens DataLayout AlignTree -> L.LayoutSpec -> Int -> Int -> State DataLayout ()
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
      L.PointerSize     sz a _ ->
         case fromBits a of
           Right a' | r == 0 -> do ptrSize .= w
                                   ptrAlign .= a'
           _ -> layoutWarnings %= (ls:)
       where (w,r) = fromIntegral sz `divMod` 8
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
parseDataLayout dl =
  execState (mapM_ addLayoutSpec dl) defaultDataLayout

-- | Type supported by symbolic simulator.
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
 deriving( Eq )

instance Show SymType where
  show = show . ppSymType

ppSymType :: SymType -> Doc
ppSymType (MemType tp) = ppMemType tp
ppSymType (Alias i) = ppIdent i
ppSymType (FunType d) = ppFunDecl d
ppSymType VoidType = text "void"
ppSymType OpaqueType = text "opaque"
ppSymType (UnsupportedType tp) = text (show (L.ppType tp))

-- | LLVM Types supported by simulator with a defined size and alignment.
data MemType
  = IntType Nat
  | PtrType SymType
  | FloatType
  | DoubleType
  | ArrayType Int MemType
  | VecType Int MemType
  | StructType StructInfo
  | MetadataType
 deriving (Eq)

instance Show MemType where
  show = show . ppMemType

ppMemType :: MemType -> Doc
ppMemType mtp =
  case mtp of
    IntType w -> ppIntType w
    FloatType -> text "float"
    DoubleType -> text "double"
    PtrType tp -> ppPtrType (ppSymType tp)
    ArrayType n tp -> ppArrayType n (ppMemType tp)
    VecType n tp  -> ppVectorType n (ppMemType tp)
    StructType si -> ppStructInfo si
    MetadataType -> text "metadata"

i1, i8, i16, i32, i64 :: MemType
i1     = IntType 1
i8     = IntType 8
i16    = IntType 16
i32    = IntType 32
i64    = IntType 64

i8p, i16p, i32p, i64p :: MemType
i8p    = PtrType (MemType i8)
i16p   = PtrType (MemType i16)
i32p   = PtrType (MemType i32)
i64p   = PtrType (MemType i64)

-- | Alignment restriction in bytes.
data FunDecl = FunDecl { fdRetType  :: !RetType
                       , fdArgTypes :: ![MemType]
                       , fdVarArgs  :: !Bool
                       }
 deriving( Eq )

-- | Return type if any.
type RetType = Maybe MemType

-- | Declare function that returns void
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

ppFunDecl :: FunDecl -> Doc
ppFunDecl (FunDecl rtp args va) = rdoc <> parens (commas (fmap ppMemType args ++ vad))
  where rdoc = maybe (text "void") ppMemType rtp
        vad = if va then [text "..."] else []

-- | Pretty print return type.
ppRetType :: RetType -> Doc
ppRetType = maybe (text "void") ppMemType

intWidthSize ::  Nat -> Size
intWidthSize w = (fromIntegral w + 7) `div` 8 -- Convert bits to bytes.

-- | Returns size of MemType in bytes.
memTypeSize :: DataLayout -> MemType -> Size
memTypeSize dl mtp =
  case mtp of
    IntType w -> intWidthSize w
    FloatType -> 4
    DoubleType -> 8
    PtrType{} -> dl ^. ptrSize
    ArrayType n tp -> fromIntegral n * memTypeSize dl tp
    VecType n tp -> fromIntegral n * memTypeSize dl tp
    StructType si -> structSize si
    MetadataType -> 0

memTypeSizeInBits :: DataLayout -> MemType -> Nat
memTypeSizeInBits dl tp = fromIntegral $ 8 * memTypeSize dl tp

-- | Returns ABI byte alignment constraint in bytes.
memTypeAlign :: DataLayout -> MemType -> Alignment
memTypeAlign dl mtp =
  case mtp of
    IntType w -> a
      where Just a = findIntMatch (fromIntegral w) (dl ^. integerInfo)
    FloatType -> a
      where Just a = findExact 32 (dl ^. floatInfo)
    DoubleType -> a
      where Just a = findExact 64 (dl ^. floatInfo)
    PtrType{} -> dl ^. ptrAlign
    ArrayType _ tp -> memTypeAlign dl tp
    VecType n tp   ->
      case findExact (memTypeSizeInBits dl tp) (dl^.vectorInfo) of
        Just a -> a
        Nothing -> fromIntegral (lgCeil n) + memTypeAlign dl tp
    StructType si  -> structAlign si
    MetadataType -> 0

-- | Information about structs.  Offsets and size is in bytes.
data StructInfo = StructInfo { siDataLayout :: !DataLayout
                             , siIsPacked   :: !Bool
                             , structSize   :: !Size
                             , structAlign  :: !Alignment
                             , structPadding :: !Size
                             , siFields     :: !(V.Vector FieldInfo)
                             }
 deriving (Show)

instance Eq StructInfo where
 si1 == si2 =
   siIsPacked si1 == siIsPacked si2
   &&
   structSize si1 == structSize si2
   &&
   structAlign si1 == structAlign si2
   &&
   structPadding si1 == structPadding si2
   &&
   siFields si1 == siFields si2


data FieldInfo = FieldInfo { fiOffset    :: !Offset
                           , fiType      :: !MemType
                             -- | Number of bytes of padding at end of field.
                           , fiPadding   :: !Size
                           }
 deriving( Eq, Show )

-- | Constructs a function for obtaining target-specific size/alignment
-- information about structs.  The function produced corresponds to the
-- StructLayout object constructor in TargetData.cpp.
mkStructInfo :: DataLayout -> Bool -> [MemType] -> StructInfo
mkStructInfo dl packed tps0 = go [] 0 (max a0 (nextAlign tps0)) tps0
  where a0 | packed = 0
           | otherwise = fromMaybe 0 (findExact 0 (dl^.aggInfo))
        -- Aligment of next type if any. Alignment value of n means to
        -- align on 2^n byte boundaries.
        nextAlign :: [MemType] -> Alignment
        nextAlign _ | packed = 0
        nextAlign [] = 0
        nextAlign (StructType si:tps) =
          nextAlign $
          map fiType (V.toList (siFields si)) ++ tps
        nextAlign (tp:_) = memTypeAlign dl tp
        -- Process fields
        go :: [FieldInfo] -- ^ Fields so far in reverse order.
           -> Size        -- ^ Total size so far (aligned to next element)
           -> Alignment   -- ^ Maximum alignment
           -> [MemType]   -- ^ Fields to process
           -> StructInfo
        go flds sz maxAlign [] =
            StructInfo { siDataLayout = dl
                       , siIsPacked = packed
                       , structSize = sz'
                       , structAlign = maxAlign
                       , structPadding = sz' - sz
                       , siFields = V.fromList (reverse flds)
                       }
          where sz' = nextPow2Multiple sz (fromIntegral maxAlign)

        go flds sz maxAlign (tp:tpl) = go (fi:flds) sz' (max maxAlign fieldAlign) tpl
          where fi = FieldInfo { fiOffset = sz
                               , fiType = tp
                               , fiPadding = sz' - e
                               }
                -- End of field for tp
                e = sz + memTypeSize dl tp
                -- Alignment of next field
                fieldAlign = nextAlign tpl
                -- Size of field at alignment for next thing.
                sz' = nextPow2Multiple e (fromIntegral fieldAlign)

siFieldTypes :: StructInfo -> Vector MemType
siFieldTypes si = fiType <$> siFields si

siFieldCount :: StructInfo -> Int
siFieldCount = V.length . siFields

-- | Returns inforation at given field if int is a valid index.
siFieldInfo :: StructInfo -> Int -> Maybe FieldInfo
siFieldInfo si i = siFields si V.!? i

-- | Returns offset of field if it is defined.
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

commas :: [Doc] -> Doc
commas = hsep . punctuate (char ',')

structBraces :: Doc -> Doc
structBraces b = char '{' <+> b <+> char '}'

-- | Pretty print struct info.
ppStructInfo :: StructInfo -> Doc
ppStructInfo si = structBraces $ commas (V.toList fields)
  where fields = ppMemType <$> siFieldTypes si

-- | Removes the last field from a struct if at least one field exists.
siDropLastField :: StructInfo -> Maybe (StructInfo, FieldInfo)
siDropLastField si
  | V.null (siFields si) = Nothing
  | otherwise = Just (si', V.last (siFields si))
 where si' = mkStructInfo (siDataLayout si) (siIsPacked si) flds'
       flds' = V.toList $ V.init $ siFieldTypes si
