------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Printf
-- Description      : Interpretation of 'printf' style conversion codes
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- A model of C's @printf@ function. This does not entirely conform to the C
-- standard's specification of @printf@; see @doc/limitations.md@ for the
-- specifics.
--
------------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.LLVM.Printf
( PrintfFlag(..)
, PrintfLengthModifier(..)
, Case(..)
, IntFormat(..)
, FloatFormat(..)
, PrintfConversionType(..)
, PrintfDirective(..)
, parseDirectives
, ConversionDirective(..)
, PrintfOperations(..)
, executeDirectives
, formatInteger
, formatRational
) where

import           Data.Char (toUpper)
import qualified Numeric as N
import           Control.Applicative
import           Data.Attoparsec.ByteString.Char8 hiding (take)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word
import qualified GHC.Stack as GHC

import           Lang.Crucible.Panic (panic)

data PrintfFlag
  = PrintfAlternateForm   -- #
  | PrintfZeroPadding     -- 0
  | PrintfNegativeWidth   -- -
  | PrintfPosSpace        -- ' '
  | PrintfPosPlus         -- +
  | PrintfThousandsSep    -- '
 deriving (Eq,Ord,Show)

data PrintfLengthModifier
  = Len_Byte                  -- hh
  | Len_Short                 -- h
  | Len_Long                  -- l
  | Len_LongLong              -- ll
  | Len_LongDouble            -- L
  | Len_IntMax                -- j
  | Len_PtrDiff               -- t
  | Len_Sizet                 -- z
  | Len_NoMod                 -- <<no length modifier>>
 deriving (Eq,Ord,Show)

data Case
  = UpperCase
  | LowerCase
 deriving (Eq,Ord,Show)

data IntFormat
  = IntFormat_SignedDecimal      -- i,d
  | IntFormat_UnsignedDecimal    -- u
  | IntFormat_Octal              -- o
  | IntFormat_Hex Case           -- x,X
 deriving (Eq,Ord,Show)

signedIntFormat :: IntFormat -> Bool
signedIntFormat IntFormat_SignedDecimal = True
signedIntFormat _ = False

data FloatFormat
  = FloatFormat_Scientific Case -- e,E
  | FloatFormat_Standard Case   -- f,F
  | FloatFormat_Auto Case       -- g,G
  | FloatFormat_Hex Case        -- a,A
 deriving (Eq,Ord,Show)

data PrintfConversionType
  = Conversion_Integer  IntFormat
  | Conversion_Floating FloatFormat
  | Conversion_Char             -- c
  | Conversion_String           -- s
  | Conversion_Pointer          -- p
  | Conversion_CountChars       -- n
 deriving (Eq,Ord,Show)

data PrintfDirective
  = StringDirective BS.ByteString
  | ConversionDirective ConversionDirective
 deriving (Eq,Ord,Show)

data ConversionDirective = Conversion
    { printfAccessField :: Maybe Int
    , printfFlags     :: Set PrintfFlag
    , printfMinWidth  :: Int
    , printfPrecision :: Maybe Int
    , printfLengthMod :: PrintfLengthModifier
    , printfType      :: PrintfConversionType
    }
 deriving (Eq,Ord,Show)


data PrintfOperations m
  = PrintfOperations
    { printfGetInteger  :: Int  -- Field number
                        -> Bool -- is Signed?
                        -> PrintfLengthModifier
                        -> m (Maybe Integer)
    , printfGetFloat    :: Int -- FieldNumber
                        -> PrintfLengthModifier
                        -> m (Maybe Rational)
    , printfGetPointer  :: Int -- FieldNumber
                        -> m String
    , printfGetString   :: Int -- FieldNumber
                        -> Maybe Int -- Number of chars to read; if Nothing, read until null terminator
                        -> m [Word8]
    , printfSetInteger  :: Int -- FieldNumber
                        -> PrintfLengthModifier
                        -> Int -- value to set
                        -> m ()

    , printfUnsupported :: !(forall a. GHC.HasCallStack => String -> m a)
    }

formatInteger
  :: Maybe Integer
  -> IntFormat
  -> Int -- min width
  -> Maybe Int -- precision
  -> Set PrintfFlag
  -> String
formatInteger mi fmt minwidth prec flags =
  case mi of
    Nothing ->
      let n = max 4 (max minwidth (fromMaybe 0 prec))
       in replicate n '?'
    Just i  -> do
      case fmt of
        IntFormat_SignedDecimal ->
           formatSignedDec i minwidth prec flags
        IntFormat_UnsignedDecimal ->
           formatUnsignedDec i minwidth prec flags
        IntFormat_Octal ->
           formatOctal i minwidth prec flags
        IntFormat_Hex c ->
           formatHex i c minwidth prec flags

insertThousands :: Char -> String -> String
insertThousands sep = reverse . go . reverse
 where
  go (a:b:c:xs@(_:_)) = a:b:c:sep:go xs
  go xs = xs


addLeadingZeros ::
  Maybe Int -> -- precision
  String ->
  String
addLeadingZeros Nothing digits = digits
addLeadingZeros (Just p) digits =
   let n = max 0 (p - length digits) in
   replicate n '0' ++ digits

formatSignedDec
  :: Integer -- value to format
  -> Int     -- minwidth
  -> Maybe Int     -- precision
  -> Set PrintfFlag
  -> String
formatSignedDec i minwidth prec flags = do
  let sgn = if | i < 0  -> "-"
               | Set.member PrintfPosPlus  flags -> "+"
               | Set.member PrintfPosSpace flags -> " "
               | otherwise -> ""
  let digits = N.showInt (abs i) []
  let precdigits = addLeadingZeros prec digits
  let sepdigits = if Set.member PrintfThousandsSep flags then
                      insertThousands ',' precdigits -- FIXME, get thousands separator from somewhere?
                  else
                      precdigits
  let pad = max 0 (minwidth - length sepdigits - length sgn)
  if | Set.member PrintfNegativeWidth flags ->
          sgn ++ sepdigits ++ replicate pad ' '
     | Set.member PrintfZeroPadding flags && prec == Nothing ->
          -- FIXME? this interacts poorly with the thousands seperation flag...
          sgn ++ replicate pad '0' ++ sepdigits
     | otherwise ->
          replicate pad ' ' ++ sgn ++ sepdigits

formatUnsignedDec
  :: Integer -- value to format
  -> Int     -- minwidth
  -> Maybe Int     -- precision
  -> Set PrintfFlag
  -> String
formatUnsignedDec i minwidth prec flags = do
  let digits = N.showInt (abs i) []
  let precdigits = addLeadingZeros prec digits
  let sepdigits = if Set.member PrintfThousandsSep flags then
                      insertThousands ',' precdigits -- FIXME, get thousands separator from somewhere?
                  else
                      precdigits
  let pad = max 0 (minwidth - length sepdigits)
  if | Set.member PrintfNegativeWidth flags ->
          sepdigits ++ replicate pad ' '
     | Set.member PrintfZeroPadding flags && prec == Nothing ->
          -- FIXME? this interacts poorly with the thousands seperation flag...
          replicate pad '0' ++ sepdigits
     | otherwise ->
          replicate pad ' ' ++ sepdigits

formatOctal
  :: Integer -- value to format
  -> Int     -- minwidth
  -> Maybe Int     -- precision
  -> Set PrintfFlag
  -> String
formatOctal i minwidth prec flags = do
  let digits = N.showOct (abs i) []
  let precdigits = addLeadingZeros prec digits
  let leadingPrecDigit =
        case precdigits of
          d:_ -> d
          [] -> panic
                  "formatOctal"
                  ["Octal-formatted number with no digits"]
  let altdigits = if Set.member PrintfAlternateForm flags && leadingPrecDigit /= '0' then
                     '0':precdigits
                  else
                     precdigits
  let pad = max 0 (minwidth - length altdigits)
  if | Set.member PrintfNegativeWidth flags ->
          altdigits ++ replicate pad ' '
     | Set.member PrintfZeroPadding flags && prec == Nothing ->
          replicate pad '0' ++ altdigits
     | otherwise ->
          replicate pad ' ' ++ altdigits

formatHex
  :: Integer -- value to format
  -> Case    -- upper or lower case
  -> Int     -- minwidth
  -> Maybe Int     -- precision
  -> Set PrintfFlag
  -> String
formatHex i c minwidth prec flags = do
  let digits = N.showHex (abs i) []
  let precdigits = addLeadingZeros prec digits
  -- Why only add "0x" when i is non-zero?  I have no idea,
  -- that's just what the docs say...
  let altstring = if Set.member PrintfAlternateForm flags && i /= 0 then
                    "0x"
                  else
                    ""
  let pad = max 0 (minwidth - length precdigits - length altstring)
  let padded = if | Set.member PrintfNegativeWidth flags ->
                       altstring ++ precdigits ++ replicate pad ' '
                  | Set.member PrintfZeroPadding flags && prec == Nothing ->
                       altstring ++ replicate pad '0' ++ precdigits
                  | otherwise ->
                       replicate pad ' ' ++ altstring ++ precdigits
  case c of
    UpperCase -> map toUpper padded
    LowerCase -> padded


formatRational
  :: Maybe Rational
  -> FloatFormat
  -> Int -- min width
  -> Maybe Int -- precision
  -> Set PrintfFlag
  -> Either String String   -- ^ Left indicates an error, right is OK
formatRational mr fmt minwidth prec flags =
  case mr of
    Nothing ->
      let n = max 4 (min minwidth (fromMaybe 0 prec))
       in return (replicate n '?')
    Just r ->
      -- FIXME, we ignore the thousands flag...
      do let toCase c x = case c of
                            UpperCase -> map toUpper x
                            LowerCase -> x
         let sgn = if | r < 0  -> "-"
                      | Set.member PrintfPosPlus  flags -> "+"
                      | Set.member PrintfPosSpace flags -> " "
                      | otherwise -> ""
         let dbl = N.fromRat (abs r) :: Double
         let prec' = case prec of Nothing -> Just 6; _ -> prec
         str <- case fmt of
                  FloatFormat_Scientific c ->
                       return $ toCase c $ N.showEFloat prec' dbl []
                  FloatFormat_Standard c ->
                   return $ toCase c $
                     if Set.member PrintfAlternateForm flags
                       then N.showFFloatAlt prec' dbl []
                       else N.showFFloat prec' dbl []
                  FloatFormat_Auto c ->
                    return $ toCase c $
                      if Set.member PrintfAlternateForm flags
                         then N.showGFloatAlt prec' dbl []
                         else N.showGFloat prec' dbl []
                  FloatFormat_Hex _c ->
                    -- FIXME, could probably implement this using N.floatToDigits...
                    Left "'a' and 'A' conversion codes not currently supported"
         let pad = max 0 (minwidth - length str - length sgn)
         return $
           if | Set.member PrintfNegativeWidth flags ->
                  sgn ++ str ++ replicate pad ' '
              | Set.member PrintfZeroPadding flags ->
                   sgn ++ replicate pad '0' ++ str
              | otherwise ->
                   replicate pad ' ' ++ sgn ++ str

-- | Given a list of 'PrintfDirective's, compute the resulting 'BS.ByteString'
-- and its length.
--
-- We make an effort not to assume a particular text encoding for the
-- 'BS.ByteString' that this returns. Some parts of the implementation do use
-- functionality from "Data.ByteString.Char8", which is limited to the subset
-- of Unicode covered by code points 0-255. We believe these uses are justified,
-- however, and we have left comments explaining the reasoning behind each use.
executeDirectives :: forall m. Monad m
                  => PrintfOperations m
                  -> [PrintfDirective]
                  -> m (BS.ByteString, Int)
executeDirectives ops = go id 0 0
  where
   go :: (BS.ByteString -> BS.ByteString) -> Int -> Int -> [PrintfDirective] -> m (BS.ByteString, Int)
   go fstr !len !_fld [] = return (fstr BS.empty, len)
   go fstr !len !fld ((StringDirective s):xs) = do
       let len'  = len + BS.length s
       let fstr' = fstr . BS.append s
       go fstr' len' fld xs
   go fstr !len !fld (ConversionDirective d:xs) =
       let fld' = fromMaybe (fld+1) (printfAccessField d) in
       case printfType d of
         Conversion_Integer fmt -> do
           let sgn = signedIntFormat fmt
           i <- printfGetInteger ops fld' sgn (printfLengthMod d)
           -- The use of BSC.pack is fine here, as the output of formatInteger
           -- consists solely of ASCII characters.
           let istr  = BSC.pack $ formatInteger i fmt (printfMinWidth d) (printfPrecision d) (printfFlags d)
           let len'  = len + BS.length istr
           let fstr' = fstr . BS.append istr
           go fstr' len' fld' xs
         Conversion_Floating fmt -> do
           r <- printfGetFloat ops fld' (printfLengthMod d)
           -- The use of BSC.pack is fine here, as the output of formatRational
           -- consists solely of ASCII characters.
           rstr <- BSC.pack <$>
                   case formatRational r fmt
                           (printfMinWidth d)
                           (printfPrecision d)
                           (printfFlags d) of
                     Left err -> printfUnsupported ops err
                     Right a -> return a
           let len'  = len + BS.length rstr
           let fstr' = fstr . BS.append rstr
           go fstr' len' fld' xs
         Conversion_String -> do
           s <- BS.pack <$> printfGetString ops fld' (printfPrecision d)
           let len'  = len + BS.length s
           let fstr' = fstr . BS.append s
           go fstr' len' fld' xs
         Conversion_Char -> do
           let sgn  = False -- unsigned
           i <- printfGetInteger ops fld' sgn Len_NoMod
           let c :: Char = maybe '?' (toEnum . fromInteger) i
           let len'  = len + 1
           -- Note the use of BSC.cons here: this assumes on the assumption
           -- that C strings are arrays of 1-byte characters.
           let fstr' = fstr . BSC.cons c
           go fstr' len' fld' xs
         Conversion_Pointer -> do
           -- Note the use of BSC.pack here: this assumes that the output of
           -- printfGetPointer uses solely ASCII characters. For crux-llvm's
           -- printf override, this is always the case, as pointers are
           -- pretty-printed using the ppPtr function, which satisfies this
           -- criterion.
           pstr <- BSC.pack <$> printfGetPointer ops fld'
           let len'  = len + BS.length pstr
           let fstr' = fstr . BS.append pstr
           go fstr' len' fld' xs
         Conversion_CountChars -> do
           printfSetInteger ops fld' (printfLengthMod d) len
           go fstr len fld' xs

parseDirectives :: [Word8] -> Either String [PrintfDirective]
parseDirectives xs =
  parseOnly (parseFormatString <* endOfInput) (BS.pack xs)

parseFormatString :: Parser [PrintfDirective]
parseFormatString = many $ choice
  [ StringDirective <$> takeWhile1 (/= '%')
  , string "%%" >> return (StringDirective "%")
  , parseConversion
  ]

parseConversion :: Parser PrintfDirective
parseConversion = do
  _ <- char '%'
  field <- option Nothing (Just <$>
             do d <- decimal
                _ <- char '$'
                return d)
  flags <- parseFlags Set.empty
  width <- option 0 decimal
  prec  <- option Nothing (char '.' >> (Just <$> decimal))
  len   <- parseLenModifier
  typ   <- parseConversionType
  return $ ConversionDirective $ Conversion
         { printfAccessField = field
         , printfFlags       = flags
         , printfMinWidth    = width
         , printfPrecision   = prec
         , printfLengthMod   = len
         , printfType        = typ
         }

parseFlags :: Set PrintfFlag -> Parser (Set PrintfFlag)
parseFlags fs = choice
  [ char '#'  >> parseFlags (Set.insert PrintfAlternateForm fs)
  , char '0'  >> parseFlags (Set.insert PrintfZeroPadding fs)
  , char '-'  >> parseFlags (Set.insert PrintfNegativeWidth fs)
  , char ' '  >> parseFlags (Set.insert PrintfPosSpace fs)
  , char '+'  >> parseFlags (Set.insert PrintfPosPlus fs)
  , char '\'' >> parseFlags (Set.insert PrintfThousandsSep fs)
  , return fs
  ]

parseLenModifier :: Parser PrintfLengthModifier
parseLenModifier = choice
  [ string "hh" >> return Len_Byte
  , string "h"  >> return Len_Short
  , string "ll" >> return Len_LongLong
  , string "L"  >> return Len_LongDouble
  , string "l"  >> return Len_Long
  , string "j"  >> return Len_IntMax
  , string "t"  >> return Len_PtrDiff
  , string "z"  >> return Len_Sizet
  , return Len_NoMod
  ]

parseConversionType :: Parser PrintfConversionType
parseConversionType = choice
  [ char 'd' >> return (Conversion_Integer IntFormat_SignedDecimal)
  , char 'i' >> return (Conversion_Integer IntFormat_SignedDecimal)
  , char 'u' >> return (Conversion_Integer IntFormat_UnsignedDecimal)
  , char 'o' >> return (Conversion_Integer IntFormat_Octal)
  , char 'x' >> return (Conversion_Integer (IntFormat_Hex LowerCase))
  , char 'X' >> return (Conversion_Integer (IntFormat_Hex UpperCase))
  , char 'e' >> return (Conversion_Floating (FloatFormat_Scientific LowerCase))
  , char 'E' >> return (Conversion_Floating (FloatFormat_Scientific UpperCase))
  , char 'f' >> return (Conversion_Floating (FloatFormat_Standard LowerCase))
  , char 'F' >> return (Conversion_Floating (FloatFormat_Standard UpperCase))
  , char 'g' >> return (Conversion_Floating (FloatFormat_Auto LowerCase))
  , char 'G' >> return (Conversion_Floating (FloatFormat_Auto UpperCase))
  , char 'a' >> return (Conversion_Floating (FloatFormat_Hex LowerCase))
  , char 'A' >> return (Conversion_Floating (FloatFormat_Hex UpperCase))
  , char 'c' >> return Conversion_Char
  , char 's' >> return Conversion_String
  , char 'p' >> return Conversion_Pointer
  , char 'n' >> return Conversion_CountChars
  ]
