------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Printf
-- Description      : Interpretation of 'printf' style conversion codes
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
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
, PrintfOperations(..)
, executeDirectives
) where

import           Data.Char (toUpper)
import qualified Numeric as N
import qualified Codec.Binary.UTF8.Generic as UTF8
import           Control.Applicative
import           Data.Attoparsec.ByteString.Char8 hiding (take)
import qualified Data.ByteString as BS
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word

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
  | ConversionDirective
    { printfAccessField :: Maybe Int
    , printfFlags     :: Set PrintfFlag
    , printfMinWidth  :: Int
    , printfPrecision :: Int
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

    , printfUnsupported :: !(forall a. String -> m a)
    }

formatInteger
  :: Maybe Integer
  -> IntFormat
  -> Int -- min width
  -> Int -- precision
  -> Set PrintfFlag
  -> String
formatInteger mi fmt minwidth prec flags =
  case mi of
    Nothing ->
      let n = max 4 (max minwidth prec)
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

formatSignedDec
  :: Integer -- value to format
  -> Int     -- minwidth
  -> Int     -- precision
  -> Set PrintfFlag
  -> String
formatSignedDec i minwidth prec flags = do
  let sgn = if | i < 0  -> "-"
               | Set.member PrintfPosPlus  flags -> "+"
               | Set.member PrintfPosSpace flags -> " "
               | otherwise -> ""
  let digits = N.showInt (abs i) []
  let precdigits = if prec > 0 then
                      let n = max 0 (prec - length digits) in
                      replicate n '0' ++ digits
                   else
                      digits
  let sepdigits = if Set.member PrintfThousandsSep flags then
                      insertThousands ',' precdigits -- FIXME, get thousands separator from somewhere?
                  else
                      precdigits
  let pad = max 0 (minwidth - length sepdigits - length sgn)
  if | Set.member PrintfNegativeWidth flags ->
          sgn ++ sepdigits ++ replicate pad ' '
     | Set.member PrintfZeroPadding flags && prec == 0 ->
          -- FIXME? this interacts poorly with the thousands seperation flag...
          sgn ++ replicate pad '0' ++ sepdigits
     | otherwise ->
          replicate pad ' ' ++ sgn ++ sepdigits

formatUnsignedDec
  :: Integer -- value to format
  -> Int     -- minwidth
  -> Int     -- precision
  -> Set PrintfFlag
  -> String
formatUnsignedDec i minwidth prec flags = do
  let digits = N.showInt (abs i) []
  let precdigits = if prec > 0 then
                      let n = max 0 (prec - length digits) in
                      replicate n '0' ++ digits
                   else
                      digits
  let sepdigits = if Set.member PrintfThousandsSep flags then
                      insertThousands ',' precdigits -- FIXME, get thousands separator from somewhere?
                  else
                      precdigits
  let pad = max 0 (minwidth - length sepdigits)
  if | Set.member PrintfNegativeWidth flags ->
          sepdigits ++ replicate pad ' '
     | Set.member PrintfZeroPadding flags && prec == 0 ->
          -- FIXME? this interacts poorly with the thousands seperation flag...
          replicate pad '0' ++ sepdigits
     | otherwise ->
          replicate pad ' ' ++ sepdigits

formatOctal
  :: Integer -- value to format
  -> Int     -- minwidth
  -> Int     -- precision
  -> Set PrintfFlag
  -> String
formatOctal i minwidth prec flags = do
  let digits = N.showOct (abs i) []
  let precdigits = if prec > 0 then
                      let n = max 0 (prec - length digits) in
                      replicate n '0' ++ digits
                   else
                      digits
  let altdigits = if Set.member PrintfAlternateForm flags && head precdigits /= '0' then
                     '0':precdigits
                  else
                     precdigits
  let pad = max 0 (minwidth - length altdigits)
  if | Set.member PrintfNegativeWidth flags ->
          altdigits ++ replicate pad ' '
     | Set.member PrintfZeroPadding flags && prec == 0 ->
          replicate pad '0' ++ altdigits
     | otherwise ->
          replicate pad ' ' ++ altdigits

formatHex
  :: Integer -- value to format
  -> Case    -- upper or lower case
  -> Int     -- minwidth
  -> Int     -- precision
  -> Set PrintfFlag
  -> String
formatHex i c minwidth prec flags = do
  let digits = N.showHex (abs i) []
  let precdigits = if prec > 0 then
                      let n = max 0 (prec - length digits) in
                      replicate n '0' ++ digits
                   else
                      digits
  -- Why only add "0x" when i is non-zero?  I have no idea,
  -- that's just what the docs say...
  let altstring = if Set.member PrintfAlternateForm flags && i /= 0 then
                    "0x"
                  else
                    ""
  let pad = max 0 (minwidth - length precdigits - length altstring)
  let padded = if | Set.member PrintfNegativeWidth flags ->
                       altstring ++ precdigits ++ replicate pad ' '
                  | Set.member PrintfZeroPadding flags && prec == 0 ->
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
  -> Int -- precision
  -> Set PrintfFlag
  -> Either String String   -- ^ Left indicates an error, right is OK
formatRational mr fmt minwidth prec flags =
  case mr of
    Nothing ->
      let n = min 4 (min minwidth prec)
       in return (replicate n '?')
    Just r ->
      -- FIXME, we ignore the thousands flag...
      do let mprec = if prec == 0 then Nothing else Just prec
         let toCase c x = case c of
                            UpperCase -> map toUpper x
                            LowerCase -> x
         let sgn = if | r < 0  -> "-"
                      | Set.member PrintfPosPlus  flags -> "+"
                      | Set.member PrintfPosSpace flags -> " "
                      | otherwise -> ""
         let dbl = N.fromRat (abs r) :: Double
         str <- case fmt of
                  FloatFormat_Scientific c ->
                       return $ toCase c $ N.showEFloat mprec dbl []
                  FloatFormat_Standard c ->
                   return $ toCase c $
                     if Set.member PrintfAlternateForm flags
                       then N.showFFloatAlt mprec dbl []
                       else N.showFFloat mprec dbl []
                  FloatFormat_Auto c ->
                    return $ toCase c $
                      if Set.member PrintfAlternateForm flags
                         then N.showGFloatAlt mprec dbl []
                         else N.showGFloat mprec dbl []
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

executeDirectives :: forall m. Monad m
                  => PrintfOperations m
                  -> [PrintfDirective]
                  -> m (String, Int)
executeDirectives ops = go id 0 0
  where
   go :: (String -> String) -> Int -> Int -> [PrintfDirective] -> m (String, Int)
   go fstr !len !_fld [] = return (fstr [], len)
   go fstr !len !fld ((StringDirective bs):xs) = do
       let s     = UTF8.toString bs
       let len'  = len + length s
       let fstr' = fstr . (s ++)
       go fstr' len' fld xs
   go fstr !len !fld (d@ConversionDirective{}:xs) =
       let fld' = fromMaybe (fld+1) (printfAccessField d) in
       case printfType d of
         Conversion_Integer fmt -> do
           let sgn = signedIntFormat fmt
           i <- printfGetInteger ops fld' sgn (printfLengthMod d)
           let istr  = formatInteger i fmt (printfMinWidth d) (printfPrecision d) (printfFlags d)
           let len'  = len + length istr
           let fstr' = fstr . (istr ++)
           go fstr' len' fld' xs
         Conversion_Floating fmt -> do
           r <- printfGetFloat ops fld' (printfLengthMod d)
           rstr <- case formatRational r fmt
                           (printfMinWidth d)
                           (printfPrecision d)
                           (printfFlags d) of
                     Left err -> printfUnsupported ops err
                     Right a -> return a
           let len'  = len + length rstr
           let fstr' = fstr . (rstr ++)
           go fstr' len' fld' xs
         Conversion_String -> do
           let prec  = if printfPrecision d == 0 then Nothing else Just (printfPrecision d)
           ws <- printfGetString ops fld' prec
           let s     = UTF8.toString ws
           let len'  = len + length s
           let fstr' = fstr . (s ++)
           go fstr' len' fld' xs
         Conversion_Char -> do
           let sgn  = False -- unsigned
           i <- printfGetInteger ops fld' sgn Len_NoMod
           let c :: Char = maybe '?' (toEnum . fromInteger) i
           let len'  = len + 1
           let fstr' = fstr . (c:)
           go fstr' len' fld' xs
         Conversion_Pointer -> do
           pstr <- printfGetPointer ops fld'
           let len'  = len + length pstr
           let fstr' = fstr . (pstr ++)
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
  prec  <- option 0 (char '.' >> decimal)
  len   <- parseLenModifier
  typ   <- parseConversionType
  return ConversionDirective
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
