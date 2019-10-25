------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.Word16String
-- Description      : Utility definitions for wide (2-byte) strings
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

module What4.Utils.Word16String
( Word16String
, fromLEByteString
, empty
, singleton
, null
, index
, append
, length
) where

import           Prelude hiding (null,length)
import qualified Prelude

import           Data.Bits
import           Data.Char
import           Data.Hashable
import           Data.Word
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Numeric

-- | A string of Word16 values, encoded as a bytestring
--   in little endian (LE) order.
--
--   We maintain the invariant that Word16Strings
--   are represented by an even number of bytes.
newtype Word16String = Word16String ByteString


instance Semigroup Word16String where
  (<>) = append

instance Monoid Word16String where
  mempty = empty
  mappend = append

instance Eq Word16String where
  (Word16String xs) == (Word16String ys) = xs == ys

instance Ord Word16String where
  compare (Word16String xs) (Word16String ys) = compare xs ys

instance Show Word16String where
 showsPrec _ = showsWord16String

instance Hashable Word16String where
 hashWithSalt s (Word16String xs) = hashWithSalt s xs

showsWord16String :: Word16String -> ShowS
showsWord16String (Word16String xs0) tl = '"' : go (BS.unpack xs0)
 where
 go [] = '"' : tl
 go (_:[]) = error "showsWord16String: representation has odd number of bytes!"
 go (lo:hi:xs)
    | c == '"'    = "\\\"" ++ go xs
    | isPrint c   = c : go xs
    | otherwise   = "\\u" ++ zs ++ esc ++ go xs

  where
  esc = showHex x []
  zs  = take (4 - Prelude.length esc) (repeat '0')

  x :: Word16
  x = fromIntegral lo .|. (fromIntegral hi `shiftL` 8)

  c :: Char
  c = toEnum (fromIntegral x)


fromLEByteString :: ByteString -> Word16String
fromLEByteString xs
  | BS.length xs `mod` 2 == 0 = Word16String xs
  | otherwise = error "fromLEByteString: bytestring must have even length"

empty :: Word16String
empty = Word16String BS.empty

singleton :: Word16 -> Word16String
singleton c = Word16String (BS.pack [ lo , hi ])
 where
 lo, hi :: Word8
 lo = fromIntegral (c .&. 0xFF)
 hi = fromIntegral (c `shiftR` 8)

null :: Word16String -> Bool
null (Word16String xs) = BS.null xs

index :: Word16String -> Int -> Word16
index (Word16String xs) i = (hi `shiftL` 8) .|. lo
 where
 lo, hi :: Word16
 hi = fromIntegral (BS.index xs (2*i + 1))
 lo = fromIntegral (BS.index xs (2*i))

append :: Word16String -> Word16String -> Word16String
append (Word16String xs) (Word16String ys) =
  Word16String (BS.append xs ys)

length :: Word16String -> Int
length (Word16String xs) = BS.length xs `shiftR` 1

