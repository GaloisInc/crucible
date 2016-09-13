module Lang.Crucible.Server.Encoding
  ( decodeSigned
  , encodeSigned
  , decodeUnsigned
  , encodeUnsigned
  , encodeRational
  , decodeRational
  ) where

import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString as BS
import Data.Bits
import Data.Int
import Data.Monoid
import Data.Ratio
import Data.Word


-- | Encode a signed integer in two's complement with the most-significant bit first.
encodeSigned :: Integer -> Builder
encodeSigned n0 = go (s n0) (ls n0) mempty
  where -- Get least-significant byte.
        ls :: Integer -> Word8
        ls n = fromIntegral (n .&. 0xFF)
        -- Get most-significant bit.
        msb w = w `testBit` 7
        -- Shift by byte
        s n = n `shiftR` 8

        --  | Incrementally create the bytestring.
        go :: Integer -- ^ The value above the current word.
           -> Word8 -- ^ The current word.
           -> Builder
           -> Builder
        -- Wehn
        go 0 l b | msb l     = Builder.word8 0 <> Builder.word8 l <> b
                 | otherwise = Builder.word8 l <> b
        -- When we have reached the end of a negative number, prepend
        -- the byte depending on what the msb is.
        go (-1) l b | msb l     = Builder.word8 l <> b
                    | otherwise = Builder.word8 (-1) <> Builder.word8 l <> b
        -- Recurse when we haven't reached most-significant word.
        go n l b = go (s n) (ls n) (Builder.word8 l <> b)

-- | Decode a signed integer in two's complement with the most-significant bit first.
decodeSigned :: BS.ByteString -> Integer
decodeSigned bs0 =
    case BS.uncons bs0 of
      Nothing -> 0
      Just (w0, bs) -> decodeUnsigned' (toInteger i) bs
        where i :: Int8
              i = fromIntegral w0

-- | Utility function that decode a unsigned integer with most-significant bit first
decodeUnsigned' :: Integer -- Initial value to shift (result negative if this is).
                -> BS.ByteString
                -> Integer
decodeUnsigned' = BS.foldl f
  where -- Append word to integer, shifting current integer by 8.
        f :: Integer -> Word8 -> Integer
        f v w = (v `shiftL` 8) .|. toInteger w

-- | Encode an unsigned integer with the most-significant bit first.
encodeUnsigned :: Integer -> Builder
encodeUnsigned n0
    | n0 >= 0 = go (s n0) (w n0)
    | otherwise = error "encodeUnsigned given negative value."
  where -- Get least-significant byte.
        w :: Integer -> Builder
        w n = Builder.word8 (fromIntegral (n .&. 0xFF))
        -- Shift by byte
        s n = n `shiftR` 8
        go :: Integer -> Builder -> Builder
        go 0 b = b
        go n b = go (s n) (w n <> b)

-- | Decode a signed integer in two's complement with the most-significant bit first.
decodeUnsigned :: BS.ByteString -> Integer
decodeUnsigned = decodeUnsigned' 0

-- | Encode an unsigned integer using Google protocol buffers varint format.
encodeUnsignedVarint :: Integer -> Builder
encodeUnsignedVarint w
       -- | If the low 7-bits are set, msb is clear, then we are done.
     | low7 == w = Builder.word8 (fromIntegral low7)
     | otherwise = Builder.word8 (fromIntegral (0x80 .|. low7))
                   <> encodeUnsignedVarint (w `shiftR` 7)
  where low7 = w .&. 0x7F

-- | Decode a unsigned integer in Google protocol buffers varint format
-- from the head of a bytestring.
decodeUnsignedVarint :: Monad m => BS.ByteString -> m (Integer, BS.ByteString)
decodeUnsignedVarint = go 0
  where go :: Monad m => Integer -> BS.ByteString -> m (Integer, BS.ByteString)
        go v bs0 =
          case BS.uncons bs0 of
            Nothing -> fail "Unexpected premature end of unsigned varint."
            Just (w,bs) | low7 == w -> return (r, bs)
                        | otherwise -> go r bs
              where low7 = w .&. 0x7F
                    r = (v `shiftL` 7) .|. toInteger low7

-- | Encode a rational as a pair with a unsigned denominator followed by a
-- signed numerator.
encodeRational :: Rational -> Builder
encodeRational r = d <> n
  where n = encodeSigned (numerator r)
        d = encodeUnsignedVarint (denominator r)

-- | Encode a rational as a pair with a unsigned denominator followed by a
-- signed numerator.
decodeRational :: Monad m => BS.ByteString -> m Rational
decodeRational bs0 = do
  (d, bs) <- decodeUnsignedVarint bs0
  return $ decodeSigned bs % d