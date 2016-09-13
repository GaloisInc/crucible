------------------------------------------------------------------------
-- |
-- Module           : Lang.MATLAB.CharVector
-- Description      : Provides a type for storing character constants
--                    in Matlab.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides a type for storing character constants in Matlab.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module Lang.MATLAB.CharVector
  ( CharVector
  , fromVector
  , toVector
  , fromText
  , toText
  , toString
  , fromString
  , fromSource
  , toSourceString
  , matchIdent
  ) where

import           Control.DeepSeq
import           Data.Hashable
import           Data.String
import           Data.Text as Text
import qualified Data.Vector as V
import           Data.Word


newtype CharVector = CV (V.Vector Word16)

instance Eq CharVector where
  CV x == CV y = x == y

instance Ord CharVector where
  compare (CV x) (CV y) = compare x y

instance IsString CharVector where
  fromString s = deepseq v (CV v)
    where v = charToWord <$> V.fromList s

instance Hashable CharVector where
  hashWithSalt s (CV v) = V.foldl' hashWithSalt s v

instance Show CharVector where
  show (CV v0) = wordToChar <$> V.toList v0

toSourceString :: CharVector -> String
toSourceString cv = '\'' : go (Text.uncons (toText cv))
  where go (Just ('\'',r)) = "\'\'" ++ go (Text.uncons r)
        go (Just (c,r)) = c : go (Text.uncons r)
        go Nothing = "\'"

-- | Create a string literal from source text.
fromSource :: Text -> Maybe CharVector
fromSource txt = do
  txt1 <- Text.stripPrefix "'" txt
  txt2 <- Text.stripSuffix "'" txt1
  return $ fromText $ Text.replace "''" "'" txt2

fromVector :: V.Vector Word16 -> CharVector
fromVector = CV

toVector :: CharVector -> V.Vector Word16
toVector (CV v) = v

wordToChar :: Word16 -> Char
wordToChar w = toEnum $ fromIntegral w

charToWord :: Char -> Word16
charToWord c = fromIntegral $ fromEnum c

-- | Convert text directly to char vector.
fromText :: Text.Text -> CharVector
fromText t = CV (V.unfoldrN (Text.length t) uncon t)
  where uncon u = (\(c,v) -> (charToWord c,v)) <$> Text.uncons u

-- | Convert char vector to text.
toText :: CharVector -> Text.Text
toText (CV v0) = Text.unfoldrN (V.length v0) go v0
  where go v | V.null v = Nothing
             | otherwise = Just (wordToChar (V.head v), V.tail v)

-- | Convert char vector to a string
toString :: CharVector -> String
toString (CV v0) = go v0
  where go v | V.null v = []
             | otherwise = wordToChar (V.head v) : go (V.tail v)

-- | @matchIdent fp rp s@ returns @True@ if @s@ is non-empty and
-- the first character satisifies @fp@ while the remaining characters
-- satisfy @rp@.
matchIdent :: (Char -> Bool) -- ^ Pattern match for first character.
           -> (Char -> Bool) -- ^ Pattern match for rest of character.
           -> CharVector
           -> Bool
matchIdent fp rp (CV v)
    | V.null v = False
    | otherwise = fp (wordToChar (v V.! 0))
               && V.all (rp . wordToChar) (V.drop 1 v)
