------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.StringLiteral
-- Description      : Utility definitions for strings
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module What4.Utils.StringLiteral
( StringLiteral(..)
, stringLiteralInfo
, fromUnicodeLit
, fromChar8Lit
, fromChar16Lit
, stringLitEmpty
, stringLitLength
, stringLitNull
, stringLitBounds
) where


import           Data.Kind
import           Data.Parameterized.Classes
import qualified Data.ByteString as BS
import           Data.String
import qualified Data.Text as T
import           Numeric.Natural

import           What4.BaseTypes
import qualified What4.Utils.Word16String as WS


------------------------------------------------------------------------
-- String literals

data StringLiteral (si::StringInfo) :: Type where
  UnicodeLiteral :: !T.Text -> StringLiteral Unicode
  Char8Literal   :: !BS.ByteString -> StringLiteral Char8
  Char16Literal  :: !WS.Word16String -> StringLiteral Char16

stringLiteralInfo :: StringLiteral si -> StringInfoRepr si
stringLiteralInfo UnicodeLiteral{} = UnicodeRepr
stringLiteralInfo Char16Literal{}  = Char16Repr
stringLiteralInfo Char8Literal{}   = Char8Repr

fromUnicodeLit :: StringLiteral Unicode -> T.Text
fromUnicodeLit (UnicodeLiteral x) = x

fromChar8Lit :: StringLiteral Char8 -> BS.ByteString
fromChar8Lit (Char8Literal x) = x

fromChar16Lit :: StringLiteral Char16 -> WS.Word16String
fromChar16Lit (Char16Literal x) = x

instance TestEquality StringLiteral where
  testEquality (UnicodeLiteral x) (UnicodeLiteral y) =
    if x == y then Just Refl else Nothing
  testEquality (Char16Literal x) (Char16Literal y) =
    if x == y then Just Refl else Nothing
  testEquality (Char8Literal x) (Char8Literal y) =
    if x == y then Just Refl else Nothing

  testEquality _ _ = Nothing

instance Eq (StringLiteral si) where
  x == y = isJust (testEquality x y)

instance OrdF StringLiteral where
  compareF (UnicodeLiteral x) (UnicodeLiteral y) =
    case compare x y of
      LT -> LTF
      EQ -> EQF
      GT -> GTF
  compareF UnicodeLiteral{} _ = LTF
  compareF _ UnicodeLiteral{} = GTF

  compareF (Char16Literal x) (Char16Literal y) =
    case compare x y of
      LT -> LTF
      EQ -> EQF
      GT -> GTF
  compareF Char16Literal{} _ = LTF
  compareF _ Char16Literal{} = GTF

  compareF (Char8Literal x) (Char8Literal y) =
    case compare x y of
      LT -> LTF
      EQ -> EQF
      GT -> GTF

instance Ord (StringLiteral si) where
  compare x y = toOrdering (compareF x y)

instance ShowF StringLiteral where
  showF (UnicodeLiteral x) = show x
  showF (Char16Literal x) = show x
  showF (Char8Literal x) = show x

instance Show (StringLiteral si) where
  show = showF


instance HashableF StringLiteral where
  hashWithSaltF s (UnicodeLiteral x) = hashWithSalt (hashWithSalt s (1::Int)) x
  hashWithSaltF s (Char16Literal x)  = hashWithSalt (hashWithSalt s (2::Int)) x
  hashWithSaltF s (Char8Literal x)   = hashWithSalt (hashWithSalt s (3::Int)) x

instance Hashable (StringLiteral si) where
  hashWithSalt = hashWithSaltF

stringLitLength :: StringLiteral si -> Natural
stringLitLength (UnicodeLiteral x) = fromIntegral (T.length x)
stringLitLength (Char16Literal x)  = fromIntegral (WS.length x)
stringLitLength (Char8Literal x)   = fromIntegral (BS.length x)

stringLitEmpty :: StringInfoRepr si -> StringLiteral si
stringLitEmpty UnicodeRepr = UnicodeLiteral mempty
stringLitEmpty Char16Repr  = Char16Literal mempty
stringLitEmpty Char8Repr   = Char8Literal mempty

stringLitNull :: StringLiteral si -> Bool
stringLitNull (UnicodeLiteral x) = T.null x
stringLitNull (Char16Literal x)  = WS.null x
stringLitNull (Char8Literal x)   = BS.null x

stringLitBounds :: StringLiteral si -> Maybe (Int, Int)
stringLitBounds si =
  case si of
    UnicodeLiteral t -> T.foldl' f Nothing t
    Char16Literal ws -> WS.foldl' f Nothing ws
    Char8Literal bs  -> BS.foldl' f Nothing bs

 where
 f :: Enum a =>  Maybe (Int,Int) -> a -> Maybe (Int, Int)
 f Nothing c = Just (fromEnum c, fromEnum c)
 f (Just (lo, hi)) c = lo' `seq` hi' `seq` Just (lo',hi')
    where
    lo' = min lo (fromEnum c)
    hi' = max hi (fromEnum c)


instance Semigroup (StringLiteral si) where
  UnicodeLiteral x <> UnicodeLiteral y = UnicodeLiteral (x <> y)
  Char16Literal x  <> Char16Literal y  = Char16Literal (x <> y)
  Char8Literal x   <> Char8Literal y   = Char8Literal (x <> y)

instance IsString (StringLiteral Unicode) where
  fromString = UnicodeLiteral . T.pack
