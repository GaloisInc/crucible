{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lang.MATLAB.FieldName
  ( FieldName
  , fieldNameFromCharVector
  , fieldNameFromText
  , fieldNameToText
  , isFieldName
  ) where

import Control.Exception (assert)
import Data.Char
import Data.Hashable
import Data.String
import Data.Text
import qualified Lang.MATLAB.CharVector as CV

------------------------------------------------------------------------
-- FieldName

-- | The name of a field.
newtype FieldName = FieldName { _unFieldName :: CV.CharVector }
  deriving (Eq, Ord, Hashable)

instance IsString FieldName where
  fromString = fieldNameFromCharVector . fromString

instance Show FieldName where
  show (FieldName nm) = show nm

fieldNameFromCharVector :: CV.CharVector -> FieldName
fieldNameFromCharVector c = assert (isFieldName c) (FieldName c)

fieldNameFromText :: Text -> FieldName
fieldNameFromText = fieldNameFromCharVector . CV.fromText

fieldNameToText :: FieldName -> Text
fieldNameToText (FieldName nm) = CV.toText nm

-- | Return true if char vector is a fiel.d
isFieldName :: CV.CharVector -> Bool
isFieldName = CV.matchIdent isAlpha isFieldChar
  where isFieldChar '_' = True
        isFieldChar c = isAlphaNum c
