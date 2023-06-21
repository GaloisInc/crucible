{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


module Mir.DefId
( DefId
, didCrate
, didCrateDisambig
, didPath
, textId
, idText

, ExplodedDefId
, idKey
, explodedDefIdPat
, textIdKey

, getTraitName
, cleanVariantName
, parseFieldName
) where

import Control.Lens (makeLenses)
import Data.Aeson

import qualified Language.Haskell.TH.Syntax as TH
import qualified Data.Text as T
import           Data.Text (Text)
import qualified Text.Regex as Regex

import Data.Maybe (fromMaybe)

import Data.String (IsString(..))
import GHC.Generics

import qualified Debug.Trace as Debug

import Prettyprinter


-- | Normal path segments consist of a name and a disambiguator index.
-- Sometimes the name is not a valid Rust identifier but rather is a special
-- string such as "{{impl}}", "{{closure}}", or "{{promoted}}".
type Segment = (Text, Int)

data DefId = DefId
    {
    -- | The name of the enclosing crate.
      _didCrate :: Text
    -- | The disambiguator of the enclosing crate.  These are strings, in a
    -- different format than the integer disambiguators used for normal path
    -- segments.
    , _didCrateDisambig :: Text
    -- | The segments of the path.
    , _didPath :: [Segment]
    }
  deriving (Eq, Ord, Generic)

makeLenses ''DefId

-- | The crate disambiguator hash produced when the crate metadata string is
-- empty. This is useful for creating 'DefId's for thing that do not have a
-- disambiguator associated with it (e.g., Crucible names).
defaultDisambiguator :: Text
defaultDisambiguator = "3a1fbbbh"

-- | Parse a string into a `DefId`.
--
-- For convenience when writing literal paths in the Haskell source, both types
-- of disambiguators are optional.  If the crate disambiguator is omitted, then
-- it's assumed to be `defaultDisambiguator`, and if a segment disambiguator is
-- omitted elsewhere in the path, it's assumed to be zero.  So you can write,
-- for example, `foo::bar::Baz`, and parsing will expand it to the
-- canonical form `foo/3a1fbbbh::bar[0]::Baz[0]`.
textId :: Text -> DefId
textId s = DefId crate disambig segs
  where
    (crateStr, segStrs) = case T.splitOn "::" s of
        [] -> error $ "textId: no crate name in " ++ show s
        x:xs -> (x, xs)

    (crate, disambig) = case T.splitOn "/" crateStr of
        [x] -> (x, defaultDisambiguator)
        [x, y] -> (x, y)
        _ -> error $ "textId: malformed crate name " ++ show crateStr

    parseSeg :: Text -> Segment
    parseSeg segStr =
        let (a, b) = T.breakOnEnd "[" segStr
            a' = fromMaybe a $ T.stripSuffix "[" a
            b' = fromMaybe b $ T.stripSuffix "]" b
        in if T.null a then (b, 0) else (a', read $ T.unpack b')

    segs = map parseSeg segStrs

idText :: DefId -> Text
idText (DefId crate disambig segs) =
    T.intercalate "::" $ (crate <> "/" <> disambig) : map printSeg segs
  where
    printSeg (name, dis) = name <> "[" <> T.pack (show dis) <> "]"

instance Show DefId where
    show defId = T.unpack (idText defId)
instance IsString DefId where
    fromString str = textId (fromString str)
instance FromJSON DefId where
    parseJSON x = textId <$> parseJSON x

-- ignores filename and entry #s
instance Pretty DefId where
    pretty = viaShow

-- | The individual 'DefId' components of a 'DefId'. The first element is the
-- crate name, and the subsequent elements are the path segments. By convention,
-- 'ExplodedDefId's never contain disambiguators, which make them a useful way
-- to refer to identifiers in a slightly more stable format that does not depend
-- on the particulars of how a package is hashed.
type ExplodedDefId = [Text]

idKey :: DefId -> ExplodedDefId
idKey did = _didCrate did : map fst (_didPath did)

explodedDefIdPat :: ExplodedDefId -> TH.Q TH.Pat
explodedDefIdPat edid = [p| ((\did -> idKey did == edid) -> True) |]

textIdKey :: Text -> ExplodedDefId
textIdKey = idKey . textId

idInit :: DefId -> DefId
idInit (DefId crate disambig segs) = DefId crate disambig (init segs)

idLast :: DefId -> Text
idLast (DefId _ _ segs) = fst $ last segs


-- If a DefId is the name of a *static* method, we can find a trait name inside of it
-- by removing the "extra" part
getTraitName :: DefId -> DefId
getTraitName = idInit

cleanVariantName :: DefId -> Text
cleanVariantName = idLast

parseFieldName :: DefId -> Maybe Text
parseFieldName (DefId _ _ []) = Nothing
parseFieldName did = Just $ idLast did
