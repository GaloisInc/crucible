{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


module Mir.DefId
( DefId
, textId
, idText

, ExplodedDefId
, idKey

, getTraitName
, cleanVariantName
, parseFieldName

, normDefId
, normDefIdPat
) where

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
    -- | The name of the enclosing crate.
    { did_crate :: Text
    -- | The disambiguator of the enclosing crate.  These are strings, in a
    -- different format than the integer disambiguators used for normal path
    -- segments.
    , did_crate_disambig :: Text
    -- | The segments of the path.
    , did_path :: [Segment]
    }
  deriving (Eq, Ord, Generic)

-- | The crate disambiguator hash produced when the crate metadata string is
-- empty.  This is the disambiguator for all sysroot crates, which are the only
-- ones we override.
defaultDisambiguator :: Text
defaultDisambiguator = "3a1fbbbh"

-- | Parse a string into a `DefId`.
--
-- For convenience when writing literal paths in the Haskell source, both types
-- of disambiguators are optional.  If the crate disambiguator is omitted, then
-- it's assumed to be `defaultDisambiguator`, and if a segment disambiguator is
-- omitted elsewhere in the path, it's assumed to be zero.  So you can write,
-- for example, `core::option::Option`, and parsing will expand it to the
-- canonical form `core/3a1fbbbh::option[0]::Option[0]`.
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
    pretty = pretty . show


type ExplodedDefId = [Text]
idKey :: DefId -> ExplodedDefId
idKey did = did_crate did : map fst (did_path did)


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

-- | Normalize a DefId string.  This allows writing down path strings in a more
-- readable form.
normDefId :: Text -> Text
normDefId s = idText $ textId s

-- | Like `normDefId`, but produces a Template Haskell pattern.  Useful for
-- defining pattern synonyms that match a specific `TyAdt` type constructor.
normDefIdPat :: Text -> TH.Q TH.Pat
normDefIdPat s = return $ TH.LitP $ TH.StringL $ T.unpack $ normDefId s
