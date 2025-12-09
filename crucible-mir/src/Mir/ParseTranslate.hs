{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
-----------------------------------------------------------------------
-- |
-- Module           : Mir.ParseTranslate
-- Description      : Produce MIR AST and translate to Crucible
-- Copyright        : (c) Galois, Inc 2018-2023
-- License          : BSD3
-- Stability        : provisional
--
-- Entry points for parsing and translating the MIR AST into Crucible.
-----------------------------------------------------------------------


module Mir.ParseTranslate (parseMIR, translateMIR) where

import Control.Lens hiding((<.>))
import Control.Monad (unless, when)

import qualified Data.Aeson as J
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.ByteString.Lazy as B
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.Word (Word64)

import GHC.Stack

import Prettyprinter (Pretty(..))

import qualified Lang.Crucible.FunctionHandle as C


import Mir.Mir (Collection(..), namedTys, tiTy, tiNeedsDrop, tiLayout, version)
import Mir.JSON ()
import Mir.GenericOps (uninternTys)
import Mir.Pass(rewriteCollection)
import Mir.Generator(RustModule(..))
import Mir.Trans(transCollection)
import qualified Mir.TransCustom as Mir (customOps)

import Debug.Trace


-- If you update the supported mir-json schema version below, make sure to also
-- update the crux-mir README accordingly.
supportedSchemaVersion :: Word64
supportedSchemaVersion = 7

-- | Parse a MIR JSON file to a 'Collection'. If parsing fails, attempt to give
-- a more informative error message if the MIR JSON schema version is
-- mismatched.
parseMIR :: (HasCallStack, ?debug::Int) =>
            FilePath
         -> B.ByteString
         -> IO Collection
parseMIR path f = do
    col <-
      case J.eitherDecode @Collection f of
        Left msg -> fallback msg
        Right col -> pure col
    checkSchemaVersion (col ^. version)
    when (?debug > 5) $ do
      traceM "--------------------------------------------------------------"
      traceM $ "Loaded module: " ++ path
      traceM $ show (pretty col)
      traceM "--------------------------------------------------------------"
    return $ uninternMir col
  where
    checkSchemaVersion :: Word64 -> IO ()
    checkSchemaVersion actualSchemaVersion =
      unless (actualSchemaVersion == supportedSchemaVersion) $
        fail $ unlines
          [ path ++ " uses an unsupported mir-json schema version: "
                 ++ show actualSchemaVersion
          , "This release only supports schema version "
            ++ show supportedSchemaVersion ++ "."
          , "(See https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md"
          , "for more details on what the schema version means.)"
          ]

    -- If parsing fails, try to interpret the file as a raw JSON J.Value and
    -- see if the schema version number (if one exists) matches. If they are
    -- mismatched, then report this, as this is a pretty significant clue that
    -- the user set up mir-json incorrectly. Otherwise, report a generic JSON
    -- parse error.
    fallback ::
      forall a.
      -- | The error message received upon failing to parse the JSON file as a
      -- 'Collection'. Raise this error if all other attempts to report a more
      -- specific error message fail.
      String ->
      IO a
    fallback jsonParseErrMsg = do
      -- First parse a J.Value, without looking at what the contents of the
      -- J.Value are. This is a bit inefficient, as we already attempted to
      -- parse the JSON file's contents earlier, and this will attempt to parse
      -- it yet again. We accept the inefficiency here because we know that we
      -- are going to report an error message regardless.
      mirJson <-
        case J.eitherDecode @J.Value f of
          Left msg -> fail $ path ++ " is not a valid JSON file: " ++ msg
          Right mirJson -> pure mirJson
      -- Next, check that the J.Value is an J.Object.
      mirJsonObj <-
        case mirJson of
          J.Object obj -> pure obj
          _ -> fail $ path ++ " does not contain a JSON object"
      -- Confirm that one of the J.Object's keys is "version".
      mirJsonVer <-
        case KeyMap.lookup "version" mirJsonObj of
          Just mirJsonVer -> pure mirJsonVer
          Nothing -> fail $ path ++ " does not contain a \"version\" field"
      -- Validate that the "version" key maps to a number.
      actualSchemaVersion <-
        case J.fromJSON @Word64 mirJsonVer of
          J.Error msg ->
            fail $ path ++ " has a \"version\" field, but it is not a number: " ++ msg
          J.Success actualSchemaVersion -> pure actualSchemaVersion
      -- As a sanity-check, ensure that the number which "version" maps to is a
      -- supported JSON schema version. If not, error out early.
      checkSchemaVersion actualSchemaVersion
      -- If we have reached this point, then we know that the JSON file failed
      -- to parse as a Collection despite the schema versions matching, so
      -- something has gone awry. Report a generic JSON parse error to the user
      -- as a last resort.
      fail $ "JSON decoding of " ++ path ++ " failed: " ++ jsonParseErrMsg

uninternMir :: Collection -> Collection
uninternMir col =
  (uninternTys unintern (col { _namedTys = mempty }))
    { -- the keys of the layouts map need to be uninterned
      _layouts = M.fromList [(x ^. tiTy, x ^. tiLayout) | x <- M.elems tyMap]
    , _needDrops = Set.fromList [x ^. tiTy | x <- M.elems tyMap, x ^. tiNeedsDrop]
    }
  where
    -- NB: knot-tying is happening here.  Some values in `tyMap` depend on
    -- other values.  This should be okay: the original `rustc::ty::Ty`s are
    -- acyclic, so the entries in `tyMap` should be too.
    tyMap = fmap (uninternTys unintern) (col ^. namedTys)
    unintern name = case M.lookup name tyMap of
        Nothing -> error $ "missing " ++ show name ++ " in type map"
        Just tyInfo -> tyInfo ^. tiTy


-- | Translate a MIR collection to Crucible
translateMIR :: (HasCallStack, ?debug::Int, ?assertFalseOnError::Bool, ?printCrucible::Bool)
   => Collection -> C.HandleAllocator -> IO RustModule
translateMIR col halloc =
  let ?customOps = Mir.customOps in
  let col0 = rewriteCollection col
  in transCollection col0 halloc
