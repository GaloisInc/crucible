{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
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
import qualified Data.ByteString.Lazy as B
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.Word (Word64)

import GHC.Stack

import Prettyprinter (Pretty(..))

import qualified Lang.Crucible.FunctionHandle as C


import Mir.Mir (Collection(..), namedTys, version, tiTy, tiNeedsDrop, tiLayout)
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
supportedSchemaVersion = 5

parseMIR :: (HasCallStack, ?debug::Int) =>
            FilePath
         -> B.ByteString
         -> IO Collection
parseMIR path f = do
  let c = (J.eitherDecode f) :: Either String Collection
  case c of
      Left msg -> fail $ "JSON Decoding of " ++ path ++ " failed: " ++ msg
      Right col -> do
        unless (col ^. version == supportedSchemaVersion) $
          fail $ unlines
            [ path ++ " uses an unsupported mir-json schema version: "
                   ++ show (col ^. version)
            , "This crux-mir release only supports schema version "
              ++ show supportedSchemaVersion ++ "."
            , "(See https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md"
            , "for more details on what the schema version means.)"
            ]
        when (?debug > 5) $ do
          traceM "--------------------------------------------------------------"
          traceM $ "Loaded module: " ++ path
          traceM $ show (pretty col)
          traceM "--------------------------------------------------------------"
        return $ uninternMir col

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
