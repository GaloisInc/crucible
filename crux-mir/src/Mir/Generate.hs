{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
-----------------------------------------------------------------------
-- |
-- Module           : Mir.Generate
-- Description      : Produce MIR AST and translate to Crucible
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Stability        : provisional
--
-- This module sets up the process to compile the rust input file,
-- extract the json representation, and parse as the MIR AST.
-- Also, entry point for translating MIR AST into crucible.
-----------------------------------------------------------------------


module Mir.Generate(generateMIR, translateMIR) where

import Data.Foldable(fold)

import Control.Lens hiding((<.>))
import Control.Monad (when)
import Control.Monad.ST

import Control.Monad.IO.Class

import qualified Data.Aeson as J
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString as BS
import qualified Data.Map as M
import qualified Data.Text as T

import System.Environment
import System.FilePath
import System.IO
import qualified System.Process as Proc
import           System.Exit (ExitCode(..))
import           System.Directory (doesFileExist, removeFile, getModificationTime)
import           Data.Time.Clock (UTCTime)

import GHC.Stack

import Prettyprinter (Pretty(..))

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C


import Mir.Mir
import Mir.JSON
import Mir.Intrinsics(MIR)
import Mir.PP()
import Mir.GenericOps (uninternTys)
import Mir.Pass(rewriteCollection)
import Mir.Generator(RustModule(..),CollectionState(..), rmCS, rmCFGs, collection)
import Mir.Trans(transCollection, transStatics)
import qualified Mir.TransCustom as Mir

import Debug.Trace 


getModificationTimeIfExists :: FilePath -> IO (Maybe UTCTime)
getModificationTimeIfExists path = doesFileExist path >>= \case
    False -> return Nothing
    True -> Just <$> getModificationTime path

needsRebuild :: FilePath -> [FilePath] -> IO Bool
needsRebuild output inputs = do
    outTime <- getModificationTimeIfExists output
    inTimes <- mapM getModificationTimeIfExists inputs
    return $ case (outTime, sequence inTimes) of
        (Nothing, _) -> True
        (_, Nothing) -> True
        (Just outTime, Just inTimes) -> any (> outTime) inTimes


mirJsonOutFile :: FilePath -> FilePath
mirJsonOutFile rustFile = rustFile -<.> "mir"

getRlibsDir :: IO FilePath
getRlibsDir = maybe "rlibs" id <$> lookupEnv "CRUX_RUST_LIBRARY_PATH"

compileMirJson :: Bool -> Bool -> FilePath -> IO ()
compileMirJson keepRlib quiet rustFile = do
    let outFile = rustFile -<.> "bin"

    rlibsDir <- getRlibsDir
    -- TODO: don't hardcode -L library path
    let cp = Proc.proc "mir-json"
            [rustFile, "-L", rlibsDir, "--crate-type=rlib", "--edition=2018"
            , "--cfg", "crux", "--cfg", "crux_top_level"
            , "-o", outFile]
    let cp' = if not quiet then cp else
            (cp { Proc.std_out = Proc.NoStream, Proc.std_err = Proc.NoStream })
    ec <- Proc.withCreateProcess cp' $ \_ _ _ ph -> Proc.waitForProcess ph
    case ec of
        ExitFailure cd -> fail $
            "Error " ++ show cd ++ " while running mir-json on " ++ rustFile
        ExitSuccess    -> return ()

    when (not keepRlib) $ do
        doesFileExist outFile >>= \case
            True  -> removeFile outFile
            False -> return ()

maybeCompileMirJson :: Bool -> Bool -> FilePath -> IO ()
maybeCompileMirJson keepRlib quiet rustFile = do
    build <- needsRebuild (mirJsonOutFile rustFile) [rustFile]
    when build $ compileMirJson keepRlib quiet rustFile


linkJson :: [FilePath] -> IO B.ByteString
linkJson jsonFiles = Proc.withCreateProcess cp $
    \Nothing (Just stdout) Nothing ph -> do
        hSetBinaryMode stdout True
        b <- BS.hGetContents stdout
        ec <- Proc.waitForProcess ph
        case ec of
            ExitFailure cd -> fail $
                "Error " ++ show cd ++ " while running mir-json on " ++ show jsonFiles
            ExitSuccess    -> return ()
        return $ B.fromStrict b
  where
    cp = (Proc.proc "mir-json-dce" jsonFiles) { Proc.std_out = Proc.CreatePipe }

linkOutFile :: FilePath -> FilePath
linkOutFile rustFile = rustFile -<.> "all.mir"

maybeLinkJson :: [FilePath] -> FilePath -> IO B.ByteString
maybeLinkJson jsonFiles cacheFile = do
    build <- needsRebuild cacheFile jsonFiles
    if build then do
        b <- linkJson jsonFiles
        B.writeFile cacheFile b
        return b
    else
        B.readFile cacheFile


libJsonFiles =
    [ "libcore.mir"
    , "libcompiler_builtins.mir"
    , "libint512.mir"
    , "libcrucible.mir"

    , "liballoc.mir"
    , "libstd.mir"
    , "libunwind.mir"
    , "libcfg_if.mir"
    , "libhashbrown.mir"
    , "liblibc.mir"

    , "libbyteorder.mir"
    , "libbytes.mir"
    ]


-- | Run mir-json on the input, generating lib file on disk
-- NOTE: If the rust file has not been modified since the
-- last .mir file was created, this function does nothing
-- This function uses 'failIO' if any error occurs
generateMIR :: (HasCallStack, ?debug::Int) =>
               FilePath          -- ^ location of input file
            -> Bool              -- ^ `True` to keep the generated .rlib
            -> IO Collection
generateMIR inputFile keepRlib
  | ext == ".rs" = do
    when (?debug > 2) $
        traceM $ "Generating " ++ stem <.> "mir"
    let rustFile = inputFile
    maybeCompileMirJson keepRlib (?debug <= 2) rustFile
    rlibsDir <- getRlibsDir
    let libJsonPaths = map (rlibsDir </>) libJsonFiles
    b <- maybeLinkJson (mirJsonOutFile rustFile : libJsonPaths) (linkOutFile rustFile)
    parseMir (linkOutFile rustFile) b
  | ext == ".json" = do
    b <- B.readFile inputFile
    parseMir inputFile b
  -- TODO: support directly reading .mir json+index format
  | otherwise = error $ show ext ++ " files are not supported"
  where
    (stem, ext) = splitExtension inputFile



parseMir :: (HasCallStack, ?debug::Int) =>
            FilePath
         -> B.ByteString
         -> IO Collection
parseMir path f = do
  let c = (J.eitherDecode f) :: Either String Collection
  case c of
      Left msg -> fail $ "JSON Decoding of " ++ path ++ " failed: " ++ msg
      Right col -> do
        when (?debug > 5) $ do
          traceM "--------------------------------------------------------------"
          traceM $ "Loaded module: " ++ path
          traceM $ show (pretty col)
          traceM "--------------------------------------------------------------"  
        return $ uninternMir col

uninternMir :: Collection -> Collection
uninternMir col = uninternTys unintern (col { _namedTys = mempty })
  where
    -- NB: knot-tying is happening here.  Some values in `tyMap` depend on
    -- other values.  This should be okay: the original `rustc::ty::Ty`s are
    -- acyclic, so the entries in `tyMap` should be too.
    tyMap = fmap (uninternTys unintern) (col^.namedTys)
    unintern name = case M.lookup name tyMap of
        Nothing -> error $ "missing " ++ show name ++ " in type map"
        Just ty -> ty


-- | Translate a MIR collection to Crucible
translateMIR :: (HasCallStack, ?debug::Int, ?assertFalseOnError::Bool, ?printCrucible::Bool) 
   => CollectionState -> Collection -> C.HandleAllocator -> IO RustModule
translateMIR lib col halloc =
  let ?customOps = Mir.customOps in
  let col0 = let ?mirLib  = lib^.collection in rewriteCollection col
  in let ?libCS = lib in transCollection col0 halloc
