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
-----------------------------------------------------------------------


module Mir.Generate(generateMIR) where

import Control.Monad (when)

import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString as BS

import System.Environment
import System.FilePath
import System.IO
import qualified System.Process as Proc
import           System.Exit (ExitCode(..))
import           System.Directory (doesFileExist, removeFile, getModificationTime)
import           Data.Time.Clock (UTCTime)

import GHC.Stack


import Mir.Mir
import Mir.ParseTranslate (parseMIR)
import Mir.PP()

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

getRlibsDir :: (?defaultRlibsDir :: FilePath) => IO FilePath
getRlibsDir = maybe ?defaultRlibsDir id <$> lookupEnv "CRUX_RUST_LIBRARY_PATH"

compileMirJson :: (?defaultRlibsDir :: FilePath) => Bool -> Bool -> FilePath -> IO ()
compileMirJson keepRlib quiet rustFile = do
    let outFile = rustFile -<.> "bin"

    rlibsDir <- getRlibsDir
    -- TODO: don't hardcode -L library path
    let cp =
          Proc.proc "mir-json" $
            [rustFile, "-L", rlibsDir, "--crate-type=rlib", "--edition=2021"] ++
            concat
              [ [ "--extern"
                , lib ++ "=" ++ rlibsDir </> "lib" ++ lib <.> "rlib"
                ]
              | lib <- libDependencies ] ++
            [ "--cfg", "crux", "--cfg", "crux_top_level"
            , "-Z", "ub-checks=false"
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

maybeCompileMirJson :: (?defaultRlibsDir :: FilePath) => Bool -> Bool -> FilePath -> IO ()
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

libDependencies :: [FilePath]
libDependencies =
    -- std and its dependencies
    [ "addr2line"
    , "adler2"
    , "alloc"
    , "cfg_if"
    , "compiler_builtins"
    , "core"
    , "crucible"
    , "getopts"
    , "gimli"
    , "hashbrown"
    , "libc"
    , "memchr"
    , "miniz_oxide"
    , "object"
    , "panic_abort"
    , "panic_unwind"
    , "proc_macro"
    , "rustc_demangle"
    , "rustc_std_workspace_alloc"
    , "rustc_std_workspace_core"
    , "rustc_std_workspace_std"
    , "std_detect"
    , "std"
    , "test"
    , "unicode_width"
    , "unwind"
    -- additional libs
    , "crucible"
    , "int512"
    , "byteorder"
    , "bytes"
    ]


-- | Run mir-json on the input, generating lib file on disk
-- NOTE: If the rust file has not been modified since the
-- last .mir file was created, this function does nothing
-- This function uses 'failIO' if any error occurs
generateMIR :: (HasCallStack, ?debug::Int, ?defaultRlibsDir :: FilePath) =>
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
    let libJsonPaths = [rlibsDir </> "lib" ++ lib <.> "mir" | lib <- libDependencies]
    b <- maybeLinkJson (mirJsonOutFile rustFile : libJsonPaths) (linkOutFile rustFile)
    parseMIR (linkOutFile rustFile) b
  | ext == ".json" = do
    b <- B.readFile inputFile
    parseMIR inputFile b
  -- TODO: support directly reading .mir json+index format
  | otherwise = error $ show ext ++ " files are not supported"
  where
    (stem, ext) = splitExtension inputFile
