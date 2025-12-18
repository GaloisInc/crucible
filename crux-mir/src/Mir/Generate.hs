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

import Data.List (stripPrefix, isPrefixOf)

import qualified Data.Foldable as Foldable
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString as BS

import System.Environment
import System.FilePath
import System.IO
import qualified System.Process as Proc
import           System.Exit (ExitCode(..))
import           System.Directory (doesFileExist, removeFile, getModificationTime, listDirectory)
import           Data.Time.Clock (UTCTime)

import GHC.Stack

import Lang.Crucible.Panic (panic)

import Mir.Mir
import Mir.Options (MIROptions(..))
import Mir.Defaults (defaultRustEditionFlag)
import Mir.ParseTranslate (parseMIR)
import Mir.PP()

import qualified Crux.Config.Common as Crux (CruxOptions(..), OutputOptions(..))
import qualified Crux.Config.Load as Crux (ColorOptions(..))

import Debug.Trace



getModificationTimeIfExists :: FilePath -> IO (Maybe UTCTime)
getModificationTimeIfExists path = doesFileExist path >>= \case
    False -> return Nothing
    True -> Just <$> getModificationTime path

needsRebuild :: FilePath -> [FilePath] -> IO Bool
needsRebuild output inputs = do
    mbOutTime <- getModificationTimeIfExists output
    mbInTimes <- mapM getModificationTimeIfExists inputs
    return $ case (mbOutTime, sequence mbInTimes) of
        (Nothing, _) -> True
        (_, Nothing) -> True
        (Just outTime, Just inTimes) -> any (> outTime) inTimes


mirJsonOutFile :: FilePath -> FilePath
mirJsonOutFile rustFile = rustFile -<.> "mir"

getRlibsDir :: (?defaultRlibsDir :: FilePath) => IO FilePath
getRlibsDir = maybe ?defaultRlibsDir id <$> lookupEnv "CRUX_RUST_LIBRARY_PATH"

buildMirJsonArgs :: [String]   -- ^ base/default args (no edition)
                 -> [String]   -- ^ extra args (from MIROptions.mirJsonArgs)
                 -> [String]
buildMirJsonArgs base extras =
  let hasEdition  = any isEditionArg extras
      -- rustc rejects multiple --edition flags, so if the user supplies
      -- an explicit --edition via --mir-json-arg, we must *not* also add
      -- the default --edition flag here.
      editionPart = if hasEdition then [] else [defaultRustEditionFlag]
  in base ++ editionPart ++ extras

isEditionArg :: String -> Bool
isEditionArg s =
  s == "--edition" || "--edition=" `isPrefixOf` s

compileMirJson :: (?defaultRlibsDir :: FilePath) => Crux.CruxOptions -> MIROptions -> Bool -> FilePath -> IO ()
compileMirJson cruxOpts mirOpts keepRlib rustFile = do
    let outFile = rustFile -<.> "bin"

    rlibsDir <- getRlibsDir
    rlibsFiles <- listDirectory rlibsDir
    -- rustc produces colorful error messages, so preserve the colors whenever
    -- possible when printing the error messages back out to the user.
    let colorOpts
          | Crux.noColorsErr $ Crux.colorOptions $ Crux.outputOptions cruxOpts
          = []
          | otherwise
          = ["--color=always"]
    -- TODO: don't hardcode -L library path
    let baseArgs =
          [ rustFile
          , "-L", rlibsDir
          , "--crate-type=rlib"
          ]
          ++ concat
               [ ["--extern", libName ++ "=" ++ rlibsDir </> file]
               | file <- rlibsFiles
               , (baseName, ".rlib") <- [splitExtension file]
               , Just libName <- [stripPrefix "lib" baseName]
               ]
          ++ colorOpts
          ++ [ "--cfg", "crux", "--cfg", "crux_top_level"
             , "-Z", "ub-checks=false"
             , "-o", outFile
             ]

    let extraMirArgs = Foldable.toList (mirJsonArgs mirOpts)

    -- Add default edition if needed, then append extraMirArgs
    let finalArgs = buildMirJsonArgs baseArgs extraMirArgs

    -- If verbosity is enabled (e.g., via -v), print the mir-json command
    let verbosity = Crux.simVerbose (Crux.outputOptions cruxOpts)
    when (verbosity > 1) $
      hPutStrLn stderr $
        "[crux-mir] mir-json " ++ unwords finalArgs

    let cp = Proc.proc "mir-json" finalArgs
    (ec, _sout, serr) <- Proc.readCreateProcessWithExitCode cp ""
    case ec of
        ExitFailure cd -> do
            hPutStrLn stderr serr
            fail $ "Error " ++ show cd ++ " while running mir-json on " ++ rustFile
        ExitSuccess    -> return ()

    when (not keepRlib) $ do
        doesFileExist outFile >>= \case
            True  -> removeFile outFile
            False -> return ()

maybeCompileMirJson :: (?defaultRlibsDir :: FilePath) => Crux.CruxOptions -> MIROptions -> Bool -> FilePath -> IO ()
maybeCompileMirJson cruxOpts mirOpts keepRlib rustFile = do
    build <- needsRebuild (mirJsonOutFile rustFile) [rustFile]
    when build $ compileMirJson cruxOpts mirOpts keepRlib rustFile


linkJson :: [FilePath] -> IO B.ByteString
linkJson jsonFiles = Proc.withCreateProcess cp $
    \mbHStdin mbHStdout mbHStderr ph ->
      case (mbHStdin, mbHStdout, mbHStderr) of
        (Nothing, Just hStdout, Nothing) -> do
          hSetBinaryMode hStdout True
          b <- BS.hGetContents hStdout
          ec <- Proc.waitForProcess ph
          case ec of
              ExitFailure cd -> fail $
                  "Error " ++ show cd ++ " while running mir-json on " ++ show jsonFiles
              ExitSuccess    -> return ()
          return $ B.fromStrict b
        _ ->
          panic
            "linkJson"
            [ "Unexpected process handles"
            , "stdin:  " ++ show mbHStdin
            , "stdout: " ++ show mbHStdout
            , "stderr: " ++ show mbHStderr
            ]
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


-- | Run mir-json on the input, generating lib file on disk
-- NOTE: If the rust file has not been modified since the
-- last .mir file was created, this function does nothing
-- This function uses 'failIO' if any error occurs
generateMIR :: (HasCallStack, ?debug::Int, ?defaultRlibsDir :: FilePath) =>
               Crux.CruxOptions
            -> MIROptions
            -> FilePath          -- ^ location of input file
            -> Bool              -- ^ `True` to keep the generated .rlib
            -> IO Collection
generateMIR cruxOpts mirOpts inputFile keepRlib
  | ext == ".rs" = do
    when (?debug > 2) $
        traceM $ "Generating " ++ stem <.> "mir"
    let rustFile = inputFile
    maybeCompileMirJson cruxOpts mirOpts keepRlib rustFile
    rlibsDir <- getRlibsDir
    rlibsFiles <- listDirectory rlibsDir
    let libJsonPaths = [rlibsDir </> file | file <- rlibsFiles, takeExtension file == ".mir"]
    b <- maybeLinkJson (mirJsonOutFile rustFile : libJsonPaths) (linkOutFile rustFile)
    parseMIR (linkOutFile rustFile) b
  | ext == ".json" = do
    b <- B.readFile inputFile
    parseMIR inputFile b
  -- TODO: support directly reading .mir json+index format
  | otherwise = error $ show ext ++ " files are not supported"
  where
    (stem, ext) = splitExtension inputFile
