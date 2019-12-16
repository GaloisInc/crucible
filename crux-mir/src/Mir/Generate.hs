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


module Mir.Generate(generateMIR, translateMIR, translateAll) where

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

import System.FilePath
import System.IO
import qualified System.Process as Proc
import           System.Exit (ExitCode(..))
import           System.Directory (doesFileExist, removeFile, getModificationTime)
import           Data.Time.Clock (UTCTime)

import GHC.Stack

import Text.PrettyPrint.ANSI.Leijen (Pretty(..))

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C


import Mir.Mir
import Mir.JSON
import Mir.Intrinsics(MIR)
import Mir.PP()
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

compileMirJson :: Bool -> FilePath -> IO ()
compileMirJson keepRlib rustFile = do
    let outFile = rustFile -<.> "bin"

    -- TODO: don't hardcode -L library path
    (ec, _, _) <- Proc.readProcessWithExitCode "mir-json"
        [rustFile, "-L", "rlibs", "--crate-type=rlib", "--edition=2018"
        , "--cfg", "crux", "--cfg", "crux_top_level"
        , "-o", outFile] ""
    case ec of
        ExitFailure cd -> fail $
            "Error " ++ show cd ++ " while running mir-json on " ++ rustFile
        ExitSuccess    -> return ()

    when (not keepRlib) $ do
        doesFileExist outFile >>= \case
            True  -> removeFile outFile
            False -> return ()

maybeCompileMirJson :: Bool -> FilePath -> IO ()
maybeCompileMirJson keepRlib rustFile = do
    build <- needsRebuild (mirJsonOutFile rustFile) [rustFile]
    when build $ compileMirJson keepRlib rustFile


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
    [ "rlibs/libcore.mir"
    , "rlibs/libcompiler_builtins.mir"
    , "rlibs/libint512.mir"
    , "rlibs/libcrucible.mir"

    , "rlibs/liballoc.mir"
    , "rlibs/libstd.mir"
    , "rlibs/libunwind.mir"
    , "rlibs/libcfg_if.mir"
    , "rlibs/libhashbrown.mir"
    , "rlibs/liblibc.mir"

    , "rlibs/libbyteorder.mir"
    , "rlibs/libbytes.mir"
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
    maybeCompileMirJson keepRlib rustFile
    b <- maybeLinkJson (mirJsonOutFile rustFile : libJsonFiles) (linkOutFile rustFile)
    parseMir (linkOutFile rustFile) b
  | ext == ".json" = do
    b <- B.readFile inputFile
    parseMir inputFile b
  -- TODO: support directly reading .mir json+index format
  | otherwise = error $ show ext ++ " files are not supported"
  where
    (stem, ext) = splitExtension inputFile



readMir :: (HasCallStack, ?debug::Int) =>
           FilePath
        -> IO Collection
readMir path = B.readFile path >>= parseMir path

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
        return col

customLibLoc :: String
customLibLoc = "lib/"


-- | Translate a MIR collection to Crucible
translateMIR :: (HasCallStack, ?debug::Int, ?assertFalseOnError::Bool, ?printCrucible::Bool) 
   => CollectionState -> Collection -> C.HandleAllocator -> IO RustModule
translateMIR lib col halloc =
  let ?customOps = Mir.customOps in
  let col0 = let ?mirLib  = lib^.collection in rewriteCollection col
  in let ?libCS = lib in transCollection col0 halloc

-- | Translate a MIR crate *and* the standard library all at once
translateAll :: (?debug::Int, ?assertFalseOnError::Bool, ?printCrucible::Bool)
             => Collection -> IO (RustModule, C.AnyCFG MIR)
translateAll col = C.withHandleAllocator $ \halloc -> do
    mir      <- translateMIR mempty col halloc
    init_cfg <- transStatics (mir^.rmCS) halloc
    return $ (mir, init_cfg)

