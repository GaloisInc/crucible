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


module Mir.Generate(generateMIR, translateMIR, translateAll, loadPrims) where

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
    -- TODO: don't hardcode -L library path
    (ec, _, _) <- Proc.readProcessWithExitCode "mir-json"
        [rustFile, "-L", "rlibs", "--crate-type=rlib", "--edition=2018"
        , "--cfg", "crux", "--cfg", "crux_top_level"] ""
    case ec of
        ExitFailure cd -> fail $
            "Error " ++ show cd ++ " while running mir-json on " ++ rustFile
        ExitSuccess    -> return ()

    when (not keepRlib) $ do
        let rlibFile = ("lib" ++ takeBaseName rustFile) <.> "rlib"
        doesFileExist rlibFile >>= \case
            True  -> removeFile rlibFile
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
    [ "lib/libcore/lib.mir"
    , "lib/compiler_builtins.mir"
    , "lib/int512.mir"
    , "lib/crucible/lib.mir"

    , "lib/liballoc/lib.mir"
    , "lib/libstd/lib.mir"
    , "lib/libunwind/lib.mir"
    , "lib/cfg-if/src/lib.mir"
    , "lib/hashbrown/src/lib.mir"
    , "lib/libc/src/lib.mir"

    , "lib/bytes.mir"
    ]


-- | Run mir-json on the input, generating lib file on disk
-- NOTE: If the rust file has not been modified since the
-- last .mir file was created, this function does nothing
-- This function uses 'failIO' if any error occurs
generateMIR :: (HasCallStack, ?debug::Int) =>
               FilePath          -- ^ location of input file
            -> String            -- ^ file to processes, without extension
            -> Bool              -- ^ `True` to keep the generated .rlib
            -> IO Collection
generateMIR dir name keepRlib = do
    let rustFile = dir </> name <.> "rs"
    maybeCompileMirJson keepRlib rustFile
    b <- maybeLinkJson (mirJsonOutFile rustFile : libJsonFiles) (linkOutFile rustFile)
    parseMir (linkOutFile rustFile) b


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

-- | load the rs file containing the standard library
loadPrims :: (?debug::Int) => Bool -> IO Collection
loadPrims useStdLib = return mempty

  {-
  let coreLib = if useStdLib then "lib" else "lib_func_only"
  -- Only print debugging info in the standard library at high debugging levels
  colCoreLib <- let ?debug = ?debug - 3 in
         generateMIR "mir-lib/src/" coreLib False

  colStdLib <- let ?debug = ?debug - 3 in
         generateMIR "lib/std/" "lib" False

  -- TODO: need to compile these libs *before* running mir-json on the main file
  let customLibs = ["crucible", "int512"]
  colCustoms <- let ?debug = ?debug - 3 in
         mapM (\libName -> generateMIR customLibLoc libName True) customLibs

  let col = mconcat $ colCoreLib : colStdLib : colCustoms
  -}

{-
  col <- mconcat <$> mapM readMir
    [ "lib/libcore/lib.mir"
    , "lib/compiler_builtins.mir"
    , "lib/int512.mir"
    , "lib/crucible/lib.mir"
    , "lib/std/lib.mir"
    , "lib/bytes.mir"
    ]

  when (?debug > 6) $ do
    traceM "--------------------------------------------------------------"
    traceM $ "Complete Collection: "
    traceM $ show (pretty col)
    traceM "--------------------------------------------------------------"  

  return col
-}



-- | Translate a MIR collection to Crucible
translateMIR :: (HasCallStack, ?debug::Int, ?assertFalseOnError::Bool, ?printCrucible::Bool) 
   => CollectionState -> Collection -> C.HandleAllocator s -> ST s RustModule
translateMIR lib col halloc =
  let ?customOps = Mir.customOps in
  let col0 = let ?mirLib  = lib^.collection in rewriteCollection col
  in let ?libCS = lib in transCollection col0 halloc

-- | Translate a MIR crate *and* the standard library all at once
translateAll :: (?debug::Int, ?assertFalseOnError::Bool, ?printCrucible::Bool)
             => Bool -> Collection -> IO (RustModule, C.AnyCFG MIR)
translateAll usePrims col = do
  prims <- liftIO $ loadPrims usePrims
  let (a,b) = runST $ C.withHandleAllocator $ \halloc -> do
               pmir     <- translateMIR mempty prims halloc
               mir      <- translateMIR (pmir^.rmCS) col halloc
               init_cfg <- transStatics (mir^.rmCS) halloc
               return $ (pmir <> mir, init_cfg)
  return $ (a,b)

