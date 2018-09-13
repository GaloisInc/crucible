module Main (main) where

import Control.Exception
import Control.Monad (when)
import Distribution.PackageDescription
  ( BuildInfo
  , GenericPackageDescription
  , HookedBuildInfo
  )
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program.Types
import Distribution.Simple.Setup
import System.Directory
import System.FilePath
import System.IO.Error
import System.Process

import Distribution.Simple.Utils
import Distribution.PackageDescription hiding (Flag)

-- | Path to Protocol buffer file.
pbPath :: FilePath
pbPath = "proto" </> "crucible.proto"

-- | Module name for protocol buffer file.
protoModule :: String
protoModule = "Lang.Crucible.Proto"

-- | Path to protocol buffer file.
protoOutPath :: FilePath
protoOutPath = "Lang" </> "Crucible" </> "Proto.hs"

needsRebuild :: FilePath -> FilePath -> IO Bool
needsRebuild src_path tgt_path = do
  let h e | isPermissionError e = return True
          | isDoesNotExistError e = return True
          | otherwise = throwIO e
  handle h $ do
    src_time <- getModificationTime src_path
    tgt_time <- getModificationTime tgt_path
    return (tgt_time < src_time)

runHPB :: Args -> BuildFlags -> IO HookedBuildInfo
runHPB args flags = do
  putStrLn "Running preBuild"
  case buildDistPref flags of
    NoFlag -> do
      fail "Path not specified."
    Flag distPath -> do
      let out_dir = distPath </> "build"
      mkProto out_dir
      preBuild simpleUserHooks args flags

-- | Write out a file to the protocol buffe to given directory.
mkProto :: FilePath -> IO ()
mkProto out_dir = do
  let hpb_path = "hpb"
  let outPath = out_dir </> protoOutPath
  b <- needsRebuild pbPath outPath
  when b $ do
    callProcess hpb_path [ pbPath
                         , "--out=" ++ out_dir
                         , "--module=" ++ protoModule
                         ]

dummyPreprocessor :: BuildInfo -> LocalBuildInfo -> ComponentLocalBuildInfo -> PreProcessor
dummyPreprocessor build local _clbi = PreProcessor {
  platformIndependent = True,
  runPreProcessor =
    mkSimplePreProcessor $ \inFile outFile verbosity -> do
      notice verbosity (inFile ++ " is being preprocessed to " ++ outFile)
      return ()
  }

main :: IO ()
main = do
  defaultMainWithHooks simpleUserHooks
    { hookedPrograms = [ simpleProgram "hpb" ]
    , preBuild = runHPB
    , hookedPreProcessors = [("hproto", dummyPreprocessor)]
    }
