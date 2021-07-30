{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
-- | This module defines a default loader for initial symbolic filesystem contents
--
-- It uses a simple convention to convert on-disk files and metadata into a
-- 'SymIO.InitialFileSystemContents'. This is not the only way to construct
-- initial filesystem contents, but it is a good default if a tool does not have
-- more specific needs.
--
-- The caller provides a single input: a path to a directory.  The directory
-- contains two things:
--
-- 1. A subdirectory named @root@ that contains the concrete files in the symbolic filesystem (i.e., the directory mapped to @/@)
-- 2. (Optional) A file named @symbolic-manifest.json@, which describes symbolic files and overlays
--
-- The symbolic manifest specifies the contents of symbolic files, including
-- constraints on symbolic values.  Furthermore, it enables users to specify
-- that concrete files in the provided filesystem have symbolic values overlaid
-- over the concrete values. If an overlay is specified in the symbolic
-- manifest, the referenced concrete file /must/ exist.
--
-- Note: future versions of this interface could support symbolic filesystems
-- stored in zip or tar files.
module Lang.Crucible.SymIO.Loader (
  loadInitialFiles
  ) where

import qualified Control.Exception as X
import qualified Data.Aeson as JSON
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           Data.Word ( Word64 )
import           GHC.Generics ( Generic )
import qualified System.Directory as SD
import           System.FilePath ( (</>) )
import qualified System.FilePath.Find as SFF
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.SymIO as SymIO

data FileSystemLoadError = ErrorDecodingJSON String
                         | forall k . FileSpecifiedAsSymbolicAndConcrete (SymIO.FDTarget k)

deriving instance Show FileSystemLoadError

instance X.Exception FileSystemLoadError

-- | The specification for the symbolic contents of a file in the symbolic
-- filesystem
--
-- There will be multiple specifications including:
--
--   * Complete symbolic file specifications (including concrete regions)
--   * Symbolic overlays on otherwise concrete files
data SymbolicFileContents =
  SymbolicContents { symbolicContentSize :: Word64
                   }
  deriving (Show, Generic)

instance JSON.FromJSON SymbolicFileContents

-- | A description of the contents of a symbolic filesystem
--
-- This includes high-level metadata and the specifications for symbolic files.
--
-- Note that the file paths are /absolute/ paths within the symbolic filesystem
data SymbolicManifest =
  SymbolicManifest { symbolicFiles :: [(FilePath, SymbolicFileContents)]
                   , useStdout :: Bool
                   , useStderr :: Bool
                   }
  deriving (Show, Generic)

instance JSON.FromJSON SymbolicManifest

-- | A file path that is absolute within the symbolic filesystem we are building
newtype AbsolutePath = AbsolutePath FilePath
  deriving (Eq, Ord, Show)

toInternalAbsolutePath
  :: FilePath
  -- ^ The
  -> FilePath
  -> AbsolutePath
toInternalAbsolutePath pfx x = AbsolutePath (fromMaybe x (List.stripPrefix pfx x))

createSymbolicFile
  :: (LCB.IsSymInterface sym)
  => sym
  -> (FilePath, SymbolicFileContents)
  -> IO (SymIO.FDTarget SymIO.In, [WI.SymBV sym 8])
createSymbolicFile sym (internalAbsPath, symContent) =
  case symContent of
    SymbolicContents { symbolicContentSize = numBytes } -> do
      bytes <- T.forM [0.. numBytes - 1] $ \byteNum -> do
        let symName = WI.safeSymbol (internalAbsPath ++ "_" ++ show byteNum)
        WI.freshConstant sym symName (WT.BaseBVRepr (PN.knownNat @8))
      return (SymIO.FileTarget internalAbsPath, bytes)

-- | Load the symbolic filesystem at the given file path
--
-- Note that this will throw an exception if:
--
--   * The symbolic manifest declares an overlay for a file that does not exist in the concrete portion of the filesystem
loadInitialFiles
  :: (LCB.IsSymInterface sym)
  => sym
  -> FilePath
  -> IO (SymIO.InitialFileSystemContents sym)
loadInitialFiles sym fsRoot = do
  -- FIXME: Use the lower-level fold primitive that enables exception handling;
  -- this version just spews errors to stderr, which is inappropriate.
  let concreteFilesRoot = fsRoot </> "root"
  concreteFilePaths <- SFF.find SFF.always SFF.always concreteFilesRoot

  -- Note that all of these paths are absolute *if* @fsRoot@ was absolute.
  -- Also, if it has leading .. components, they will be included.  We need to
  -- normalize these paths so that they have @fsRoot@ stripped off (and thus are
  -- absolute in the symbolic filesystem)
  let relativePaths = [ (p, toInternalAbsolutePath concreteFilesRoot p)
                      | p <- concreteFilePaths
                      ]
  concFiles <- mapM (\(p, name) -> (name,) <$> BS.readFile p) relativePaths
  let concMap = Map.fromList [ (SymIO.FileTarget p, bytes) | (AbsolutePath p, bytes) <- concFiles ]

  let manifestFilePath = fsRoot </> "system-manifest.json"
  hasManifest <- SD.doesFileExist manifestFilePath
  case hasManifest of
    False ->
      return SymIO.InitialFileSystemContents { SymIO.concreteFiles = concMap
                                             , SymIO.symbolicFiles = Map.empty
                                             , SymIO.useStdout = False
                                             , SymIO.useStderr = False
                                             }
    True -> do
      manifestBytes <- BS.readFile manifestFilePath
      case JSON.eitherDecodeStrict manifestBytes of
        Left msg -> X.throwIO (ErrorDecodingJSON msg)
        Right symManifest -> do
          symFiles <- mapM (createSymbolicFile sym) (symbolicFiles symManifest)
          F.forM_ symFiles $ \(fdTarget, _) -> do
            case Map.lookup fdTarget concMap of
              Nothing -> return ()
              Just _ -> X.throwIO (FileSpecifiedAsSymbolicAndConcrete fdTarget)
          return SymIO.InitialFileSystemContents { SymIO.concreteFiles = concMap
                                                 , SymIO.symbolicFiles = Map.fromList symFiles
                                                 , SymIO.useStdout = useStdout symManifest
                                                 , SymIO.useStderr = useStderr symManifest
                                                 }
