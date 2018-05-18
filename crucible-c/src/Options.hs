module Options where

import System.FilePath

data Options = Options
  { clangBin :: FilePath
    -- ^ Path to Clang binary

  , libDir   :: FilePath
    -- ^ Path to our C file

  , outDir   :: FilePath
    -- ^ Store results in this directory

  , inputFile :: FilePath
    -- ^ The file to analyze
  }

optsBCFile :: Options -> FilePath
optsBCFile opts =
  case takeExtension (inputFile opts) of
    ".bc" -> inputFile opts
    _     -> outDir opts </> "input.bc"

