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
-- It also includes the top-level translation function to produce the
-- Crucible CFG from this AST.
-----------------------------------------------------------------------


module Mir.Generate(generateMIR, RustModule(..), translateMIR) where

import Control.Lens hiding((<.>))
import Control.Monad (when)
import Control.Monad.ST

import qualified Data.Aeson as J
import qualified Data.ByteString.Lazy as B
import qualified Data.Map as M
import qualified Data.Text as T

import System.FilePath
import qualified System.Process as Proc
import           System.Exit (ExitCode(..))
import           System.Directory (doesFileExist, removeFile, getModificationTime)

import GHC.Stack

import Text.PrettyPrint.ANSI.Leijen (Pretty(..))

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C


import Mir.Mir
import Mir.JSON
import Mir.Intrinsics(MIR)
import Mir.PP()
import Mir.Pass(rewriteCollection)
import Mir.Trans(transCollection, RustModule(..))


import Debug.Trace


-- | Run mir-json on the input, generating lib file on disk 
-- This function uses 'failIO' if any error occurs
generateMIR :: (HasCallStack, ?debug::Int) =>
               FilePath          -- ^ location of input file
            -> String            -- ^ file to processes, without extension
            -> IO Collection
generateMIR dir name  = do
  
  let rustFile = dir </> name <.> "rs"
  let mirFile  = dir </> name <.> "mir"
  
  doesFileExist rustFile >>= \case
    True -> return ()
    False -> fail $ "Cannot read " ++ rustFile 

  rustModTime <- getModificationTime rustFile

  let runMirJSON = do (ec, _, _) <- Proc.readProcessWithExitCode "mir-json"
                                    [rustFile, "--crate-type", "lib"] ""
                      return ec

  ec <- doesFileExist mirFile >>= \case 
    True  -> do mirModTime <- getModificationTime mirFile
                if mirModTime >= rustModTime then
                  return ExitSuccess
                else runMirJSON
    False -> runMirJSON

  case ec of
    ExitFailure cd -> fail $ "Error " ++ show cd ++ " while running mir-json on " ++ dir ++ name
    ExitSuccess    -> return ()

  let rlibFile = ("lib" ++ name) <.> "rlib"
  doesFileExist rlibFile >>= \case
    True  -> removeFile rlibFile
    False -> return ()

  f <- B.readFile (dir </> name <.> "mir")
  let c = (J.eitherDecode f) :: Either String Collection
  case c of
      Left msg -> fail $ "JSON Decoding of MIR failed: " ++ msg
      Right col -> do
        when (?debug > 5) $ do
          traceM "--------------------------------------------------------------"
          traceM $ "Generated module: " ++ name
          traceM $ show (pretty col)
          traceM "--------------------------------------------------------------"  
        return col

-- | Translate MIR to Crucible
translateMIR :: (HasCallStack, ?debug::Int) => Collection -> RustModule
translateMIR col =
  runST $ C.withHandleAllocator $ (transCollection (rewriteCollection col))

    

