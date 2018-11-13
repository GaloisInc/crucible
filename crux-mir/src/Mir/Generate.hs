{-# LANGUAGE LambdaCase #-}


module Mir.Generate(generateMIR) where

import qualified Data.Aeson as J
import qualified Data.ByteString.Lazy as B
import System.FilePath
import qualified System.Process as Proc
import           System.Exit (ExitCode(..))
import           System.Directory (doesFileExist, removeFile, getModificationTime)

import GHC.Stack
import Mir.Mir
import Mir.PP()
import Text.PrettyPrint.ANSI.Leijen (Pretty(..))


import Debug.Trace


-- | Run mir-json on the input, generating lib file on disk 
-- This function uses 'failIO' if any error occurs
generateMIR :: HasCallStack =>
               FilePath          -- ^ location of input file
            -> String            -- ^ file to processes, without extension
            -> IO Collection
generateMIR dir name = do
  
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
    ExitFailure cd -> fail $ "Error while running mir-json: " ++ show cd
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
        traceM "--------------------------------------------------------------"
        traceM $ "Collection: " ++ name
        traceM $ show (pretty col)
        traceM "--------------------------------------------------------------"
        return col
