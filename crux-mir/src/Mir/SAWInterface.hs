{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Mir.SAWInterface (RustModule, extractMIR, generateMIR, rmCFGs, translateMIR) where

import Mir.Run
import Mir.Intrinsics
import Mir.Mir
import Mir.Pass as P
import Mir.Pass.CollapseRefs as P
import Mir.Pass.RewriteMutRef as P
import Mir.Pass.RemoveStorage as P
import Mir.Pass.RemoveBoxNullary as P
import System.IO
import System.FilePath
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedAST as SC
import qualified Data.Aeson as J
import qualified Data.ByteString.Lazy as B
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedAST as SC
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified What4.Interface as C hiding (mkStruct)
import qualified Lang.Crucible.Backend.SAWCore as C
import qualified Text.Regex as Regex
import qualified Data.AIG.Interface as AIG



import Control.Monad

import GHC.Stack

import           Mir.PP()
import           Text.PrettyPrint.ANSI.Leijen (putDoc,Pretty(..))
import qualified System.Process as Proc
import           System.Exit (ExitCode(..),exitWith)
import           System.Directory (listDirectory, doesFileExist, removeFile)



-----------------------------------------------------------------------

data RustModule = RustModule {
    rmCFGs :: M.Map T.Text (C.AnyCFG MIR)
}

cleanFnName :: T.Text -> T.Text
cleanFnName t = T.pack $
    let r1 = Regex.mkRegex "\\[[0-9]+\\]"
        r2 = Regex.mkRegex "::"
        s1 = Regex.subRegex r1 (T.unpack t) ""
        s2 = Regex.subRegex r2 s1 "" in
    s2

extractMIR :: AIG.IsAIG l g =>
     AIG.Proxy l g -> SC.SharedContext -> RustModule -> String -> IO SC.Term
extractMIR proxy sc rm n = do
    let cfgmap = rmCFGs rm
        link = forM_ cfgmap (\(C.AnyCFG cfg) -> C.bindFnHandle (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg))
    (C.AnyCFG cfg) <- case (M.lookup (T.pack n) cfgmap) of
             Just c -> return c
             _ -> fail $ "Could not find cfg: " ++ n
             
    --print $ "CFG for " ++ n         
    --print $ C.ppCFG True cfg
    
    term <- extractFromCFGPure link proxy sc cfg

    --print $ "SAW core for " ++ n
    --print $ SC.showTerm term
    
    return term


-- | Translate MIR to Crucible
translateMIR :: Collection -> RustModule
translateMIR col = RustModule cfgmap where
  passes  = P.passRemoveBoxNullary
  cfgmap_ = mirToCFG col (Just passes)
  cfgmap  = M.fromList $ map (\(k,v) -> (cleanFnName k, v)) $ M.toList cfgmap_
  

-- | Run mir-json on the input, generating lib file on disk 
-- This function uses 'failIO' if any error occurs
generateMIR :: HasCallStack =>
               FilePath          -- ^ location of input file
            -> String            -- ^ file to processes, without extension
            -> IO Collection
generateMIR dir name = do
  
  let rustFile = dir </> name <.> "rs"
  
  doesFileExist rustFile >>= \case
    True -> return ()
    False -> fail $ "Cannot read " ++ rustFile 

  (ec, _, _) <- Proc.readProcessWithExitCode "mir-json"
    [rustFile, "--crate-type", "lib"] ""

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
      Right col -> return col
      

