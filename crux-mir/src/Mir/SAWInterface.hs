{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

module Mir.SAWInterface (RustModule, loadMIR, extractMIR, rmCFGs, translateMIR) where

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
import           Mir.Generate



-----------------------------------------------------------------------
-- NOTE: need to call the static initializer for the RustModule at some point
-- this allocates and initializes global variables

decorateFnName :: String -> String
decorateFnName t = "::" ++ t ++ "[0]"

extractMIR :: AIG.IsAIG l g =>
     AIG.Proxy l g -> SC.SharedContext -> RustModule -> String -> IO SC.Term
extractMIR proxy sc rm n = do
    let cfgmap = rmCFGs rm
        link = forM_ cfgmap (\(C.AnyCFG cfg) -> C.bindFnHandle (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg))
    (C.AnyCFG cfg) <- case (M.lookup (T.pack (decorateFnName n)) cfgmap) of
             Just c -> return c
             _ -> fail $ "Could not find cfg: " ++ n
             
    --print $ "CFG for " ++ n         
    --print $ C.ppCFG True cfg
    
    term <- extractFromCFGPure link proxy sc cfg

    --print $ "SAW core for " ++ n
    --print $ SC.showTerm term
    
    return term


loadMIR :: HasCallStack => SC.SharedContext -> FilePath -> IO RustModule
loadMIR _sc fp = do
    let ?debug = 0
    f <- B.readFile fp
    let c = (J.eitherDecode f) :: Either String Collection
    case c of
      Left msg -> fail $ "Decoding of MIR failed: " ++ msg
      Right col -> return $ translateMIR col 
      
