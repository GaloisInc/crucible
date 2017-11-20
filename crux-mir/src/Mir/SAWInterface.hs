module Mir.SAWInterface (RustModule, loadMIR, extractMIR, rmCFGs) where

import Mir.Run
import Mir.Mir
import Mir.Pass as P
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
import qualified Lang.Crucible.Config as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Solver.Interface as C hiding (mkStruct)
import qualified Lang.Crucible.Solver.SAWCoreBackend as C
import qualified Lang.Crucible.Solver.SimpleBuilder as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Text.Regex as Regex

import Control.Monad

data RustModule = RustModule {
    rmCFGs :: M.Map T.Text C.AnyCFG
}

cleanFnName :: T.Text -> T.Text
cleanFnName t = T.pack $
    let r1 = Regex.mkRegex "\\[[0-9]+\\]"
        r2 = Regex.mkRegex "::"
        s1 = Regex.subRegex r1 (T.unpack t) ""
        s2 = Regex.subRegex r2 s1 "" in
    s2

extractMIR :: SC.SharedContext -> RustModule -> String -> IO SC.Term
extractMIR sc rm n = do
    let cfgmap = rmCFGs rm
        link = forM_ cfgmap (\(C.AnyCFG cfg) -> C.bindFnHandle (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg))
    (C.AnyCFG cfg) <- case (M.lookup (T.pack n) cfgmap) of
             Just c -> return c
             _ -> fail $ "Could not find cfg: " ++ n
    term <- extractFromCFGPure link sc cfg
    return term

loadMIR :: SC.SharedContext -> FilePath -> IO RustModule
loadMIR sc fp = do
    f <- B.readFile fp
    let c = (J.eitherDecode f) :: Either String Collection
    case c of
      Left msg -> fail $ "Decoding of MIR failed: " ++ msg
      Right coll -> do
          let cfgmap_ = mirToCFG (functions coll) (Just (P.passMutRefArgs . P.passRemoveStorage . P.passRemoveBoxNullary))
          let cfgmap = M.fromList $ map (\(k,v) -> (cleanFnName k, v)) $ M.toList cfgmap_
          return $ RustModule cfgmap
