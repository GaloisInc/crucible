module SAWScript.CryptolBuiltins where

import Control.Applicative
import Control.Monad.State

import qualified Verifier.SAW.Cryptol as C
import Verifier.SAW
import Verifier.SAW.Prelude

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP

import qualified Data.Map as Map

import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verinf.Symbolic as BE

import SAWScript.Proof
import SAWScript.Builtins (withBE)

extractCryptol :: SharedContext s -> FilePath -> String -> IO (SharedTerm s)
extractCryptol sc filepath name = do
  (result, warnings) <- M.loadModuleByPath filepath
  mapM_ (print . pp) warnings
  (m, modEnv) <-
    case result of
      Left err -> fail (show err)
      Right x -> return x
  let declGroups = concatMap mDecls (M.loadedModules modEnv)
  env <- C.importDeclGroups sc C.emptyEnv declGroups
  let env' = C.envE env
  let qname = QName (Just (mName m)) (Name name)
  case Map.lookup qname env' of
    Nothing -> fail "Name not found in this module"
    Just t -> return t


-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC. (Currently ignores satisfying assignments.)
satABC' :: SharedContext s -> ProofScript s ProofResult
satABC' sc = StateT $ \t -> withBE $ \be -> do
  case BE.beCheckSat be of
    Nothing -> fail "Backend does not support SAT checking."
    Just chk -> do
      lit <- BBSim.bitBlast be sc t
      satRes <- chk lit
      case satRes of
        BE.UnSat -> do putStrLn "UNSAT"
                       (,) () <$> scApplyPreludeFalse sc
        BE.Sat _ -> do putStrLn "SAT"
                       (,) () <$> scApplyPreludeTrue sc
        _ -> fail "ABC returned Unknown for SAT query."
