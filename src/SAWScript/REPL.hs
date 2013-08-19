module SAWScript.REPL where

import Control.Monad ((>=>))
import Control.Monad.Trans.Class (lift)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (foldrM)
import qualified Data.Map as Map
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (moduleNameFromString)
import SAWScript.BuildModules (buildModules)
import SAWScript.Compiler (runCompiler, ErrT, mapErrT)
import SAWScript.Import (loadModuleFromString, preludeLoadedModules)
import SAWScript.Interpreter (interpretMain)
import SAWScript.Options (Options)

-- TODO: Get rid of all this!
import Control.Applicative
import Control.Monad
import qualified Data.Map      as M
import qualified Data.Foldable as F
import qualified Data.Set      as S
import Data.List
import System.IO
import System.Console.GetOpt
import System.Environment
import System.FilePath
import SAWScript.AST
import SAWScript.BuildModules as BM
import SAWScript.Compiler
import SAWScript.Import
import SAWScript.Interpreter
import SAWScript.MGU (checkModule)
import SAWScript.Options
import SAWScript.RenameRefs as RR
import SAWScript.ResolveSyns

run :: Options -> IO ()
run options = runInputT Haskeline.defaultSettings loop
  where loop :: InputT IO ()
        loop = do
          line <- Haskeline.getInputLine "Prelude> "
          case line of
            Nothing -> return ()
            Just instruction -> do
              runCompiler (evaluateAndPrint options) instruction
                (const $ return ())
              loop

evaluateAndPrint :: Options -> String -> ErrT (InputT IO) ()
evaluateAndPrint options s = do
  preexistingModules <- liftIO preludeLoadedModules
  loadModuleFromString options "<stdin>" s preexistingModules $
    mapErrT liftIO . buildModules >=>
    mapErrT liftIO . foldrM checkModuleWithDeps Map.empty >=>
    liftIO . interpretMain options . Map.findWithDefault (error "wtf") (moduleNameFromString "<stdin>") >=>
    lift . Haskeline.outputStrLn . showResult

showResult :: (Show a) => a -> String
showResult = show

-- TODO: This is duplicate code from 'Main'.  Factor it out.
checkModuleWithDeps :: BM.ModuleParts (ExprSimple RawT)
  -> M.Map ModuleName ValidModule
  -> Err (M.Map ModuleName ValidModule)
checkModuleWithDeps (BM.ModuleParts mn ee pe te ds) cms =
  mod >>=
  resolveSyns >>=
  renameRefs  >>=
  checkModule >>= \cm -> return $ M.insert mn cm cms
  where
  deps :: Err (M.Map ModuleName ValidModule)
  deps = fmap M.fromList $ forM (S.toList ds) $ \n ->
           case M.lookup n cms of
             Nothing -> fail $ "Tried to compile module " ++ show mn ++
                               " before compiling its dependency, " ++ show n
             Just m  -> return (n,m)
  mod  = Module mn ee pe te <$> deps

