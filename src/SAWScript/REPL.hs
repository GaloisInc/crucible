module SAWScript.REPL where

import Control.Monad.Trans.Class (lift)
import Control.Monad.IO.Class (liftIO)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (TopStmtSimple, RawT)
import SAWScript.Compiler (runCompiler, ErrT, mapErrT)
import SAWScript.Import (loadModuleFromString, preludeLoadedModules)
import SAWScript.Options (Options)

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
    \mods -> do
      {- TODO: Actually do something useful here instead of just printing the
      modules -}
      lift $ Haskeline.outputStrLn $ showResult mods

showResult :: (Show a) => a -> String
showResult = show
