module SAWScript.REPL where

import Control.Monad ((=<<))
import Control.Monad.IO.Class (liftIO)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (BlockStmt, UnresolvedName, RawT)
import SAWScript.Compiler (runCompiler, ErrT, mapErrT)
import SAWScript.Lexer (scan)
import SAWScript.Parser (parseBlockStmt)

run :: IO ()
run = runInputT Haskeline.defaultSettings loop
  where loop :: InputT IO ()
        loop = do
          line <- Haskeline.getInputLine "Prelude> "
          case line of
            Nothing -> return ()
            Just instruction -> do
              runCompiler evaluate instruction $ \r -> do
                Haskeline.outputStrLn $ showResult r
              loop

evaluate :: String -> ErrT (InputT IO) (BlockStmt UnresolvedName RawT)
evaluate line = do
  tokens <- mapErrT liftIO $ scan "<stdin>" line
  statement <- mapErrT liftIO $ parseBlockStmt tokens
  return statement

showResult :: Show a => a -> String
showResult = show
