module SAWScript.REPL where

import Control.Monad.IO.Class (liftIO)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.Compiler (runCompiler, ErrT, mapErrT)
import SAWScript.Lexer (scan)
import SAWScript.Parser (parseTopStmt)
import SAWScript.Token (Token)
import SAWScript.Utils (Pos)

run :: IO ()
run = runInputT Haskeline.defaultSettings loop
  where loop :: InputT IO ()
        loop = do
          line <- Haskeline.getInputLine "Prelude> "
          case line of
            Nothing -> return ()
            Just instruction -> runCompiler evaluate instruction $ \r -> do
              Haskeline.outputStrLn $ showResult r
              loop

evaluate :: String -> ErrT (InputT IO) [Token Pos]
evaluate = mapErrT liftIO . scan "<stdin>"

showResult :: [Token Pos] -> String
showResult = show
