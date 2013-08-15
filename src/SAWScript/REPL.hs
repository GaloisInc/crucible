module SAWScript.REPL where

import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.Compiler (Compiler, runCompiler)
import SAWScript.Lexer (lexSAW)
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

evaluate :: Compiler String [Token Pos]
evaluate = return . lexSAW "stdin"

showResult :: [Token Pos] -> String
showResult = show
