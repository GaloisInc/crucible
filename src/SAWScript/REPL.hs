module SAWScript.REPL where

import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (TopStmtSimple, RawT)
import SAWScript.Compiler (Compiler, runCompiler)
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseModule)

run :: IO ()
run = runInputT Haskeline.defaultSettings loop
  where loop :: InputT IO ()
        loop = do
          line <- Haskeline.getInputLine "Prelude> "
          case line of
            Nothing -> return ()
            Just instruction -> do
              runCompiler evaluate instruction (Haskeline.outputStrLn . showResult)
              loop

evaluate :: Compiler String [TopStmtSimple RawT]
evaluate = parseModule . lexSAW "<stdin>"

showResult :: (Show a) => a -> String
showResult = show
