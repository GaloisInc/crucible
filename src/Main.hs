import System.Console.Haskeline
import SAWScript.Lexer
import SAWScript.Parser
import System.IO
import Control.Monad
import Control.Monad.Trans.Class

echo s = do outputStrLn s; return ()

main :: IO ()
main = do
  putStrLn "SAWScript, Version 2.0.1, :? for help\n"
  putStrLn "\n .oooooo..o       .o.    oooooo   oooooo     oooo "
  putStrLn "d8P'    `Y8      .888.    `888.    `888.     .8'  "
  putStrLn "Y88bo.          .8\"888.    `888.   .8888.   .8'   "
  putStrLn " `\"Y8888o.     .8' `888.    `888  .8'`888. .8'    "
  putStrLn "     `\"Y88b   .88ooo8888.    `888.8'  `888.8'     "
  putStrLn "oo     .d8P  .8'     `888.    `888'    `888'      "
  putStrLn "8\"\"88888P'  o88o     o8888o    `8'      `8'       \n"
  runInputT defaultSettings loop
    where 
      loop :: InputT IO ()
      loop = do
        minput <- getInputLine "> "
        case minput of
          Nothing      -> loop
          Just (":q")  -> do
            echo "Leaving SAWScript"
            return ()
          Just (':':s) -> do
            processDirective s
            loop
          Just str     -> do
            interpret str
            loop

processDirective :: String -> InputT IO ()
processDirective s = case words s of
  ["h"]     -> printHelp
  ["?"]     -> printHelp
  "l":files -> do
    strings <- lift (load files)
    mapM_ interpret strings
  otherwise -> do echo ("Unrecognized directive: ':"++s++"'."); return ()

printHelp :: InputT IO ()
printHelp = do --TODO: Fill in directives as they are developed.
  echo " Commands available from the prompt:\n"
  echo " -- Commands for debugging:\n"
  echo " -- Commands for changing settings:\n"
  echo " -- Commands for displaying information:\n"
  return ()

load :: [FilePath] -> IO [String]
load = 
  (mapM readFile)

interpret :: String -> InputT IO ()
interpret str = do
  let tokens = scan str
  mapM_ (echo . show) tokens
  let ast = parse tokens
  echo . show $ ast