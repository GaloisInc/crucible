module Main where

import Control.Monad
import System.Process

interactIO :: (String -> IO String) -> IO ()
interactIO act = do
  txt <- getContents
  mapM_ (act >=> putStr) (lines txt)

-- TODO: this does no error handling whatsoever
processCommand :: String -> IO String
processCommand line =
  case words line of
    ("$cmd":cmd:args) -> readProcess cmd args ""
    ["$include", "all", file] -> readFile file
    ["$include", range, file] ->
      do txt <- readFile file
         return . unlines . take (endN - startN) $ drop startN (lines txt)
        where
          (start, end') = break (== '-') range
          end = tail end'
          startN = read start - 1
          endN = read end
    _ -> return (line ++ "\n")

main :: IO ()
main = interactIO processCommand
