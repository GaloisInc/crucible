-- from crucible-c/src/Log.hs
module Log where

import System.Console.ANSI

sayOK :: String -> String -> IO ()
sayOK = sayCol Green

sayFail :: String -> String -> IO ()
sayFail = sayCol Red

say :: String -> String -> IO ()
say x y = putStrLn ("[" ++ x ++ "] " ++ y)

sayCol :: Color -> String -> String -> IO ()
sayCol col x y =
  do putStr "["
     printCol col x
     putStrLn ("] " ++ y)



printCol :: Color -> String -> IO ()
printCol c x =
  do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
     putStr x
     setSGR [Reset]
