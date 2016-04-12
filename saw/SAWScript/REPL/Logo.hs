{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.REPL.Logo where

import SAWScript.Version (versionText)
import System.Console.ANSI

type Version = String

type Logo = [String]

logo :: Bool -> Logo
logo useColor =
     [ sgr [SetColor Foreground Dull  White] ++ l | l <- ws ]
  ++ [ sgr [SetColor Foreground Vivid Blue ] ++ l | l <- vs ]
  ++ [ sgr [SetColor Foreground Dull  Blue ] ++ l | l <- ds ]
  ++ [ sgr [Reset] ]
  where
  sgr | useColor  = setSGRCode
      | otherwise = const []
  ver = sgr [SetColor Foreground Dull White]
        ++ replicate (lineLen - 20 - length versionText) ' '
        ++ versionText
  ls =
    [ "   ___  __ _ _ _ _"
    , "  / __|/ _\' | | | |"
    , "  \\__ \\ (_| | | | |"
    , "  |___/\\__,_|\\_,_/ " ++ ver
    ]
  lineLen   = length (head ls)
  slen      = length ls `div` 3
  (ws,rest) = splitAt slen ls
  (vs,ds)   = splitAt slen rest

displayLogo :: Bool -> IO ()
displayLogo useColor = mapM_ putStrLn (logo useColor)
