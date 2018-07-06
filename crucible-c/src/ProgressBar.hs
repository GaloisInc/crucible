module ProgressBar where

import System.IO
import System.Console.ANSI
import Control.Monad(zipWithM)

withProgressBar' :: String -> [a] -> (a -> IO b) -> IO [b]
withProgressBar' pref xs f = zipWithM one [ 1 .. ] xs
  where
  tot  = show (length xs)
  totW = length tot
  sh x = let y = show x
         in replicate (totW - length y) ' ' ++ y

  msgLen = length (msg 0)
  clear  = cursorBackward msgLen

  msg n = pref ++ sh (n::Integer) ++ " / " ++ tot

  one n a = do putStr (msg n)
               hFlush stdout
               b <- f a
               clear
               return b


withProgressBar :: Int -> [a] -> (a -> IO b) -> IO [b]
withProgressBar w xs f =
  do prt "|"
     go 0 0 xs []
  where
  prt x = do putStr x
             hFlush stdout

  step = fromIntegral w / fromIntegral (length xs) :: Float
  go shown loc todo done =
    do let new = floor loc - shown
       prt (replicate (floor loc - shown) '=')
       case todo of
         [] -> prt "|\n" >> return (reverse done)
         a : as ->
           do b <- f a
              go (shown + new) (loc + step) as (b : done)


