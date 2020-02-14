module Crux.ProgressBar where

import System.IO
import System.Console.ANSI
import Control.Monad(zipWithM)

import Control.Concurrent


prepStatus :: String -> Int -> (Integer -> IO (), IO (), IO ())
prepStatus pref tot = (start,end,finish)
  where
  start n = do putStr (msg n)
               hFlush stdout
  end     = do threadDelay 100000
               cursorBackward msgLen
               hFlush stdout

  finish = do cursorBackward msgLen
              putStrLn ""
              hFlush stdout

  totS  = show tot
  totW  = length totS
  sh x  = let y = show x
          in replicate (totW - length y) ' ' ++ y

  msgLen = length (msg 0)

  msg n = pref ++ sh (n::Integer) ++ " / " ++ totS



withProgressBar' :: String -> [a] -> (a -> IO b) -> IO [b]
withProgressBar' pref xs f = zipWithM one [ 1 .. ] xs <* finish
  where
  (start,end,finish) = prepStatus pref (length xs)

  one n a = do start n
               b <- f a
               end
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


