module ProgressBar where

import System.IO

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


