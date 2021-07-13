module Crux.ProgressBar where

import System.IO
import System.Console.ANSI
import Control.Monad(zipWithM)

-- | Callback called with index when a goal is started
type ProverMilestoneStartGoal = Integer -> IO ()

-- | Callback called with index when a goal has ended
type ProverMilestoneEndGoal = Integer -> IO ()

-- | Callback called when all goals have ended
type ProverMilestoneFinish = IO ()

-- | Set of three callbacks called by the prover to let loggers indicate
-- progress of the proving process.
type ProverMilestoneCallbacks =
  ( ProverMilestoneStartGoal
  , ProverMilestoneEndGoal
  , ProverMilestoneFinish
  )

silentProverMilestoneCallbacks :: ProverMilestoneCallbacks
silentProverMilestoneCallbacks =
  (const (return ()), const (return ()), return ())

prepStatus :: String -> Int -> IO ProverMilestoneCallbacks
prepStatus pref tot =
   do ansi <- hSupportsANSI stdout
      if ansi then
        return (start,end,finish)
      else
        return silentProverMilestoneCallbacks

  where
  start n = do hSaveCursor stdout
               hPutStr stdout (msg n)
               hFlush stdout
  end _n  = do hRestoreCursor stdout
               hFlush stdout

  finish = do hClearLine stdout
              hFlush stdout

  totS  = show tot
  totW  = length totS
  sh x  = let y = show x
          in replicate (totW - length y) ' ' ++ y

  msg n = pref ++ sh (n::Integer) ++ " / " ++ totS



withProgressBar' :: String -> [a] -> (a -> IO b) -> IO [b]
withProgressBar' pref xs f =
    do (start,end,finish) <- prepStatus pref (length xs)
       let one n a =
            do start n
               b <- f a
               end n
               return b
       zipWithM one [ 1 .. ] xs <* finish

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
