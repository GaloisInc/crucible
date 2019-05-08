#!/usr/bin/env runhaskell

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{- |
Module           : Main
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : atomb
-}
module Main where

import Control.Monad
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Text.Printf

type Verbosity = Int

up :: FilePath -> FilePath
up = takeDirectory

skipList, expFailList :: [String]
skipList    = [  -- SCW: yep slow
                 "ashesJSuite/benchmarks/symjpack-t"
              ,  "jikesDerekTestSuite/benchmarks/testFieldAccess"
              ,  "ashesHardTestSuite/benchmarks/matrix"

                 -- The following are very slow
              ,  "ashesHardTestSuite/benchmarks/illness"
              , "ashesHardTestSuite/benchmarks/boyer"
              
                 -- The following require command-line arguments and
                 -- read files.
              , "ashesHardTestSuite/benchmarks/machineSim"
              , "ashesJSuite/benchmarks/jpat-p"
              ]
expFailList = [

     -- wrong string produced (!)
--     "kaffeRegressionSuite/benchmarks/str"
    
     -- some numerical results are wrong!
      "ashesEasyTestSuite/benchmarks/fahrenheit"

    -- needs too much from java.io library
    -- FileOutputStream argument
   , "jikesHpjTestSuite/benchmarks/recur"
         
  -- tests length of args during simulation (npe)
    , "kaffeRegressionSuite/benchmarks/initTest"
  -- needs args (commandline argument)
  , "jikesDerekTestSuite/benchmarks/sort"

    -- wrong answer
    -- String constants should all share the same
    -- object at runtime instead of allocating new
    -- objects.
  , "jikesHpjTestSuite/benchmarks/multarg"

    -- fRem doesn't round (but dRem does)
    -- check what the Crucible version of this operation
    -- should do
    -- UPDATE: I think the problem is the display,
    -- not the calculation. The output is printed
    -- without rounding, but the answers are different
  , "jikesDerekTestSuite/benchmarks/testArithmetic"

    -- needs java/lang/StrictMath.sqrt
    , "sootRegressionSuite/benchmarks/fixedBug-numericalDiffs"

    -- needs: Double.doubleToRawLongBits
  , "kaffeRegressionSuite/benchmarks/doublePrint"

    -- needs sun/misc/FloatingDecimal$ExceptionalBinaryToASCIIBuffer
  , "kaffeRegressionSuite/benchmarks/doubleComp"


    -- saveLocals: somehow there are two more registers
    -- than values when 'saveLocals' is called.
    -- I don't know how to debug this.
  , "ashesHardTestSuite/broken/nucleic"

    -- generateInstruction: jsr/ret not supported
  , "sootRegressionSuite/benchmarks/fixedBug-jsr"
  , "jikesHpjTestSuite/benchmarks/try2"
  , "jikesHpjTestSuite/benchmarks/try1"
  , "jikesHpjTestSuite/benchmarks/try3"
  , "jikesDerekTestSuite/benchmarks/testFinally"
  , "kaffeRegressionSuite/benchmarks/nullPointerTest"
  , "jikesPrTestSuite/benchmarks/pr146"

    -- Strange parsing issue: trying to load native code
    -- needs more than we are currently providing
  , "kaffeRegressionSuite/benchmarks/testFloatDouble"
  , "kaffeRegressionSuite/benchmarks/doubleBug"
  , "ashesHardTestSuite/benchmarks/decode"
  , "ashesHardTestSuite/benchmarks/lu"
  , "ashesHardTestSuite/benchmarks/probe"
  , "ashesHardTestSuite/benchmarks/fft"
  , "kaffeRegressionSuite/benchmarks/badFloatTest"

  -- needs java.lang.Thread
  , "kaffeRegressionSuite/benchmarks/tname"
  , "kaffeRegressionSuite/benchmarks/tthrd1"    
  
    -- needs java.lang.Class
  , "kaffeRegressionSuite/benchmarks/schtum"
  , "kaffeRegressionSuite/benchmarks/illegalInterface"
  , "kaffeRegressionSuite/benchmarks/methodBug"
    -- more reflection: Integer.TYPE
  , "kaffeRegressionSuite/benchmarks/testClassRef"

    -- needs sun.reflect.Reflection
  , "kaffeRegressionSuite/benchmarks/getInterfaces"
  , "kaffeRegressionSuite/broken/invTarExcTest"
  , "kaffeRegressionSuite/broken/testSerializable"
  , "kaffeRegressionSuite/benchmarks/forNameTest"
  , "kaffeRegressionSuite/benchmarks/reflectInvoke"
  , "kaffeRegressionSuite/benchmarks/reflectInterfaces"
  , "kaffeRegressionSuite/broken/constructorTest"
  , "jikesPrTestSuite/benchmarks/pr226"

    -- needs java.lang.reflect.Array
  , "kaffeRegressionSuite/benchmarks/reflectMultiArray"

    -- java beans
  , "kaffeRegressionSuite/broken/beanBug"
  , "kaffeRegressionSuite/broken/bean"

    -- data structures
  , "kaffeRegressionSuite/benchmarks/hashtableTest1"
  , "kaffeRegressionSuite/benchmarks/exceptionTest"

    -- native method
   , "kaffeRegressionSuite/broken/TestNative"

    
    --- BELOW this line are tests that were not  ----
    --- supported by the previous version of jss ----

               -- Floating point array tests
              ,  "ashesHardTestSuite/benchmarks/matrix"  -- SLOW
              , "jikesDerekTestSuite/benchmarks/testArrayAccess" -- uses array[0].getClass().getName()
              , "jikesHpjTestSuite/benchmarks/arraymethod" -- strange fp behavior
--              , "jikesHpjTestSuite/benchmarks/callmm"  (FIXED!)

                -- Trivially different output
              , "jikesHpjTestSuite/broken/array2"
              , "jikesHpjTestSuite/broken/array3"
              , "jikesHpjTestSuite/broken/array5"
              , "jikesHpjTestSuite/broken/checkcast2"
              , "jikesHpjTestSuite/broken/dgram1"
              , "jikesHpjTestSuite/broken/dgramTest"
              , "kaffeRegressionSuite/broken/StackDump"
                -- Concurrency tests
              , "kaffeRegressionSuite/broken/threadInterrupt"
              , "kaffeRegressionSuite/broken/threadStop"
                -- Reflection tests
              , "ashesHardTestSuite/benchmarks/puzzle"
              , "jikesHpjTestSuite/benchmarks/checkarray"
              , "jikesHpjTestSuite/benchmarks/classname"
              , "jikesHpjTestSuite/benchmarks/fisTest"
              , "jikesHpjTestSuite/benchmarks/fosTest"
              , "jikesHpjTestSuite/benchmarks/fTest"
              , "jikesHpjTestSuite/benchmarks/rafTest"
              , "jikesHpjTestSuite/benchmarks/syncm1"
              , "jikesPrTestSuite/broken/pr165"
              , "kaffeRegressionSuite/broken/execTest"
              , "kaffeRegressionSuite/broken/fileTest"
              , "kaffeRegressionSuite/broken/processClassInst"
              , "kaffeRegressionSuite/broken/processClassStop"
              , "kaffeRegressionSuite/broken/processClassTest"
              , "kaffeRegressionSuite/broken/reflect"
                -- Tests requiring exception handling
              , "ashesEasyTestSuite/benchmarks/simple21"
              , "ashesEasyTestSuite/benchmarks/simple41"
              , "ashesEasyTestSuite/benchmarks/simple53"
              , "ashesEasyTestSuite/benchmarks/simple57"
              , "jikesHpjTestSuite/benchmarks/checkcast6"
              , "jikesHpjTestSuite/benchmarks/checkcastjp"
              , "jikesHpjTestSuite/benchmarks/lptry1"
              , "jikesHpjTestSuite/benchmarks/lptry2"
              , "jikesHpjTestSuite/benchmarks/trychk1"
              , "jikesHpjTestSuite/benchmarks/trychk2"
              , "jikesHpjTestSuite/benchmarks/trychk3"
              , "jikesHpjTestSuite/benchmarks/trychk6"
              , "jikesHpjTestSuite/benchmarks/trychk7"
              , "jikesHpjTestSuite/benchmarks/trychk8"
              , "jikesHpjTestSuite/broken/tryexcept"
              , "jikesPrTestSuite/benchmarks/pr257"
              , "jikesPrTestSuite/benchmarks/pr287"
              , "kaffeRegressionSuite/benchmarks/lostFrame"
              , "kaffeRegressionSuite/broken/indexTest"
              , "sootRegressionSuite/benchmarks/fixedBug-aggregation4"
              , "sootRegressionSuite/benchmarks/fixedBug-deadCodeElimination"
              , "sootRegressionSuite/benchmarks/fixedBug-deadCodeElimination2"
              , "sootRegressionSuite/benchmarks/ifNullTest"
              , "sootRegressionSuite/benchmarks/movingThrow"
              , "sootRegressionSuite/benchmarks/outstandingBug-aggregation7"
                -- Tests requiring special classes
              , "ashesHardTestSuite/benchmarks/lexgen"
              , "ashesJSuite/benchmarks/rhino-a"
              , "jikesHpjTestSuite/benchmarks/dTest"
              , "jikesHpjTestSuite/broken/clientsock"
              , "jikesHpjTestSuite/broken/serversock"
              , "kaffeRegressionSuite/benchmarks/burford"
              , "kaffeRegressionSuite/benchmarks/deadThread"
              , "kaffeRegressionSuite/benchmarks/exceptionInInitializerTest"
              , "kaffeRegressionSuite/benchmarks/findSystemClass"
              , "kaffeRegressionSuite/benchmarks/kaffeVerifyBug"
              , "kaffeRegressionSuite/benchmarks/markResetTest"
              , "kaffeRegressionSuite/benchmarks/overflow"
              , "kaffeRegressionSuite/benchmarks/processClassLockTest"
              , "kaffeRegressionSuite/benchmarks/soTimeout"
              , "kaffeRegressionSuite/benchmarks/testUnlock"
              , "kaffeRegressionSuite/benchmarks/ttest"
              , "kaffeRegressionSuite/benchmarks/udpTest"
              , "kaffeRegressionSuite/benchmarks/uncaughtException"
              , "kaffeRegressionSuite/benchmarks/wc"
              , "kaffeRegressionSuite/broken/alias"
              , "kaffeRegressionSuite/broken/catchDeath"
              , "kaffeRegressionSuite/broken/clTest"
              , "kaffeRegressionSuite/broken/gcTest"
              , "sootRegressionSuite/benchmarks/syncTest"
              ]

data TestResult
  = Skipped
  | ExpectedFailure
  | Passed
  | SurprisePass
  | Failed
  deriving (Eq, Show)

runTest :: Verbosity -> String -> IO TestResult
runTest verbosity file = do
  curDir <- getCurrentDirectory
  (className:_) <- words `liftM` readFile file
  let dirName   = takeDirectory file
      dirParts  = splitPath dirName

      lastParts = drop (length dirParts - 3) dirParts
      testId    = joinPath lastParts
      topDir = up (up curDir)
      jdkPath = "/Library/Java/JavaVirtualMachines/jdk1.8.0_171.jdk/Contents/Home/jre/lib/rt.jar"
 --     jdkPath = topDir </> "jdk1.6"
      --jssPath = topDir </> "dist" </> "build" </> "jss" </> "jss"
      jssPath = curDir </> "runcrucible.sh"
      goldFile = dirName </> "correctOutput"
  goldExists <- doesFileExist goldFile
  case () of
    () | testId `elem` skipList -> return Skipped
    () | goldExists -> do
      expectedOutput <- readFile goldFile
      setCurrentDirectory dirName
      printf "%-58s" testId
      hFlush stdout
      (exitCode, outText, errText) <- readProcessWithExitCode
                                      jssPath
                                      [ "-c", "classes"
--                                      , "-j", jdkPath
--                                               ++ ":" ++
--                                               (topDir </> "support" </> "galois.jar")
                                      , "-d", show verbosity
                                      , className ++ ".java"
                                      ]
                                      ""
      let success = outText == expectedOutput && exitCode == ExitSuccess
      res <- if success
        then if testId `elem` expFailList
            then do
               printf "  Surprise Pass (%5d)\n" (length outText)
               return SurprisePass
             else  do
               printf "  Pass (%5d)\n" (length outText)
               return Passed
        else if testId `elem` expFailList
          then do
            printf "%14s\n" "Expect Fail"
            return ExpectedFailure
          else do
            printf "%14s\n" "Unexpect Fail"
            putStrLn "Expected:"
            putStr expectedOutput
            putStrLn "Got:"
            putStr outText
            putStr errText
            putStrLn $ "Exit code = " ++ show exitCode
            return Failed
      setCurrentDirectory curDir
      return res
    () | otherwise -> return Skipped

runFind :: String -> String -> IO [String]
runFind dir name = lines `liftM` readProcess "find" [dir, "-name", name] ""



main :: IO ()
main = wip


{-  
main = do
  dir <- getCurrentDirectory
  results <- mapM (runTest 1) =<< runFind dir "mainClass"
  putStrLn "========"
  printf "Total tests: %d\n" . length $ results
  printf "Passed %d\n" . length . filter (== Passed) $ results
  printf "Skipped %d\n" . length . filter (== Skipped) $ results
  printf "Saw %d expected failures\n" . length . filter (== ExpectedFailure) $
    results
  printf "Saw %d unexpected failures\n" . length . filter (== Failed) $
    results
  printf "Saw %d unexpected passes\n" . length . filter (== SurprisePass) $
    results
-}

wip :: IO ()
wip = do
  let top = "ashesSuiteCollection/suites/"
  
  let testCase = "kaffeRegressionSuite/benchmarks/str"

  result <- runTest 2 $ top ++ testCase ++ "/mainClass"

  print result


