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
    -- npe during simulation
    "sootRegressionSuite/benchmarks/fixedBug-numericalDiffs"
  , "sootRegressionSuite/benchmarks/fixedBug-aggregation6"
  , "kaffeRegressionSuite/benchmarks/tthrd1"
  , "kaffeRegressionSuite/benchmarks/initTest"
  , "kaffeRegressionSuite/broken/TestNative"
  , "kaffeRegressionSuite/benchmarks/tname"
  , "kaffeRegressionSuite/benchmarks/str2"
  , "kaffeRegressionSuite/benchmarks/str"
  , "ashesEasyTestSuite/benchmarks/factorial"
  , "ashesEasyTestSuite/benchmarks/simple54"
  , "ashesEasyTestSuite/benchmarks/fahrenheit"
  , "jikesPrTestSuite/benchmarks/pr209"
  , "jikesPrTestSuite/benchmarks/pr138"
  , "jikesPrTestSuite/benchmarks/pr199j"
  , "jikesPrTestSuite/benchmarks/pr236b"
  , "jikesPrTestSuite/benchmarks/pr172"
  
    -- field "out" not found (and missing last newline)
  , "jikesDerekTestSuite/benchmarks/testCompare"
  , "jikesDerekTestSuite/benchmarks/testStackAccess"
  , "jikesDerekTestSuite/benchmarks/testVirtualCall"
  , "jikesDerekTestSuite/benchmarks/testSwitch"
  
    -- unexpected variant
  , "sootRegressionSuite/benchmarks/fixedBug-similarSignatures"
    -- wrong answer
  , "jikesHpjTestSuite/benchmarks/bigComp"
  , "jikesHpjTestSuite/benchmarks/multmain"
  , "jikesDerekTestSuite/benchmarks/testConversions"
  , "jikesDerekTestSuite/benchmarks/sort"
  , "jikesDerekTestSuite/benchmarks/testConstants"
  , "jikesPrTestSuite/benchmarks/pr191c"
  , "kaffeRegressionSuite/benchmarks/finaltest"

    -- null is not concrete
  , "jikesDerekTestSuite/benchmarks/testReturn"
  
   -- classcast
  ,  "jikesHpjTestSuite/benchmarks/implement"
  
    -- native method "longBitsToDouble"
  , "kaffeRegressionSuite/benchmarks/doubleComp"

    -- native methods - initIDs
  , "jikesHpjTestSuite/benchmarks/recur"
    -- -- native method gc
  , "kaffeRegressionSuite/benchmarks/intfTest"
  , "kaffeRegressionSuite/benchmarks/testClassRef"

    -- illegal index
  , "kaffeRegressionSuite/benchmarks/moduloTest"
  , "kaffeRegressionSuite/benchmarks/testIntLong"

    -- fNeg
  , "jikesDerekTestSuite/benchmarks/testArithmetic"

    -- saveLocals: Generator.hs:197
  , "ashesHardTestSuite/broken/nucleic"
   
    -- generateInstruction: jsr/ret not supported
  , "sootRegressionSuite/benchmarks/fixedBug-jsr"
  , "jikesHpjTestSuite/benchmarks/try2"
  , "jikesHpjTestSuite/benchmarks/try1"
  , "jikesHpjTestSuite/benchmarks/try3"
  , "jikesDerekTestSuite/benchmarks/testFinally"
  , "kaffeRegressionSuite/benchmarks/nullPointerTest"
  , "jikesPrTestSuite/benchmarks/pr146"
  
    -- unimplemented: multianewarray
  , "jikesHpjTestSuite/benchmarks/checkcast7"
  , "jikesHpjTestSuite/benchmarks/array4"
  , "jikesHpjTestSuite/benchmarks/instance"
  , "ashesEasyTestSuite/benchmarks/life"
  
    -- unimplemented: CheckCast for array
  , "jikesHpjTestSuite/benchmarks/checkcast1"
  
    -- unimplemented: instanceof for array
  , "jikesHpjTestSuite/benchmarks/instance1"
  , "jikesDerekTestSuite/benchmarks/testInstanceOf"
  
    -- java.io.FileOutputStream
  , "jikesHpjTestSuite/benchmarks/multarg"
  
    -- Strange parsing issue: trying to load native code
    -- needs more than we are currently providing
  , "kaffeRegressionSuite/benchmarks/testFloatDouble"
  , "kaffeRegressionSuite/benchmarks/doubleBug"
  , "ashesHardTestSuite/benchmarks/decode"
  , "ashesHardTestSuite/benchmarks/lu"
  , "ashesHardTestSuite/benchmarks/probe"
  , "ashesHardTestSuite/benchmarks/fft"
  , "kaffeRegressionSuite/benchmarks/badFloatTest"
  , "jikesPrTestSuite/benchmarks/pr196"
  
    -- needs java.lang.Class
  , "kaffeRegressionSuite/benchmarks/schtum"
  , "kaffeRegressionSuite/benchmarks/illegalInterface"
  , "kaffeRegressionSuite/benchmarks/methodBug"
  
    -- or sun.reflect.Reflection
  , "kaffeRegressionSuite/benchmarks/getInterfaces"
  , "kaffeRegressionSuite/broken/invTarExcTest"
  , "kaffeRegressionSuite/broken/testSerializable"
  , "kaffeRegressionSuite/benchmarks/forNameTest"
  , "kaffeRegressionSuite/benchmarks/reflectInvoke"
  , "kaffeRegressionSuite/benchmarks/reflectInterfaces"
  , "kaffeRegressionSuite/broken/constructorTest"
  , "jikesPrTestSuite/benchmarks/pr226"
    
    -- or java.lang.reflect.Array
  , "kaffeRegressionSuite/benchmarks/reflectMultiArray"
  
    -- java beans
  , "kaffeRegressionSuite/broken/beanBug"
  , "kaffeRegressionSuite/broken/bean"
    
    -- data structures 
  , "kaffeRegressionSuite/benchmarks/hashtableTest1"
  , "kaffeRegressionSuite/benchmarks/exceptionTest"
              
    --- BELOW this line are tests that were not  ----
    --- supported by the previous version of jss ----
              
               -- Floating point array tests
              ,  "ashesHardTestSuite/benchmarks/matrix"
              , "jikesDerekTestSuite/benchmarks/testArrayAccess"
              , "jikesHpjTestSuite/benchmarks/arraymethod"
              , "jikesHpjTestSuite/benchmarks/callmm"
              , "jikesHpjTestSuite/benchmarks/float1"
              , "kaffeRegressionSuite/benchmarks/doublePrint"
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
              , "jikesPrTestSuite/benchmarks/pr128"
              , "jikesPrTestSuite/benchmarks/pr189"
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
              , "sootRegressionSuite/benchmarks/smbAccessTest"
              , "sootRegressionSuite/benchmarks/syncTest"
              ]

data TestResult
  = Skipped
  | ExpectedFailure
  | Passed
  | Failed
  deriving (Eq, Show)

runTest :: String -> IO TestResult
runTest file = do
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
                                      [ "-c", "classes" -- "-c", jdkPath ++ ":classes"
--                                      , "-j", jdkPath 
--                                               ++ ":" ++
--                                               (topDir </> "support" </> "galois.jar")
                                      , className
                                      ]
                                      ""
      let success = outText == expectedOutput && exitCode == ExitSuccess
      res <- if success
        then do
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
main = do
  dir <- getCurrentDirectory
  results <- mapM runTest =<< runFind dir "mainClass"
  putStrLn "========"
  printf "Total tests: %d\n" . length $ results
  printf "Passed %d\n" . length . filter (== Passed) $ results
  printf "Skipped %d\n" . length . filter (== Skipped) $ results
  printf "Saw %d expected failures\n" . length . filter (== ExpectedFailure) $
    results
  printf "Saw %d unexpected failures\n" . length . filter (== Failed) $
    results

wip :: IO ()
wip = do
  let top = "ashesSuiteCollection/suites/"
  -- class cast bug
  result <- runTest $ top ++ "jikesHpjTestSuite/benchmarks/implement/mainClass"
  
  _ <- runTest $ top ++ "ashesEasyTestSuite/benchmarks/simple54/mainClass"
  putStrLn (show result)
