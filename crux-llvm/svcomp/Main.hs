{- | This is the SVCOMP utility for crux-llvm.  It is designed to run
   the inputs for the "Competition on Software Verification" (SV-COMP)
   and produce benchmark data for that run.
-}

{-# Language DeriveGeneric #-}
{-# Language ImplicitParams #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main (main) where

import Control.Concurrent.Async( async, wait )
import Control.Exception
  (bracket, catch, throwIO, SomeException, fromException, AsyncException, displayException, try )

import Data.Aeson ( encode, ToJSON(..), FromJSON, ToJSONKey, eitherDecode', object )
import Data.Bits( bit )
import qualified Data.ByteString.Lazy as LBS
import GHC.Generics (Generic)
import Data.List
  ( isSuffixOf )
import qualified Data.Map as Map
import Data.Time.Clock
  ( getCurrentTime, diffUTCTime, NominalDiffTime )
import System.Exit
  ( ExitCode(..), exitSuccess, exitFailure )
import System.FilePath ( takeFileName, takeDirectory, (</>), (-<.>) )
import System.Directory ( copyFile, createDirectoryIfMissing, removeDirectoryRecursive )
import System.IO
  ( Handle, hGetContents, hClose, openFile, IOMode(..), hFlush )

-- unix
import System.Posix.IO
import System.Posix.Process
import System.Posix.Resource

-- crux
import qualified Crux
import Crux.Config.Common(CruxOptions(..))
import Crux.Log
import Crux.Report
import Crux.SVCOMP
import Crux.Types as Crux

-- local
import Crux.LLVM.Config
import Crux.LLVM.Compile
import Crux.LLVM.Simulate
import CruxLLVMMain( processLLVMOptions )

main :: IO ()
main = do
  cfg <- llvmCruxConfig
  let opts = Crux.cfgJoin cfg svcompOptions
  Crux.loadOptions defaultOutputConfig "crux-llvm-svcomp" "0.1" opts $ \(co0,(lo0,svOpts)) ->
    do (cruxOpts, llvmOpts) <- processLLVMOptions (co0{ outDir = "results" </> "SVCOMP" },lo0)
       bss <- loadSVCOMPBenchmarks cruxOpts
       let taskMap = deduplicateTasks bss
       ts <- genSVCOMPBitCode cruxOpts llvmOpts svOpts taskMap
       evaluateBenchmarkLLVM cruxOpts llvmOpts svOpts ts


genSVCOMPBitCode :: Logs => CruxOptions -> LLVMOptions -> SVCOMPOptions -> TaskMap
                 -> IO [(Int, VerificationTask, Either SomeException FilePath)]
genSVCOMPBitCode cruxOpts llvmOpts svOpts tm = concat <$> mapM goTask (zip [0::Int ..] (Map.toList tm))
 where
 goTask (n, ((task, tgtWidth), bss)) = action `catch` handler
   where
   outputPath = svTaskDirectory (Crux.outDir cruxOpts) n task

   action =
     do tgt <- getTarget tgtWidth bss
        rslt <- processVerificationTask tgt n task
        return $! maybe [] (\outFile -> [(n, task, Right outFile)]) rslt

   handler e
     | Just (_::AsyncException) <- fromException e = throwIO e
     | otherwise =
         do sayFail "SVCOMP" $ unlines [ "Failed to compile task:"
                                       , show (verificationSourceFile task)
                                       , displayException e]
            removeDirectoryRecursive outputPath `catch` \e' ->
               sayFail "SVCOMP" $ unlines [ "Double fault! While trying to remove:"
                                          , outputPath
                                          , displayException (e'::SomeException)]
            return [(n, task, Left e)]


 getTarget tgtWidth bss =
   case tgtWidth of
     Just 32 -> return "i386-unknown-linux-elf"
     Just 64 -> return "x86_64-unknown-linux-elf"
     Just x  -> fail $ "Unexpected architecture width (" ++ show x ++ ") for benchmark(s) " ++ show (map benchmarkName bss)
     Nothing -> fail $ "Missing architecture width for benchmark(s) " ++ show (map benchmarkName bss)

 processVerificationTask _tgt _num task
   | or [ isSuffixOf bl (verificationSourceFile task) | bl <- svcompBlacklist svOpts ]
   = do sayWarn "SVCOMP" $ unlines
          [ "Skipping:"
          , "  " ++ verificationSourceFile task ++ " due to blacklist"
          ]
        return Nothing

 processVerificationTask tgt num task =
   let files = verificationInputFiles task in
     if null files
     then do sayWarn "SVCOMP" $ unlines
               [ "Skipping:"
               , "  " ++ verificationSourceFile task ++ " because no input files are present"
               ]
             return Nothing
     else
       do let taskFile = verificationSourceFile task
              inputBase = takeDirectory taskFile
              outputPath  = svTaskDirectory (Crux.outDir cruxOpts) num task
              llvmOpts' = llvmOpts { targetArch = Just tgt }
              cruxOpts' = cruxOpts { bldDir = outputPath }
              outName = "svcomp~" <> head files -<.> ".bc"
          createDirectoryIfMissing True outputPath
          copyFile taskFile (outputPath </> takeFileName taskFile)
          Just <$> genBitCodeToFile outName ((inputBase </>) <$> files) cruxOpts' llvmOpts' True


svTaskDirectory :: FilePath -> Int -> VerificationTask -> FilePath
svTaskDirectory base num task = base </> path
 where
 files = verificationInputFiles task
 path  = padTaskNum ++ filebase files

 padWidth = 5

 filebase [] = ""
 filebase (f:_) = '_' : takeFileName f

 padTaskNum = padding ++ xs
   where
   padding = take (padWidth - length xs) (repeat '0')
   xs = show num

hGetContentsStrict :: Handle -> IO String
hGetContentsStrict hdl =
  do s <- hGetContents hdl
     length s `seq` return s

evaluateBenchmarkLLVM :: Logs => CruxOptions -> LLVMOptions -> SVCOMPOptions
                      -> [(Int, VerificationTask, Either SomeException FilePath)]
                      -> IO ()
evaluateBenchmarkLLVM cruxOpts llvmOpts svOpts ts =
   bracket (openFile (svcompOutputFile svOpts) WriteMode)
           (\jsonOutHdl -> LBS.hPutStr jsonOutHdl "]\n" >> hClose jsonOutHdl)
           (\jsonOutHdl -> mapM_ (evaluateVerificationTask jsonOutHdl) ts)

 where
 megabyte = bit 20 :: Integer

 maybeSetLim _ Nothing = return ()
 maybeSetLim res (Just lim) =
   setResourceLimit res (ResourceLimits (ResourceLimit lim) ResourceLimitUnknown)

 root = Crux.outDir cruxOpts

 evaluateVerificationTask jsonOutHdl (num, task, compileErrOrOutFile) =
    do ed <- case compileErrOrOutFile of
         Left ex ->
           failTask num task "Failed to compile task" ex
         Right inpBCFile ->
           try (executeTask num task inpBCFile) >>= \case
             Left ex
               | Just (_::AsyncException) <- fromException ex -> throwIO ex
               | otherwise -> failTask num task "Failed during process coordination" ex
             Right ed -> return ed

       let leadingString
              | num == 0 = "[\n"
              | otherwise= ",\n"

       LBS.hPutStr jsonOutHdl leadingString
       LBS.hPutStr jsonOutHdl (encode ed)
       LBS.hPutStr jsonOutHdl "\n"
       hFlush jsonOutHdl

 failTask num task msg ex =
    do let taskRoot = svTaskDirectory root num task
       let sourceFile = verificationSourceFile task
       let err = unlines [msg, displayException ex]
       return EvaluationData
              { taskRoot = taskRoot
              , sourceFile = sourceFile
              , elapsedTime = 0
              , exitCode = Nothing
              , evaluationResult = Left err
              , subprocessOutput = ""
              }

 executeTask num task inpBCFile =
    do let taskRoot = svTaskDirectory root num task
       let sourceFile = verificationSourceFile task

       (readFd, writeFd) <- createPipe
       (jsonReadFd, jsonWriteFd) <- createPipe
       readHdl <- fdToHandle readFd
       jsonReadHdl <- fdToHandle jsonReadFd

       sayOK "SVCOMP" $ concat
         [ "Evaluating:\n"
         , "  " ++ taskRoot ++ "\n"
         , "  " ++ sourceFile
         ]

       startTime <- getCurrentTime

       pid <- forkProcess $
                do maybeSetLim ResourceCPUTime (svcompCPUlimit svOpts)
                   maybeSetLim ResourceTotalMemory ((megabyte *) <$> svcompMemlimit svOpts)
                   writeHdl <- fdToHandle writeFd
                   jsonHdl <- fdToHandle jsonWriteFd
                   evaluateSingleTask writeHdl jsonHdl cruxOpts llvmOpts root num task inpBCFile
                   exitSuccess

       ast  <- async (getProcessStatus True {- Block -} False {- stopped -} pid)
       aout <- async (hGetContentsStrict readHdl)
       ares <- async (eitherDecode' <$> LBS.hGetContents jsonReadHdl)

       st <- wait ast
       endTime <- getCurrentTime

       closeFd writeFd
       out <- wait aout
       output out

       closeFd jsonWriteFd
       res <- wait ares

       let wallTime = diffUTCTime endTime startTime
       sayOK "SVCOMP" $ unwords ["Elapsed wall-clock time:", show wallTime]

       case st of
         Just (Exited ExitSuccess) ->
           return ()
         Just (Exited (ExitFailure x)) ->
           sayFail "SVCOMP" $ unwords ["Evaluation process exited with failure code", show x]
         Just (Terminated sig _) ->
           sayWarn "SVCOMP" $ unwords ["Evaluation process terminated by signal", show sig]
         Just (Stopped sig) ->
           sayWarn "SVCOMP" $ unwords ["Evaluation process stopped by signal", show sig]
         Nothing ->
           sayFail "SVCOMP" "Could not retrieve evauation process status"

       return EvaluationData
              { taskRoot = taskRoot
              , sourceFile = sourceFile
              , elapsedTime = wallTime
              , exitCode = st
              , evaluationResult = res
              , subprocessOutput = out
              }


instance ToJSON ProcessStatus where
  toJSON (Exited ec)        = object [("exited", toJSON x)]
    where x = case ec of
                ExitSuccess  -> 0
                ExitFailure e -> e
  toJSON (Terminated sig _) = object [("terminated",toJSON (fromEnum sig))]
  toJSON (Stopped sig)      = object [("stopped", toJSON (fromEnum sig))]

data EvaluationData =
  EvaluationData
  { taskRoot :: String
  , sourceFile :: String
  , evaluationResult :: Either String EvaluationResult
  , elapsedTime :: NominalDiffTime
  , exitCode :: Maybe ProcessStatus
  , subprocessOutput :: String
  }
 deriving (Eq,Ord,Show,Generic)


instance ToJSON EvaluationData
instance ToJSONKey EvaluationData

data EvaluationResult =
  EvaluationResult
  { computedResult :: Maybe Bool
  , expectedResult :: Maybe Bool
  , totalGoals :: Integer
  , disprovedGoals :: Integer
  , unknownGoals :: Integer
  , provedGoals :: Integer
  , incompleteGoals :: Integer
  , programComplete :: Bool
  }
 deriving (Eq,Ord,Show,Generic)

instance ToJSON EvaluationResult
instance FromJSON EvaluationResult
instance ToJSONKey EvaluationResult

evaluateSingleTask :: Handle -> Handle -> CruxOptions -> LLVMOptions
                   -> FilePath
                   -> Int -> VerificationTask -> FilePath -> IO ()
evaluateSingleTask writeHdl jsonHdl cruxOpts llvmOpts bsRoot num task inpBCFile =
   do let taskRoot = svTaskDirectory bsRoot num task
      let srcRoot  = takeDirectory (verificationSourceFile task)
      let inputs   = map (srcRoot </>) (verificationInputFiles task)
      let cruxOpts' = cruxOpts { outDir = taskRoot, inputFiles = inputs }

      let ?outputConfig = OutputConfig False writeHdl writeHdl False

      mres <- try $
               do res <- Crux.runSimulator cruxOpts' (simulateLLVMFile inpBCFile llvmOpts)
                  generateReport cruxOpts' res
                  return res

      case mres of
        Left e ->
          do sayFail "SVCOMP" $ unlines
               [ "Simulator threw exception:"
               , displayException (e :: SomeException)
               ]
             hClose writeHdl
             hClose jsonHdl
             exitFailure

        Right (CruxSimulationResult cmpl gls) ->
          do let totalGoals = sum (Crux.totalProcessedGoals . fst <$> gls)
             let disprovedGoals = sum (Crux.disprovedGoals . fst <$> gls)
             let provedGoals = sum (Crux.provedGoals . fst <$> gls)
             let incompleteGoals = sum (Crux.incompleteGoals . fst <$> gls)
             let unknownGoals = totalGoals - (disprovedGoals + provedGoals + incompleteGoals)

             let programComplete =
                   case cmpl of
                     ProgramComplete -> True
                     ProgramIncomplete -> False

             let verdict
                   | disprovedGoals > 0 = Falsified
                   | ProgramComplete <- cmpl
                   , provedGoals == totalGoals = Verified
                   | otherwise = Unknown

             let expectedResult = propertyVerdict task

             let computedResult = case verdict of
                                    Verified -> Just True
                                    Falsified -> Just False
                                    Unknown -> Nothing

             case expectedResult of
               Nothing -> sayWarn "SVCOMP" $ unlines (["No verdict to evaluate!"] ++ map show (verificationProperties task))
               Just True ->
                 case verdict of
                   Verified  ->
                      sayOK "SVCOMP" "CORRECT (Verified)"
                   Falsified ->
                      sayFail "SVCOMP" $ unwords ["FAILED! benchmark should be verified"]
                   Unknown   -> sayWarn "SVCOMP" "UNKNOWN (Should verify)"
               Just False ->
                 case verdict of
                   Verified  ->
                      sayFail "SVCOMP" $ unwords ["FAILED! benchmark should contain an error!"]
                   Falsified ->
                      sayOK "SVCOMP" "CORRECT (Falisifed)"
                   Unknown ->
                      sayWarn "SVCOMP" "UNKNOWN (Should falsify)"

             LBS.hPut jsonHdl (encode EvaluationResult{ .. })

             hClose writeHdl
             hClose jsonHdl
