{-# Language DeriveGeneric #-}
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main (main) where

import Control.Concurrent.Async( async, wait )
import Control.Exception (bracket)
import Control.Monad

import Data.Aeson ( encode, ToJSON(..), FromJSON, ToJSONKey, eitherDecode', object )
import Data.Bits( bit )
import qualified Data.ByteString.Lazy as LBS
import GHC.Generics (Generic)
import Data.List
  ( isSuffixOf )
import qualified Data.Text as Text
import Data.Time.Clock
  ( getCurrentTime, diffUTCTime, NominalDiffTime )
import System.Exit
  ( exitFailure, ExitCode(..) )
import System.FilePath
  ( takeFileName, takeDirectory, (</>)
  , replaceExtension
  )
import System.Directory
  ( createDirectoryIfMissing, doesFileExist, copyFile )
import System.IO
  ( Handle, hGetContents, hClose, openFile, IOMode(..) )

-- unix
import System.Posix.IO
import System.Posix.Process
import System.Posix.Resource

-- crux
import qualified Crux
import Crux.Config.Common(CruxOptions(..))
import Crux.Log
import Crux.Goal
import Crux.Report
import Crux.SVCOMP
import Crux.Types

-- local
import Crux.LLVM.Config
import Crux.LLVM.Compile
import Crux.LLVM.Simulate
import CruxLLVMMain( processLLVMOptions )

main :: IO ()
main = do
  let opts = Crux.cfgJoin llvmCruxConfig svcompOptions
  Crux.loadOptions defaultOutputConfig "crux-llvm-svcomp" "0.1" opts $ \(co0,(lo0,svOpts)) ->
    do (cruxOpts, llvmOpts) <- processLLVMOptions (co0,lo0)
       bss <- loadSVCOMPBenchmarks cruxOpts
       genSVCOMPBitCode cruxOpts llvmOpts svOpts bss
       mapM_ (evaluateBenchmarkLLVM cruxOpts llvmOpts svOpts) bss


genSVCOMPBitCode :: Logs => CruxOptions -> LLVMOptions -> SVCOMPOptions -> [BenchmarkSet] -> IO ()
genSVCOMPBitCode cruxOpts llvmOpts svOpts = mapM_ processBenchmark
 where
 processBenchmark bs =
   do let nm = benchmarkName bs
      say "SVCOMP" $ unwords ["Preparing", show nm]
      tgt <- getTarget bs
      mapM_ (processVerificationTask tgt (Text.unpack nm)) (zip [0::Int ..] (benchmarkTasks bs))

 processVerificationTask _tgt _benchName (_num,task)
   | or [ isSuffixOf bl (verificationSourceFile task) | bl <- svcompBlacklist svOpts ]
   = return ()

 processVerificationTask tgt benchName (num,task) =
   do let files = verificationInputFiles task
          inputBase = takeDirectory (verificationSourceFile task)
          outputPath  = svTaskDirectory (Crux.outDir cruxOpts </> benchName) num task
          finalBCFile = outputPath </> "combined.bc"
          srcBCNames = [ (inputBase </> src, outputPath </> replaceExtension src ".bc") | src <- files ]
          incs src = [ inputBase </> takeDirectory src
                     , libDir llvmOpts </> "includes"
                     ] ++ incDirs llvmOpts
          params (src, srcBC) =
            [ "-c", "-g", "-emit-llvm", "-O1", "-fsanitize=shift", "-fsanitize-trap=shift", "--target=" ++ tgt ] ++
            concat [ ["-I", dir] | dir <- incs src ] ++
            [ "-o", srcBC, src ]

      createDirectoryIfMissing True outputPath

      finalBcExists <- doesFileExist finalBCFile
      unless (finalBcExists && lazyCompile llvmOpts) $
        do forM_ srcBCNames $ \(src, srcBC) ->
              do copyFile src (takeDirectory srcBC </> takeFileName src)
                 copyFile (verificationSourceFile task) (takeDirectory srcBC </> takeFileName (verificationSourceFile task))
                 bcExists <- doesFileExist srcBC
                 unless (bcExists && lazyCompile llvmOpts) $
                   runClang llvmOpts (params (src, srcBC))
           llvmLink llvmOpts (map snd srcBCNames) finalBCFile

 getTarget bs =
   case benchmarkArchWidth bs of
     Just 32 -> return "i386-unknown-linux-elf"
     Just 64 -> return "x86_64-unknown-linux-elf"
     Just x ->
       do sayFail "SVCOMP" $
             "Unexpected architecture width (" ++ show x ++ ") for benchmark " ++ show (benchmarkName bs)
          exitFailure
     Nothing ->
       do sayFail "SVCOMP" $
             "Missing architecture width for benchmark " ++ show (benchmarkName bs)
          exitFailure

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

evaluateBenchmarkLLVM :: Logs => CruxOptions -> LLVMOptions -> SVCOMPOptions -> BenchmarkSet -> IO ()
evaluateBenchmarkLLVM cruxOpts llvmOpts svOpts bs =
   bracket (openFile (svcompOutputFile svOpts) WriteMode) hClose $ \jsonOutHdl ->
     mapM_ (evaluateVerificationTask jsonOutHdl) (zip [0::Int ..] (benchmarkTasks bs))


 where
 megabyte = bit 20 :: Integer

 maybeSetLim _ Nothing = return ()
 maybeSetLim res (Just lim) =
   setResourceLimit res (ResourceLimits (ResourceLimit lim) ResourceLimitUnknown)

 bsRoot = Crux.outDir cruxOpts </> Text.unpack (benchmarkName bs)

 evaluateVerificationTask _ (_num,task)
   | or [ isSuffixOf bl (verificationSourceFile task) | bl <- svcompBlacklist svOpts ]
   = sayWarn "SVCOMP" $ unlines
        [ "Skipping:"
        , "  " ++ verificationSourceFile task
        ]

 evaluateVerificationTask jsonOutHdl (num, task) =
    do (readFd, writeFd) <- createPipe
       (jsonReadFd, jsonWriteFd) <- createPipe
       readHdl <- fdToHandle readFd
       jsonReadHdl <- fdToHandle jsonReadFd

       let taskRoot = svTaskDirectory bsRoot num task
       let sourceFile = verificationSourceFile task
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
                   evaluateSingleTask writeHdl jsonHdl cruxOpts llvmOpts bsRoot num task

       ast <- async (getProcessStatus True {- Block -} False {- stopped -} pid)
       aout <- async (hGetContentsStrict readHdl)
       ares <- async (eitherDecode' <$> LBS.hGetContents jsonReadHdl)

       st <- wait ast
       endTime <- getCurrentTime

       closeFd writeFd
       out <- wait aout
       output out

       closeFd jsonWriteFd
       res <- wait ares

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

       let wallTime = diffUTCTime endTime startTime
       sayOK "SVCOMP" $ unwords ["Elapsed wall-clock time:", show wallTime]

       let ed = EvaluationData
                { taskRoot = taskRoot
                , sourceFile = sourceFile
                , elapsedTime = wallTime
                , exitCode = st
                , evaluationResult = res
                , subprocessOutput = out
                }
       LBS.hPutStr jsonOutHdl (encode ed)
       LBS.hPutStr jsonOutHdl "\n"

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
  , totalGoals :: Int
  , disprovedGoals :: Int
  , unknownGoals :: Int
  , provedGoals :: Int
  , programComplete :: Bool
  }
 deriving (Eq,Ord,Show,Generic)

instance ToJSON EvaluationResult
instance FromJSON EvaluationResult
instance ToJSONKey EvaluationResult

evaluateSingleTask :: Handle -> Handle -> CruxOptions -> LLVMOptions -> FilePath -> Int -> VerificationTask -> IO ()
evaluateSingleTask writeHdl jsonHdl cruxOpts llvmOpts bsRoot num task =
   do let taskRoot = svTaskDirectory bsRoot num task
      let srcRoot  = takeDirectory (verificationSourceFile task)
      let inputs   = map (srcRoot </>) (verificationInputFiles task)
      let cruxOpts' = cruxOpts { outDir = taskRoot, inputFiles = inputs }

      let ?outputConfig = OutputConfig False writeHdl writeHdl False
      res@(CruxSimulationResult cmpl gls) <- Crux.runSimulator cruxOpts' (simulateLLVM cruxOpts' llvmOpts)
      generateReport cruxOpts' res

      let totalGoals = sum (fmap countTotalGoals gls)
      let disprovedGoals = sum (fmap countDisprovedGoals gls)
      let unknownGoals = sum (fmap countUnknownGoals gls)
      let provedGoals = sum (fmap countProvedGoals gls)
      let programComplete =
            case cmpl of
              ProgramComplete -> True
              ProgramIncomplete -> False

      let verdict
            | disprovedGoals > 0 = Falsified
            | ProgramComplete <- cmpl
            , unknownGoals == 0 = Verified
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
