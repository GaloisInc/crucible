{-# Language OverloadedStrings #-}
module Main (main) where

import Control.Monad
import Data.Bits( bit )
import Data.List
  ( isSuffixOf )
import qualified Data.Text as Text
import System.Exit
  ( exitFailure, ExitCode(..) )
import System.FilePath
  ( takeFileName, takeDirectory, (</>)
  , replaceExtension
  )
import System.Directory
  ( createDirectoryIfMissing, doesFileExist, copyFile )

-- unix
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


evaluateBenchmarkLLVM :: Logs => CruxOptions -> LLVMOptions -> SVCOMPOptions -> BenchmarkSet -> IO ()
evaluateBenchmarkLLVM cruxOpts llvmOpts svOpts bs =
   mapM_ (evaluateVerificationTask) (zip [0::Int ..] (benchmarkTasks bs))

 where
 megabyte = bit 20 :: Integer

 maybeSetLim _ Nothing = return ()
 maybeSetLim res (Just lim) =
   setResourceLimit res (ResourceLimits (ResourceLimit lim) ResourceLimitUnknown)

 bsRoot = Crux.outDir cruxOpts </> Text.unpack (benchmarkName bs)

 evaluateVerificationTask (_num,task)
   | or [ isSuffixOf bl (verificationSourceFile task) | bl <- svcompBlacklist svOpts ]
   = sayWarn "SVCOMP" $ unlines
        [ "Skipping:"
        , "  " ++ verificationSourceFile task
        ]

 evaluateVerificationTask (num, task) =
    do pid <- forkProcess $
                do maybeSetLim ResourceCPUTime (svcompCPUlimit svOpts)
                   maybeSetLim ResourceTotalMemory ((megabyte *) <$> svcompMemlimit svOpts)
                   evaluateSingleTask cruxOpts llvmOpts bsRoot num task

       st <- getProcessStatus True {- Block -} False {- stopped -} pid
       case st of
         Just (Exited ExitSuccess) ->
           return ()
         Just (Exited (ExitFailure x)) ->
           sayFail "SVCOMP" $ "Evaluation process exited with failure code " ++ show x
         Just (Terminated sig _) ->
           sayFail "SVCOMP" $ "Evaluation process terminated by signal " ++ show sig
         Just (Stopped sig) ->
           sayFail "SVCOMP" $ "Evaluation process stopped by signal " ++ show sig
         Nothing ->
           sayFail "SVCOMP" "Could not retrieve evauation process status"


evaluateSingleTask :: Logs => CruxOptions -> LLVMOptions -> FilePath -> Int -> VerificationTask -> IO ()
evaluateSingleTask cruxOpts llvmOpts bsRoot num task =
   do let taskRoot = svTaskDirectory bsRoot num task
      let srcRoot  = takeDirectory (verificationSourceFile task)
      let inputs   = map (srcRoot </>) (verificationInputFiles task)
      let cruxOpts' = cruxOpts { outDir = taskRoot, inputFiles = inputs }
      sayOK "SVCOMP" $ unlines
        [ "Evaluating:"
        , "  " ++ taskRoot
        , "  " ++ verificationSourceFile task
        ]
      res@(CruxSimulationResult cmpl gls) <- Crux.runSimulator cruxOpts' (simulateLLVM cruxOpts' llvmOpts)
      generateReport cruxOpts' res

      let verdict
            | sum (fmap countDisprovedGoals gls) > 0 = Falsified
            | ProgramComplete <- cmpl
            , sum (fmap countUnknownGoals gls) == 0 = Verified
            | otherwise                             = Unknown

      case propertyVerdict task of
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
