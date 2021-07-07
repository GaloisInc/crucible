{-# Language ImplicitParams #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module CruxLLVMMain
  ( cruxLLVMLoggingToSayWhat
  , defaultOutputConfig
  , mainWithOutputTo
  , mainWithOutputConfig
  , Crux.mkOutputConfig
  , processLLVMOptions
  )
  where

import           System.Directory ( createDirectoryIfMissing )
import           System.Exit ( ExitCode )
import           System.FilePath ( dropExtension, takeFileName, (</>) )
import           System.IO ( Handle )

-- crux
import qualified Crux
import           Crux.Log as Log ( OutputConfig(..), cruxLogMessageToSayWhat )
import           Crux.Config.Common (CruxOptions(..))

-- local
import           Crux.LLVM.Config
import           Crux.LLVM.Compile
import qualified Crux.LLVM.Log as Log
import           Crux.LLVM.Simulate
import           Paths_crux_llvm (version)


mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig $
  Crux.mkOutputConfig True h h cruxLLVMLoggingToSayWhat

data CruxLLVMLogging
  = LoggingCrux Crux.CruxLogMessage
  | LoggingCruxLLVM Log.CruxLLVMLogMessage

cruxLLVMLoggingToSayWhat :: CruxLLVMLogging -> Crux.SayWhat
cruxLLVMLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
cruxLLVMLoggingToSayWhat (LoggingCruxLLVM msg) = Log.cruxLLVMLogMessageToSayWhat msg

defaultOutputConfig :: Maybe CruxOptions -> OutputConfig CruxLLVMLogging
defaultOutputConfig = Crux.defaultOutputConfig cruxLLVMLoggingToSayWhat

mainWithOutputConfig :: (Maybe CruxOptions -> OutputConfig CruxLLVMLogging) -> IO ExitCode
mainWithOutputConfig mkOutCfg = do
  let ?injectCruxLogMessage = LoggingCrux
  let ?injectCruxLLVMLogMessage = LoggingCruxLLVM
  cfg <- llvmCruxConfig
  Crux.loadOptions mkOutCfg "crux-llvm" version cfg $ \initOpts ->
    do (cruxOpts, llvmOpts) <- processLLVMOptions initOpts
       bcFile <- genBitCode cruxOpts llvmOpts
       res <- Crux.runSimulator cruxOpts $ simulateLLVMFile bcFile llvmOpts
       makeCounterExamplesLLVM cruxOpts llvmOpts res
       Crux.postprocessSimResult True cruxOpts res

processLLVMOptions :: (CruxOptions,LLVMOptions) -> IO (CruxOptions,LLVMOptions)
processLLVMOptions (cruxOpts,llvmOpts) =
  do -- keep looking for clangBin if it is unset
     clangFilePath <- if clangBin llvmOpts == ""
                        then getClang
                        else return (clangBin llvmOpts)

     let llvmOpts2 = llvmOpts { clangBin = clangFilePath }

     -- update outDir if unset
     name <- case Crux.inputFiles cruxOpts of
               x : _ -> pure (dropExtension (takeFileName x))
                          -- use the first file as output directory
               [] -> throwCError NoFiles

     let cruxOpts2 = if Crux.outDir cruxOpts == ""
                       then cruxOpts { Crux.outDir = "results" </> name }
                       else cruxOpts

         odir      = Crux.outDir cruxOpts2

     createDirectoryIfMissing True odir

     return (cruxOpts2, llvmOpts2)
