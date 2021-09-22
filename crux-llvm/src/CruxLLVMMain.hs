{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language ImplicitParams #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}

module CruxLLVMMain
  ( CruxLLVMLogging
  , cruxLLVMLoggingToSayWhat
  , defaultOutputConfig
  , mainWithOptions
  , mainWithOutputTo
  , mainWithOutputConfig
  , Crux.mkOutputConfig
  , processLLVMOptions
  , withCruxLLVMLogging
  )
  where

import           Data.Aeson ( ToJSON )
import           GHC.Generics ( Generic )
import           System.Directory ( createDirectoryIfMissing )
import           System.Exit ( ExitCode )
import           System.FilePath ( dropExtension, takeFileName, (</>) )
import           System.IO ( Handle )

-- crux
import qualified Crux
import qualified Crux.Log as Log
import           Crux.Config.Common (CruxOptions(..))

-- local
import           Crux.LLVM.Config
import           Crux.LLVM.Compile
import qualified Crux.LLVM.Log as Log
import           Crux.LLVM.Simulate
import           Paths_crux_llvm (version)


mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig $
  Crux.mkOutputConfig (h, True) (h, True) cruxLLVMLoggingToSayWhat

data CruxLLVMLogging
  = LoggingCrux Crux.CruxLogMessage
  | LoggingCruxLLVM Log.CruxLLVMLogMessage
  deriving ( Generic, ToJSON )

cruxLLVMLoggingToSayWhat :: CruxLLVMLogging -> Crux.SayWhat
cruxLLVMLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
cruxLLVMLoggingToSayWhat (LoggingCruxLLVM msg) = Log.cruxLLVMLogMessageToSayWhat msg

defaultOutputConfig :: IO (Maybe CruxOptions -> Log.OutputConfig CruxLLVMLogging)
defaultOutputConfig = Crux.defaultOutputConfig cruxLLVMLoggingToSayWhat

withCruxLLVMLogging ::
  (
    Log.SupportsCruxLogMessage CruxLLVMLogging =>
    Log.SupportsCruxLLVMLogMessage CruxLLVMLogging =>
    a
  ) -> a
withCruxLLVMLogging a =
  let
    ?injectCruxLogMessage = LoggingCrux
    ?injectCruxLLVMLogMessage = LoggingCruxLLVM
  in a

mainWithOutputConfig ::
  (Maybe CruxOptions -> Log.OutputConfig CruxLLVMLogging) ->
  IO ExitCode
mainWithOutputConfig mkOutCfg = withCruxLLVMLogging $ do
  cfg <- llvmCruxConfig
  Crux.loadOptions mkOutCfg "crux-llvm" version cfg mainWithOptions

mainWithOptions ::
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  (CruxOptions, LLVMOptions) -> IO ExitCode
mainWithOptions initOpts =
  do
    (cruxOpts, llvmOpts) <- processLLVMOptions initOpts
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
