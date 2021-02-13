{-# Language OverloadedStrings #-}
module CruxLLVMMain
  ( mainWithOutputTo, mainWithOutputConfig, defaultOutputConfig, processLLVMOptions )
  where

import System.Exit
  ( ExitCode )
import System.IO
  ( Handle )
import System.FilePath
  ( dropExtension, takeFileName, (</>) )
import System.Directory
  ( createDirectoryIfMissing )

-- crux
import qualified Crux
import Crux.Log (OutputConfig(..), defaultOutputConfig)
import Crux.Config.Common(CruxOptions(..))

-- local
import Crux.LLVM.Config
import Crux.LLVM.Compile
import Crux.LLVM.Simulate


mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig (OutputConfig False h h False)

mainWithOutputConfig :: OutputConfig -> IO ExitCode
mainWithOutputConfig outCfg = do
  cfg <- llvmCruxConfig
  Crux.loadOptions outCfg "crux-llvm" "0.1" cfg $ \initOpts ->
    do (cruxOpts, llvmOpts) <- processLLVMOptions initOpts
       bcFile <- genBitCode cruxOpts llvmOpts
       res <- Crux.runSimulator cruxOpts (simulateLLVMFile bcFile llvmOpts)
       makeCounterExamplesLLVM cruxOpts llvmOpts res
       Crux.postprocessSimResult cruxOpts res

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
