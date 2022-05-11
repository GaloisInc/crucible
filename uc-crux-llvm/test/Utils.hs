{-
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils
  ( testDir,
    withOptions,
    simulateFunc
  ) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Control.Exception (try)
import           Data.Maybe (fromMaybe, isNothing)
import           System.Environment (lookupEnv)
import           System.FilePath ((</>))
import           System.IO (IOMode(WriteMode), withFile)

import qualified Text.LLVM.AST as L

import qualified What4.ProblemFeatures as What4 (noFeatures)

import qualified Lang.Crucible.CFG.Core as Crucible
import           Lang.Crucible.FunctionHandle (HandleAllocator, newHandleAllocator)

import           Lang.Crucible.LLVM.Intrinsics as CLLVM (defaultIntrinsicsOptions)
import qualified Lang.Crucible.LLVM.MemModel as CLLVM
import           Lang.Crucible.LLVM.Translation as CLLVM (defaultTranslationOptions)

import qualified Crux
import qualified Crux.Config.Load as Crux hiding (colorOptions)
import qualified Crux.Config.Common as Crux
import qualified Crux.Log as Log

import           Crux.LLVM.Config (LLVMOptions)
import qualified Crux.LLVM.Config as CruxLLVM
import           Crux.LLVM.Compile (genBitCode)
import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.App (AppContext, makeAppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, CFGWithTypes(..), defnTypes, findFun, withModulePtrWidth)
import           UCCrux.LLVM.Context.Function (FunctionContext, makeFunctionContext)
import           UCCrux.LLVM.Module (FuncSymbol(FuncDefnSymbol))
import           UCCrux.LLVM.Newtypes.FunctionName (functionNameFromString)
import           UCCrux.LLVM.Precondition (emptyPreconds)
import qualified UCCrux.LLVM.Logging as Log
import qualified UCCrux.LLVM.Main as Main
import qualified UCCrux.LLVM.Run.EntryPoints as EntryPoints
import qualified UCCrux.LLVM.Run.Simulate as Sim

import qualified Logging as Log
{- ORMOLU_ENABLE -}

testDir :: FilePath
testDir = "test/programs"

withOptions ::
  Maybe L.Module ->
  FilePath ->
  ( forall m arch.
    Log.Logs Log.UCCruxLLVMTestLogging =>
    Log.SupportsCruxLogMessage Log.UCCruxLLVMTestLogging =>
    AppContext ->
    ModuleContext m arch ->
    HandleAllocator ->
    Crux.CruxOptions ->
    LLVMOptions ->
    IO a
  ) ->
  IO a
withOptions llvmModule file k =
  Log.withUCCruxLLVMTestLogging $
  do
    withFile (testDir </> file <> ".output") WriteMode $ \h ->
      do
        let appCtx = makeAppContext Log.Low
        llOpts <- (\ll -> ll { CruxLLVM.noCompile = False }) <$> mkLLOpts ""
        let cruxOpts = mkCruxOpts [testDir </> file]
        let ?outputConfig =
              Crux.mkOutputConfig
                (h, False)
                (h, False)
                Log.ucCruxLLVMTestLoggingToSayWhat
                (Just (Crux.outputOptions cruxOpts))
        _ <- Crux.postprocessOptions cruxOpts -- Validate, create build directory
        path <-
          let complain exc = do
                Log.sayUCCruxLLVMTest Log.ClangTrouble
                Log.logException exc
                error ("aborting: " ++ show exc)
           in if isNothing llvmModule
              then try (genBitCode cruxOpts llOpts) >>= either complain return
              else return "<fake-path>"
        cruxOpts' <- Crux.postprocessOptions (mkCruxOpts [path])

        -- TODO(lb): It would be nice to print this only when the test fails
        -- putStrLn
        --   ( unwords
        --       [ "\nReproduce with:\n",
        --         "cabal v2-run exe:uc-crux-llvm -- ",
        --         "--entry-points",
        --         intercalate " --entry-points " (map show fns),
        --         testDir </> file
        --       ]
        --   )

        halloc <- newHandleAllocator
        memVar <- CLLVM.mkMemVar "uc-crux-llvm:test_llvm_memory" halloc
        Main.SomeModuleContext' modCtx <-
          case llvmModule of
            Just lMod -> Main.translateLLVMModule llOpts halloc memVar path lMod
            Nothing -> Main.translateFile llOpts halloc memVar path

        k appCtx modCtx halloc cruxOpts' llOpts

  where
    mkLLOpts :: FilePath -> IO CruxLLVM.LLVMOptions
    mkLLOpts libDir =
      do clang <- fromMaybe "clang" <$> lookupEnv "CLANG"
         llvmLink <- fromMaybe "llvm-link" <$> lookupEnv "LLVM_LINK"
         return $
           CruxLLVM.LLVMOptions
             { CruxLLVM.clangBin = clang
             , CruxLLVM.linkBin = llvmLink
             -- NB(lb): The -fno-wrapv here ensures that Clang will emit 'nsw' flags
             -- even on platforms using nixpkgs, which injects -fno-strict-overflow
             -- by default.
             , CruxLLVM.clangOpts = ["-fno-wrapv"]
             , CruxLLVM.libDir = libDir
             , CruxLLVM.incDirs = []
             , CruxLLVM.targetArch = Nothing
             , CruxLLVM.ubSanitizers = []
             , CruxLLVM.intrinsicsOpts = CLLVM.defaultIntrinsicsOptions
             , CruxLLVM.memOpts = CLLVM.defaultMemOptions
             , CruxLLVM.transOpts = CLLVM.defaultTranslationOptions
             , CruxLLVM.entryPoint = "main"
             , CruxLLVM.lazyCompile = False
             , CruxLLVM.noCompile = True
             , CruxLLVM.optLevel = 1
             , CruxLLVM.symFSRoot = Nothing
             , CruxLLVM.supplyMainArguments = CruxLLVM.NoArguments
             }

    mkCruxOpts :: [FilePath] -> Crux.CruxOptions
    mkCruxOpts files =
      Crux.CruxOptions
        { Crux.inputFiles = files
        , Crux.outDir = "" -- no reports
        , Crux.bldDir = "crux-build"
        , Crux.checkPathSat = True
        , Crux.profileCrucibleFunctions = False
        , Crux.profileSolver = False
        , Crux.branchCoverage = False
        , Crux.pathStrategy = Crux.SplitAndExploreDepthFirst
        , Crux.globalTimeout =
            Just (fromRational (toRational (5 :: Int)))
        , Crux.goalTimeout =
            Just (fromRational (toRational (5 :: Int)))
        , Crux.profileOutputInterval =
            fromRational (toRational (1.0 :: Double))
        , Crux.loopBound = Just 8
        , Crux.recursionBound = Just 8
        , Crux.makeCexes = False
        , Crux.unsatCores = False
        -- With Yices, cast_float_to_pointer_write.c hangs
        , Crux.solver = "z3"
        , Crux.pathSatSolver = Just "z3"
        , Crux.forceOfflineGoalSolving = False
        , Crux.pathSatSolverOutput = Nothing
        , Crux.onlineSolverOutput = Nothing
        , Crux.yicesMCSat = False
        , Crux.floatMode = "default"
        , Crux.proofGoalsFailFast = False
        , Crux.skipReport = True
        , Crux.skipSuccessReports = True
        , Crux.skipIncompleteReports = True
        , Crux.hashConsing = False
        , Crux.onlineProblemFeatures = What4.noFeatures
        , Crux.outputOptions = Crux.OutputOptions
          { Crux.colorOptions = Crux.allColors
          , Crux.printFailures = False
          , Crux.printSymbolicVars = False
          , Crux.quietMode = True
          , Crux.simVerbose = 0
          }
        }

simulateFunc ::
  FilePath ->
  -- | Function name
  String ->
  (forall m arch argTypes.
    ArchOk arch =>
    Log.Logs Log.UCCruxLLVMTestLogging =>
    Log.SupportsCruxLogMessage Log.UCCruxLLVMTestLogging =>
    AppContext ->
    ModuleContext m arch ->
    HandleAllocator ->
    Crux.CruxOptions ->
    LLVMOptions ->
    FunctionContext m arch argTypes ->
    IO (Sim.SimulatorCallbacks m arch argTypes r)) ->
  IO r
simulateFunc file func makeCallbacks =
  withOptions
    Nothing
    file
    ( \appCtx modCtx halloc cruxOpts llOpts ->
        do [entry] <-
            EntryPoints.getEntryPoints <$>
              EntryPoints.makeEntryPointsOrThrow
                (modCtx ^. defnTypes)
                [functionNameFromString func]
           withModulePtrWidth modCtx $
             do CFGWithTypes cfg argFTys _retTy _varArgs <-
                   pure (findFun modCtx (FuncDefnSymbol entry))
                let funCtx =
                      makeFunctionContext modCtx entry argFTys (Crucible.cfgArgTypes cfg)
                -- TODO(lb): also provide these
                -- let ?memOpts = CruxLLVM.memOpts llOpts
                -- let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
                cbs <- makeCallbacks appCtx modCtx halloc cruxOpts llOpts funCtx
                Sim.runSimulatorWithCallbacks
                  appCtx
                  modCtx
                  funCtx
                  halloc
                  (emptyPreconds argFTys)
                  cfg
                  cruxOpts
                  llOpts
                  cbs
    )
