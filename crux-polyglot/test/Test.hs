{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

import qualified Config.Schema.Load as CfgL
import qualified Config.Schema.Spec as CfgS
import           Control.Lens ( (^.) )
import           Data.IORef
import qualified Data.Map.Strict as Map
import qualified Prettyprinter as PP
import           System.Exit ( ExitCode(ExitSuccess) )
import           System.FilePath ( takeFileName, (-<.>) )
import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Config as CfgV
import qualified Crux
import qualified Crux.Config.Common as CCC
import qualified Crux.LLVM.Compile as CLCmp
import qualified Crux.LLVM.Simulate as LLVMSim
import qualified Crux.Model as CM
import qualified Crux.Types as CT
import qualified Data.Parameterized.Context as C
import qualified Data.Parameterized.Context.Unsafe as U
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.FunctionHandle as CFH
import           Lang.Crucible.LLVM.Errors ( ppBB )
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.Simulator.SimError ( SimError, ppSimError )
import qualified What4.Expr as W4
import qualified What4.Expr.Builder as WEB

import qualified Crux.Polyglot.Config as PC


-- | Runs the various tests.
--
-- Warning: this will parse actual command-line parameters, so
-- specifying something like "--config" on the testing command line
-- will cause the tests to read that config file and potentially be
-- altered.
main :: IO ()
main = defaultMain $
       testCase "basic, two C files" $
       do let inpfiles = [ "test/samples/ex3/main.c"
                         , "test/samples/ex3/helper.c"
                         ]
          let ?outputConfig = Crux.defaultOutputConfig
          opts <- testOptions inpfiles

          (cruxOpts, pgOpts) <- PC.processPolyglotOpts opts
          initCB <- simulatePolyglot cruxOpts pgOpts
          res <- Crux.runSimulator cruxOpts initCB
          rval <- Crux.postprocessSimResult cruxOpts res
          rval @?= ExitSuccess


-- | Generate test Options for a specified set of files.  Instead of
--
-- > cfg <- PC.cruxPolyglotConfig
-- > Crux.loadOptions Crux.defaultOutputConfig "crux-polyglot" "0.1" cfg $ ...
--
-- which would read the actual command-line, config file,
-- and environment variables, the following constructs the
-- options with only the elements desired by this test.

testOptions :: Crux.Logs => [FilePath] -> IO (CCC.CruxOptions, PC.PolyglotOptions)
testOptions inpfiles =
  do cfg <- Crux.cfgJoin CCC.cruxOptions <$> PC.cruxPolyglotConfig
     let defaultOpts = (CfgL.loadValue
                         (CfgS.sectionsSpec "crux-polyglot-test" (Crux.cfgFile cfg) )
                         (CfgV.Sections () []))
     case defaultOpts of
       Left err -> error $ "failed to init default options: " <> show err
       Right (c,p) -> do c' <- CCC.postprocessOptions (c {CCC.inputFiles = inpfiles})
                         return (c', p)


simulatePolyglot :: Crux.Logs => Crux.CruxOptions -> PC.PolyglotOptions -> IO Crux.SimulatorCallback
simulatePolyglot cruxOpts pgOpts =

  do llvmModules <-
       let llvmPrep :: FilePath -> IO FilePath
           llvmPrep i = let o = "cply~" <> takeFileName i -<.> ".bc" in
                          CLCmp.genBitCodeToFile o [i] cruxOpts (PC.llvmPGOpts pgOpts) False
       in mapM llvmPrep (CCC.inputFiles cruxOpts) :: IO [FilePath]

     return $ Crux.SimulatorCallback $ setupPolyglotState pgOpts llvmModules


type PolyExt arch = U.EmptyCtx '::> LLVM arch '::> LLVM arch
data ExtVal a = ExtVal a


setupPolyglotState :: CB.IsSymInterface sym
                   => sym ~ WEB.ExprBuilder t st fs
                   => Crux.Logs
                   => PC.PolyglotOptions
                   -> [FilePath]
                   -> sym
                   -> Maybe (Crux.SomeOnlineSolver sym)
                   -> IO (Crux.RunnableState sym,
                          Maybe (W4.GroundEvalFn t) -> CT.LPred sym SimError -> IO (PP.Doc ann))
setupPolyglotState pgOpts bcFiles sym mb'Online = do
  halloc <- CFH.newHandleAllocator
  bbMapRef <- newIORef (Map.empty :: LLVMMem.LLVMAnnMap sym)
  -- let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
  let ?recordLLVMAnnotation = modifyIORef bbMapRef . Map.insert
  cbs <- mapM (\f -> LLVMSim.setupFileSim halloc f (PC.llvmPGOpts pgOpts) sym mb'Online) bcFiles

  --                 , _functionBindings      :: !(FunctionBindings personality sym ext)
  -- type FunctionBindings p sym ext = FnHandleMap (FnState p sym ext)
  --  data FnState p sym ext (args :: Ctx CrucibleType) (ret :: CrucibleType)
  --   = UseOverride !(Override p sym ext args ret)
  --   | forall blocks . UseCFG !(CFG ext blocks args ret) !(CFGPostdom blocks)

  let simctx = initSimContext sym
               llvmIntrinsicTypes -- KWQ ??
               halloc
               stdout
               (fnBindingsFromList [])
               (llvmExtensionImpl (memOpts llvmOpts)) -- KWQ ?? mo :: MemOptions
               CM.emptyModel
        -- & profilingMetrics %~ Map.union (llvmMetrics llvmCtxt) -- KWQ

  -- arbitrary, we should probably make this limit configurable
  let detailLimit = 10

  let explainFailure evalFn gl =
        do bb <- readIORef bbMapRef
           ex <- LLVMMem.explainCex sym bb evalFn >>= \f -> f (gl ^. CB.labeledPred)
           let details =
                 case ex of
                   LLVMMem.NoExplanation -> mempty
                   LLVMMem.DisjOfFailures xs ->
                     case map ppBB xs of
                       []  -> mempty
                       [x] -> PP.indent 2 x
                       xs' | length xs' <= detailLimit
                             -> PP.vcat [ "All of the following conditions failed:"
                                        , PP.indent 2 (PP.vcat xs')
                                        ]
                           | otherwise
                             -> PP.vcat
                                [ "All of the following conditions failed (and other conditions have been elided to reduce output): "
                                , PP.indent 2 (PP.vcat (take detailLimit xs'))
                                ]
           return $ PP.vcat [ ppSimError (gl^. CB.labeledPredMsg), details ]

  return (head cbs, explainFailure)
