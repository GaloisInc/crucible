{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import Control.Lens (use)
import Control.Monad.IO.Class (MonadIO(..))

import qualified Data.List as List (sort)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(..))
import qualified Data.Text.IO as T

import qualified System.FilePath as Path
import qualified System.IO as IO

import Lang.Crucible.Backend (IsSymBackend, IsSymInterface)
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState (SymGlobalState, insertGlobal)
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Syntax.Atoms (GlobalName(..))
import Lang.Crucible.Syntax.Overrides as SyntaxOvrs
import Lang.Crucible.Types
import Lang.Crucible.CFG.Common (GlobalVar(..))

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure)
import Test.Tasty.Golden

import What4.Config
import What4.FunctionName
import What4.Interface (intLit)
import What4.Solver.Z3 (z3Options)

import Lang.Crucible.CLI

import Overrides as TestOvrs

main :: IO ()
main = do
  simTests <- findTests "Simulation" "test-data/simulate" testSimulator
  let allTests = testGroup "Tests" [resolvedExternTest, resolvedForwardDecTest, simTests]
  defaultMain allTests

findTests :: String -> FilePath -> (FilePath -> FilePath -> IO ()) -> IO TestTree
findTests group_name test_dir test_action =
  do inputs <- findByExtension [".cbl"] test_dir
     return $ testGroup group_name
       [ goldenFileTestCase input test_action
       | input <- List.sort inputs
       ]

goldenFileTestCase :: FilePath -> (FilePath -> FilePath -> IO ()) -> TestTree
goldenFileTestCase input test_action =
  goldenVsFileDiff
   (Path.takeBaseName input) -- test name
   (\x y -> ["diff", "-u", x, y])
   goodFile -- golden file path
   outFile
   (test_action input outFile) -- action whose result is tested
  where
    outFile = Path.replaceExtension input ".out"
    goodFile = Path.replaceExtension input ".out.good"

testOptions :: [ConfigDesc]
testOptions = z3Options

testSimulator :: FilePath -> FilePath -> IO ()
testSimulator inFile outFile =
  do contents <- T.readFile inFile
     IO.withFile outFile IO.WriteMode $ \outh -> do
       let hooks = 
             defaultSimulateProgramHooks
               { setupOverridesHook =  \bak ha ->
                   do os1 <- SyntaxOvrs.setupOverrides bak ha
                      os2 <- TestOvrs.setupOverrides bak ha
                      return $ concat [os1,os2]
               }
       simulateProgram inFile contents outh Nothing testOptions hooks False []

-- | A basic test that ensures a forward declaration behaves as expected when
-- invoked with an override that is assigned to it after parsing.
resolvedForwardDecTest :: TestTree
resolvedForwardDecTest =
  testGroup "Forward declarations"
  [ goldenFileTestCase ("test-data" Path.</> "declare" Path.</> "main.cbl") $ \mainCbl mainOut ->
    IO.withFile mainOut IO.WriteMode $ \outh ->
    do mainContents <- T.readFile mainCbl
       let hooks =
             defaultSimulateProgramHooks
               { setupHook = resolveForwardDecs
               }
       simulateProgram mainCbl mainContents outh Nothing testOptions hooks False []
  ]
  where
    resolveForwardDecs ::
      IsSymBackend sym bak =>
      bak ->
      HandleAllocator ->
      Map FunctionName SomeHandle ->
      OverrideSim p sym ext rtp a r ()
    resolveForwardDecs _bak _ha fds
      | Just (SomeHandle hdl) <- Map.lookup "foo" fds
      , Just Refl <- testEquality (handleArgTypes hdl) Ctx.empty
      , Just Refl <- testEquality (handleReturnType hdl) IntegerRepr
      = bindFnHandle hdl (UseOverride fooOv)

      | otherwise
      = fail "Could not find @foo function of the appropriate type"

    fooOv ::
      IsSymInterface sym =>
      Override p sym ext EmptyCtx IntegerType
    fooOv = mkOverride "foo" $ do
      sym <- use (stateContext.ctxSymInterface)
      liftIO $ intLit sym 42

-- | A basic test that ensures an extern behaves as expected after assigning a
-- value to it after parsing.
resolvedExternTest :: TestTree
resolvedExternTest =
  testGroup "Externs"
  [ goldenFileTestCase ("test-data" Path.</> "extern" Path.</> "main.cbl") $ \mainCbl mainOut ->
    IO.withFile mainOut IO.WriteMode $ \outh ->
    do mainContents <- T.readFile mainCbl
       let hooks =
             defaultSimulateProgramHooks
               { resolveExternsHook = resolveExterns
               }
       simulateProgram mainCbl mainContents outh Nothing testOptions hooks False []
  ]
  where
    resolveExterns ::
      IsSymInterface sym =>
      sym ->
      Map GlobalName (Some GlobalVar) ->
      SymGlobalState sym ->
      IO (SymGlobalState sym)
    resolveExterns sym externs gst
      | Just (Some gv) <- Map.lookup (GlobalName "foo") externs
      , Just Refl <- testEquality (globalType gv) IntegerRepr
      = do fooVal <- intLit sym 42
           pure $ insertGlobal gv fooVal gst

      | otherwise
      = assertFailure "Could not find $$foo extern of the appropriate type"
