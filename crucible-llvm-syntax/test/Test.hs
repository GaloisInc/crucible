{-# LANGUAGE ImplicitParams #-}

module Main where

import Control.Applicative
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.ST

import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(..))
import Data.Text (Text)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.IO

import Lang.Crucible.Syntax.Concrete hiding (SyntaxError)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState (SymGlobalState, insertGlobal)
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Syntax.Atoms (GlobalName(..))
import Lang.Crucible.Syntax.Prog
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.ExprParse
import Lang.Crucible.Syntax.Overrides as SyntaxOvrs
import Lang.Crucible.Types
import Lang.Crucible.CFG.Common (GlobalVar(..))
import Lang.Crucible.CFG.SSAConversion

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden
import Test.Tasty.HUnit
import System.FilePath
import System.Directory

import What4.Config
import What4.FunctionName
import What4.Interface (intLit)
import What4.ProgramLoc
import What4.Solver.Z3 (z3Options)

import Lang.Crucible.LLVM.Syntax (llvmParserHooks)

main :: IO ()
main = do
  parseTests <- findTests "Parse tests" "test-data" testParser
  defaultMain $ testGroup "Tests" [parseTests]

findTests :: String -> FilePath -> (FilePath -> FilePath -> IO ()) -> IO TestTree
findTests groupName testDir testAction =
  do inputs <- findByExtension [".cbl"] testDir
     return $ testGroup groupName
       [ goldenFileTestCase input testAction
       | input <- sort inputs
       ]

goldenFileTestCase :: FilePath -> (FilePath -> FilePath -> IO ()) -> TestTree
goldenFileTestCase input testAction =
  goldenVsFileDiff
   (takeBaseName input) -- test name
   (\x y -> ["diff", "-u", x, y])
   goodFile -- golden file path
   outFile
   (testAction input outFile) -- action whose result is tested
  where
    outFile = replaceExtension input ".out"
    goodFile = replaceExtension input ".out.good"

testParser :: FilePath -> FilePath -> IO ()
testParser inFile outFile =
  do contents <- T.readFile inFile
     let ?parserHooks = llvmParserHooks
     withFile outFile WriteMode $ doParseCheck inFile contents True

testOptions :: [ConfigDesc]
testOptions = z3Options

