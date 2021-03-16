{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Main (main) where

{- ORMOLU_DISABLE -}
import           Control.Exception (SomeException, try, displayException)
import           Data.Foldable (for_)
import           Data.List (intercalate)
import qualified Data.Text as Text
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           System.FilePath ((</>))
import           System.IO (IOMode(WriteMode), withFile)

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (NatRepr, knownNat)
import           Data.Parameterized.Some (Some(..))

import           Lang.Crucible.FunctionHandle (newHandleAllocator)

import qualified Crux
import           Crux.LLVM.Compile (genBitCode)

-- Code being tested
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Main (loopOnFunctions, translate)
import           UCCrux.LLVM.Errors.Unimplemented (catchUnimplemented)
import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.Classify (partitionUncertainty)
import           UCCrux.LLVM.FullType (FullType(..), FullTypeRepr(..))
import           UCCrux.LLVM.Run.Result (DidHitBounds(DidHitBounds, DidntHitBounds))
import qualified UCCrux.LLVM.Run.Result as Result
{- ORMOLU_ENABLE -}

-- Just test that a few things typecheck as expected

exampleHere :: Cursor m ('FTInt 64) ('FTInt 64)
exampleHere = Here (FTIntRepr knownNat)

_exampleArray :: Cursor m ('FTArray 8 ('FTInt 64)) ('FTInt 64)
_exampleArray = Index (knownNat :: NatRepr 7) knownNat exampleHere

_exampleStruct ::
  Cursor
    m
    ('FTStruct ('Ctx.EmptyCtx Ctx.::> 'FTInt 32 Ctx.::> 'FTInt 64))
    ('FTInt 64)
_exampleStruct =
  Field
    (Ctx.extend (Ctx.extend Ctx.empty (FTIntRepr knownNat)) (FTIntRepr knownNat))
    (Ctx.lastIndex Ctx.knownSize)
    exampleHere

testDir :: FilePath
testDir = "test/programs"

findBugs :: FilePath -> [String] -> IO (Map.Map String Result.SomeBugfindingResult)
findBugs file fns =
  do
    withFile (testDir </> file <> ".output") WriteMode $ \h ->
      do
        let outCfg = Crux.OutputConfig False h h True
        conf <- Config.ucCruxLLVMConfig
        (appCtx, path, cruxOpts, ucOpts) <-
          Crux.loadOptions outCfg "uc-crux-llvm" "0.1" conf $ \(cruxOpts, ucOpts) ->
            do
              let cruxOpts' = cruxOpts {Crux.inputFiles = [testDir </> file]}
              let ucOpts' = ucOpts {Config.entryPoints = fns}
              (appCtx, cruxOpts'', ucOpts'') <- Config.processUCCruxLLVMOptions (cruxOpts', ucOpts')
              path <-
                try (genBitCode cruxOpts'' (Config.ucLLVMOptions ucOpts'))
                  >>= \case
                    Left (exc :: SomeException) ->
                      error ("Trouble when running Clang:" ++ displayException exc)
                    Right path -> pure path

              pure (appCtx, path, cruxOpts'', ucOpts'')
        putStrLn
          ( unwords
              [ "Reproduce with:\n",
                "cabal v2-run exe:uc-crux-llvm -- ",
                "--entry-points",
                intercalate " --entry-points " (map show fns),
                testDir </> file
              ]
          )
        let ?outputConfig = outCfg
        halloc <- newHandleAllocator
        Some modCtx <- translate ucOpts halloc path
        loopOnFunctions appCtx modCtx halloc cruxOpts ucOpts

inFile :: FilePath -> [(String, String -> Result.SomeBugfindingResult -> IO ())] -> TT.TestTree
inFile file specs =
  TH.testCase file $
    do
      results <- findBugs file (map fst specs)
      for_ specs $
        \(fn, spec) ->
          spec fn $ fromMaybe (error ("Couldn't find result for function" ++ fn)) $ Map.lookup fn results

hasBugs :: String -> Result.SomeBugfindingResult -> IO ()
hasBugs fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.FoundBugs _bugs -> pure ()
      _ -> TH.assertFailure (unwords ["Expected", fn, "to have bugs"])

isSafe :: String -> Result.SomeBugfindingResult -> IO ()
isSafe fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.AlwaysSafe -> pure ()
      _ ->
        TH.assertFailure
          ( unwords
              [ "Expected",
                fn,
                "to be safe but the result was:\n",
                Text.unpack (Result.printFunctionSummary (Result.summary result))
              ]
          )

isSafeToBounds :: String -> Result.SomeBugfindingResult -> IO ()
isSafeToBounds fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.SafeUpToBounds -> pure ()
      _ ->
        TH.assertFailure
          ( unwords
              [ "Expected",
                fn,
                "to be safe up to recursion/loop bounds but the result was\n",
                Text.unpack (Result.printFunctionSummary (Result.summary result))
              ]
          )

isSafeWithPreconditions :: DidHitBounds -> String -> Result.SomeBugfindingResult -> IO ()
isSafeWithPreconditions hitBounds fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.SafeWithPreconditions didExhaust _preconditions ->
        hitBounds TH.@=? didExhaust
      _ ->
        TH.assertFailure
          ( unwords
              [ "Expected",
                fn,
                "to be safe with preconditions but the result was\n",
                Text.unpack (Result.printFunctionSummary (Result.summary result))
              ]
          )

isUnannotated :: String -> Result.SomeBugfindingResult -> IO ()
isUnannotated fn (Result.SomeBugfindingResult result) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show unclass
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    0 < length missingAnn
      TH.@? unwords
        [ "Expected",
          fn,
          "to be unannotated but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

hasFailedAssert :: String -> Result.SomeBugfindingResult -> IO ()
hasFailedAssert fn (Result.SomeBugfindingResult result) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show unclass
    [] TH.@=? map show missingAnn
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    0 < length failedAssert
      TH.@? unwords
        [ "Expected",
          fn,
          "to have failing assertions but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

isUnclassified :: String -> Result.SomeBugfindingResult -> IO ()
isUnclassified fn (Result.SomeBugfindingResult result) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show missingAnn
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    0 < length unclass
      TH.@? unwords
        [ "Expected",
          fn,
          "to be unclassified but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

hasMissingAnn :: String -> Result.SomeBugfindingResult -> IO ()
hasMissingAnn fn (Result.SomeBugfindingResult result) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unclass
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    0 < length missingAnn
      TH.@? unwords
        [ "Expected",
          fn,
          "to have a missing annotation but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

isUnimplemented :: FilePath -> String -> TT.TestTree
isUnimplemented file fn =
  TH.testCase (fn <> " exercises unimplemented functionality") $
    catchUnimplemented
      ( do
          results <- findBugs file [fn]
          Result.SomeBugfindingResult result <- pure $ fromMaybe (error "No result") (Map.lookup fn results)
          let (_unclass, _missingAnn, _failedAssert, unimpl, _unfixed, _unfixable) =
                partitionUncertainty (Result.uncertainResults result)
          0 < length unimpl
            TH.@? unwords
              [ "Expected",
                fn,
                "to be unimplemented but the result was:\n",
                Text.unpack (Result.printFunctionSummary (Result.summary result))
              ]
      )
      >>= \case
        Left _ -> pure ()
        Right () -> TH.assertFailure (unwords ["Expected", fn, "to be unimplemented"])

tests :: TT.TestTree
tests =
  TT.testGroup
    "bugfinding"
    [ inFile "assert_false.c" [("assert_false", hasBugs)],
      inFile "assert_arg_eq.c" [("assert_arg_eq", hasBugs)], -- goal: hasFailedAssert
      inFile "double_free.c" [("double_free", hasBugs)],
      inFile "add1.c" [("add1", isSafe)],
      inFile "add1_double.c" [("add1_double", isSafe)], -- TODO: correct?
      inFile "add1_float.c" [("add1_float", isSafe)], -- TODO: correct?
      inFile "branch.c" [("branch", isSafe)],
      inFile "compare_to_null.c" [("compare_to_null", isSafe)],
      inFile "opaque_struct.c" [("opaque_struct", isSafe)],
      inFile "print.c" [("print", isSafe)],
      inFile "read_global.c" [("read_global", isSafe)],
      inFile "write_global.c" [("write_global", isSafe)],
      inFile "factorial.c" [("factorial", isSafeToBounds)],
      inFile "loop_arg_bound.c" [("loop_arg_bound", isSafeToBounds)],
      inFile "loop_constant_big_bound_arg_start.c" [("loop_constant_big_bound_arg_start", isSafeToBounds)],
      inFile "loop_constant_bound_arg_start.c" [("loop_constant_bound_arg_start", isSafeToBounds)], -- TODO: Why not just isSafe?
      inFile "deref_arg.c" [("deref_arg", isSafeWithPreconditions DidntHitBounds)],
      inFile "deref_arg_const_index.c" [("deref_arg_const_index", isSafeWithPreconditions DidntHitBounds)],
      inFile "deref_struct_field.c" [("deref_struct_field", isSafeWithPreconditions DidntHitBounds)],
      inFile "do_free.c" [("do_free", isSafeWithPreconditions DidntHitBounds)],
      inFile "linked_list_sum.c" [("linked_list_sum", isSafeWithPreconditions DidHitBounds)],
      inFile "memset_const_len.c" [("memset_const_len", isSafeWithPreconditions DidntHitBounds)],
      inFile "memset_const_len_arg_byte.c" [("memset_const_len_arg_byte", isSafeWithPreconditions DidntHitBounds)],
      inFile "mutually_recursive_linked_list_sum.c" [("mutually_recursive_linked_list_sum", isSafeWithPreconditions DidHitBounds)],
      inFile "not_double_free.c" [("not_double_free", isSafeWithPreconditions DidntHitBounds)],
      inFile "ptr_as_array.c" [("ptr_as_array", isSafeWithPreconditions DidntHitBounds)],
      inFile "sized_array_arg.c" [("sized_array_arg", isSafeWithPreconditions DidntHitBounds)],
      inFile "writes_to_arg.c" [("writes_to_arg", isSafeWithPreconditions DidntHitBounds)],
      inFile "writes_to_arg_conditional.c" [("writes_to_arg_conditional", isSafeWithPreconditions DidntHitBounds)],
      inFile "writes_to_arg_conditional_ptr.c" [("writes_to_arg_conditional_ptr", isSafeWithPreconditions DidntHitBounds)],
      inFile "writes_to_arg_field.c" [("writes_to_arg_field", isSafeWithPreconditions DidntHitBounds)],
      inFile "writes_to_arg_ptr.c" [("writes_to_arg_ptr", isSafeWithPreconditions DidntHitBounds)],
      inFile "do_exit.c" [("do_exit", isUnclassified)], -- goal: isSafe
      inFile "do_fork.c" [("do_fork", isUnclassified)],
      inFile "do_getchar.c" [("do_getchar", isUnclassified)], -- goal: isSafe
      inFile "do_recv.c" [("do_recv", isUnclassified)],
      -- The following test requires relational preconditions:
      inFile "memset_arg_len.c" [("memset_arg_len", isUnclassified)], -- goal: isSafeWP
      inFile "nested_structs.c" [("nested_structs", isUnclassified)], -- goal: ???
      inFile "oob_read_heap.c" [("oob_read_heap", isUnclassified)], -- goal: notSafe
      inFile "oob_read_stack.c" [("oob_read_stack", isUnclassified)], -- goal: notSafe
      inFile "uninitialized_stack.c" [("uninitialized_stack", isUnclassified)], -- goal: notSafe
      isUnimplemented
        "call_function_pointer.c"
        "call_function_pointer", -- goal: ???
        --
        --
        -- TODO(lb): Fix upstream? Missing annotations just seems like a bug.
      inFile "memcpy_const_len.c" [("memcpy_const_len", hasMissingAnn)],
      inFile "deref_arg_arg_index.c" [("deref_arg_arg_index", hasMissingAnn)]
      -- SQLite
      -- This is slow, and WIP
      -- inFile
      --   "sqlite-3.32.1/sqlite3.c"
      --   [ ("appendText", isSafeWithPreconditions False),
      --     ("sqlite3_filename_database", isUnclassified)
      --   ]

      -- TODO: https://github.com/GaloisInc/crucible/issues/651
      -- , isSafeWithPreconditions "do_strlen.c" "do_strlen" False

      -- TODO: Not sure if Crux can do C++?
      -- , isSafe "cxxbasic.cpp" "cxxbasic"
    ]

main :: IO ()
main = TT.defaultMain $ TT.testGroup "uc-crux-llvm" [tests]
