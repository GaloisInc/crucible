{-
Module           : Main
Description      : Tests
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

For now, this test suite only has \"acceptance tests\", i.e. tests that describe
very high-level behavior.

There are two ways to add such tests:

1. add a C file to test/programs and add assertions about it using 'inFile'
   below, or
2. construct an LLVM module \"by hand\" and use 'inModule'.

The advantages of the first approach are:

* It's usually very concise, making it easy to add additional tests.
* The output is guaranteed to be realistic.

The advantages of the second approach are:

* The tests will run faster (no external process, no filesystem access).
* The tests are more deterministic (same reasons).
* You can abstract over the AST with Haskell functions (like those used in the
  various tests of arithmetic).

The big disadvantages of the second approach, as compared with the first, are:

* It's possible to write an ill-formed/ill-typed AST (though this should be
  caught the first time the test runs).
* There's no guarantee that Clang would ever produce such an AST.
* It can be verbose.

Some tests have a \"Goal\" comment attached to them. In cases where the test is
currently \"unclassified\", the current state of the code isn't wrong per se,
but may be imprecise. If that's not the current state, such a comment indicates
a very real bug.
-}
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
import           Data.Maybe (fromMaybe, isNothing)
import           System.FilePath ((</>))
import           System.IO (IOMode(WriteMode), withFile)

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (NatRepr, knownNat)
import           Data.Parameterized.Some (Some(..))

import           Lang.Crucible.FunctionHandle (newHandleAllocator)

import qualified Crux
import           Crux.LLVM.Compile (genBitCode)
import           Crux.LLVM.Config (clangOpts)

-- Code being tested
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Main (loopOnFunctions, translateFile, translateLLVMModule)
import           UCCrux.LLVM.Errors.Unimplemented (catchUnimplemented)
import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.Classify.Types (partitionUncertainty)
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

findBugs ::
  Maybe L.Module ->
  FilePath ->
  [String] ->
  IO (Map.Map String Result.SomeBugfindingResult)
findBugs llvmModule file fns =
  do
    withFile (testDir </> file <> ".output") WriteMode $ \h ->
      do
        let isRealFile = isNothing llvmModule
        let outCfg = Crux.OutputConfig False h h True
        conf <- Config.ucCruxLLVMConfig
        (appCtx, path, cruxOpts, ucOpts) <-
          Crux.loadOptions outCfg "uc-crux-llvm" "0.1" conf $ \(cruxOpts, ucOpts) ->
            do
              let cruxOpts' = cruxOpts {Crux.inputFiles = [testDir </> file]}
              let ucOpts' = ucOpts {Config.entryPoints = fns}
              (appCtx, cruxOpts'', ucOpts'') <- Config.processUCCruxLLVMOptions (cruxOpts', ucOpts')
              path <-
                if isRealFile
                  then
                    try
                      ( genBitCode
                          cruxOpts''
                          ( (Config.ucLLVMOptions ucOpts')
                              { -- NB(lb): The -fno-wrapv here ensures that
                                -- Clang will emit 'nsw' flags even on platforms
                                -- using nixpkgs, which injects
                                -- -fno-strict-overflow by default.
                                clangOpts = ["-fno-wrapv"]
                              }
                          )
                      )
                      >>= \case
                        Left (exc :: SomeException) ->
                          error ("Trouble when running Clang:" ++ displayException exc)
                        Right path -> pure path
                  else pure "<fake-path>"

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
        Some modCtx <-
          case llvmModule of
            Just lMod -> translateLLVMModule ucOpts halloc path lMod
            Nothing -> translateFile ucOpts halloc path
        loopOnFunctions appCtx modCtx halloc cruxOpts ucOpts

inFile :: FilePath -> [(String, String -> Result.SomeBugfindingResult -> IO ())] -> TT.TestTree
inFile file specs =
  TH.testCase file $
    do
      results <- findBugs Nothing file (map fst specs)
      for_ specs $
        \(fn, spec) ->
          spec fn $ fromMaybe (error ("Couldn't find result for function" ++ fn)) $ Map.lookup fn results

inModule :: FilePath -> L.Module -> [(String, String -> Result.SomeBugfindingResult -> IO ())] -> TT.TestTree
inModule fakePath llvmModule specs =
  TH.testCase fakePath $
    do
      results <- findBugs (Just llvmModule) fakePath (map fst specs)
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
          results <- findBugs Nothing file [fn]
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

inFileTests :: TT.TestTree
inFileTests =
  TT.testGroup "file based tests" $
    map
      (uncurry inFile)
      [ ("assert_false.c", [("assert_false", hasBugs)]),
        ("assert_arg_eq.c", [("assert_arg_eq", hasBugs)]), -- goal: hasFailedAssert
        ("double_free.c", [("double_free", hasBugs)]),
        ("branch.c", [("branch", isSafe)]),
        ("compare_to_null.c", [("compare_to_null", isSafe)]),
        ("opaque_struct.c", [("opaque_struct", isSafe)]),
        ("print.c", [("print", isSafe)]),
        ("read_global.c", [("read_global", isSafe)]),
        ("write_global.c", [("write_global", isSafe)]),
        ("factorial.c", [("factorial", isSafeToBounds)]),
        ("loop_arg_bound.c", [("loop_arg_bound", isSafeToBounds)]),
        ("loop_constant_big_bound_arg_start.c", [("loop_constant_big_bound_arg_start", isSafeToBounds)]),
        ("loop_constant_bound_arg_start.c", [("loop_constant_bound_arg_start", isSafeToBounds)]), -- TODO: Why not just isSafe?
        ("deref_arg.c", [("deref_arg", isSafeWithPreconditions DidntHitBounds)]),
        ("deref_arg_const_index.c", [("deref_arg_const_index", isSafeWithPreconditions DidntHitBounds)]),
        ("deref_struct_field.c", [("deref_struct_field", isSafeWithPreconditions DidntHitBounds)]),
        ("do_free.c", [("do_free", isSafeWithPreconditions DidntHitBounds)]),
        ("linked_list_sum.c", [("linked_list_sum", isSafeWithPreconditions DidHitBounds)]),
        ("memset_const_len.c", [("memset_const_len", isSafeWithPreconditions DidntHitBounds)]),
        ("memset_const_len_arg_byte.c", [("memset_const_len_arg_byte", isSafeWithPreconditions DidntHitBounds)]),
        ("mutually_recursive_linked_list_sum.c", [("mutually_recursive_linked_list_sum", isSafeWithPreconditions DidHitBounds)]),
        ("not_double_free.c", [("not_double_free", isSafeWithPreconditions DidntHitBounds)]),
        ("ptr_as_array.c", [("ptr_as_array", isSafeWithPreconditions DidntHitBounds)]),
        ("sized_array_arg.c", [("sized_array_arg", isSafeWithPreconditions DidntHitBounds)]),
        ("writes_to_arg.c", [("writes_to_arg", isSafeWithPreconditions DidntHitBounds)]),
        ("writes_to_arg_conditional.c", [("writes_to_arg_conditional", isSafeWithPreconditions DidntHitBounds)]),
        ("writes_to_arg_conditional_ptr.c", [("writes_to_arg_conditional_ptr", isSafeWithPreconditions DidntHitBounds)]),
        ("writes_to_arg_field.c", [("writes_to_arg_field", isSafeWithPreconditions DidntHitBounds)]),
        ("writes_to_arg_ptr.c", [("writes_to_arg_ptr", isSafeWithPreconditions DidntHitBounds)]),
        ("do_exit.c", [("do_exit", isUnclassified)]), -- goal: isSafe
        ("do_fork.c", [("do_fork", isUnclassified)]),
        ("do_getchar.c", [("do_getchar", isUnclassified)]), -- goal: isSafe
        ("do_recv.c", [("do_recv", isUnclassified)]),
        ("memset_arg_len.c", [("memset_arg_len", isUnclassified)]), -- goal: isSafeWP
        ("nested_structs.c", [("nested_structs", isUnclassified)]), -- goal: ???
        ("oob_read_heap.c", [("oob_read_heap", isUnclassified)]), -- goal: hasBugs
        ("oob_read_stack.c", [("oob_read_stack", isUnclassified)]), -- goal: hasBugs
        ("uninitialized_stack.c", [("uninitialized_stack", isUnclassified)]), -- goal: hasBugs
        ("write_const_global.c", [("write_const_global", isUnclassified)]), -- goal: hasBugs
        ("use_after_free.c", [("use_after_free", isUnclassified)]), -- goal: hasBugs
        --
        --
        -- TODO(lb): Fix upstream? Missing annotations just seems like a bug.
        ("memcpy_const_len.c", [("memcpy_const_len", hasMissingAnn)]),
        ("deref_arg_arg_index.c", [("deref_arg_arg_index", hasMissingAnn)])
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

i32 :: L.Type
i32 = L.PrimType (L.Integer 32)

float :: L.Type
float = L.PrimType (L.FloatType L.Float)

double :: L.Type
double = L.PrimType (L.FloatType L.Double)

result :: L.Ident -> L.Instr -> L.Stmt
result ident inst = L.Result ident inst []

effect :: L.Instr -> L.Stmt
effect inst = L.Effect inst []

emptyDefine :: L.Define
emptyDefine =
  L.Define
    { L.defName = "<empty>",
      L.defArgs = [],
      L.defVarArgs = False,
      L.defAttrs = [],
      L.defRetType = L.PrimType L.Void,
      L.defLinkage = Nothing,
      L.defSection = Nothing,
      L.defGC = Nothing,
      L.defBody = [],
      L.defMetadata = mempty,
      L.defComdat = Nothing
    }

oneDefine ::
  String ->
  [L.Typed L.Ident] ->
  L.Type ->
  [L.BasicBlock] ->
  L.Module
oneDefine name args ret blocks =
  L.emptyModule
    { L.modSourceName = Just (name ++ ".c"),
      L.modDefines =
        [ emptyDefine
            { L.defName = L.Symbol name,
              L.defArgs = args,
              L.defRetType = ret,
              L.defBody = blocks
            }
        ]
    }

oneArith ::
  String ->
  L.Type ->
  L.Value ->
  L.ArithOp ->
  L.Module
oneArith name ty val op =
  oneDefine
    name
    [L.Typed ty (L.Ident "arg")]
    ty
    [ L.BasicBlock
        (Just "bb")
        [ result
            "retVal"
            (L.Arith op (L.Typed ty (L.ValIdent (L.Ident "arg"))) val),
          effect (L.Ret (L.Typed ty (L.ValIdent (L.Ident "retVal"))))
        ]
    ]

moduleTests :: TT.TestTree
moduleTests =
  TT.testGroup
    "module based tests"
    [ inModule
        "add1.c"
        (oneArith "add1" i32 (L.ValInteger 1) (L.Add False False))
        [("add1", isSafe)],
      inModule
        "add1_nsw.c"
        (oneArith "add1_nsw" i32 (L.ValInteger 1) (L.Add False True))
        [("add1_nsw", isSafeWithPreconditions DidntHitBounds)],
      inModule
        "add1_nuw.c"
        (oneArith "add1_nuw" i32 (L.ValInteger 1) (L.Add True False))
        [("add1_nuw", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add1_float.c"
        (oneArith "add1_float" float (L.ValFloat 1.0) L.FAdd)
        [("add1_float", isSafe)],
      inModule
        "add1_double.c"
        (oneArith "add1_double" double (L.ValDouble 1.0) L.FAdd)
        [("add1_double", isSafe)],
      inModule
        "sub1.c"
        (oneArith "sub1" i32 (L.ValInteger 1) (L.Sub False False))
        [("sub1", isSafe)],
      inModule
        "sub1_nsw.c"
        (oneArith "sub1_nsw" i32 (L.ValInteger 1) (L.Sub False True))
        [("sub1_nsw", isSafeWithPreconditions DidntHitBounds)],
      inModule
        "sub1_nuw.c"
        (oneArith "sub1_nuw" i32 (L.ValInteger 1) (L.Sub True False))
        [("sub1_nuw", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "sub1_float.c"
        (oneArith "sub1_float" float (L.ValFloat 1.0) L.FSub)
        [("sub1_float", isSafe)],
      inModule
        "sub1_double.c"
        (oneArith "sub1_double" double (L.ValDouble 1.0) L.FSub)
        [("sub1_double", isSafe)],
      inModule
        "mul0.c"
        (oneArith "mul0" i32 (L.ValInteger 0) (L.Mul True True))
        [("mul0", isSafe)],
      inModule
        "mul1.c"
        (oneArith "mul1" i32 (L.ValInteger 1) (L.Mul False True))
        [("mul1", isSafe)],
      inModule
        "mul1_nsw.c"
        (oneArith "mul1_nsw" i32 (L.ValInteger 1) (L.Mul False True))
        [("mul1_nsw", isSafe)],
      inModule
        "mul1_nuw.c"
        (oneArith "mul1_nuw" i32 (L.ValInteger 1) (L.Mul True False))
        [("mul1_nuw", isSafe)],
      inModule
        "udiv0.c"
        (oneArith "udiv0" i32 (L.ValInteger 0) (L.UDiv False))
        [("udiv0", isUnclassified)], -- TODO Goal: hasBugs
      inModule
        "udiv1.c"
        (oneArith "udiv1" i32 (L.ValInteger 1) (L.UDiv False))
        [("udiv1", isSafe)],
      inModule
        "udiv1_exact.c"
        (oneArith "udiv1_exact" i32 (L.ValInteger 1) (L.UDiv True))
        [("udiv1_exact", isSafe)],
      inModule
        "udiv2.c"
        (oneArith "udiv2" i32 (L.ValInteger 2) (L.UDiv False))
        [("udiv2", isSafe)],
      inModule
        "udiv2_exact.c"
        (oneArith "udiv2_exact" i32 (L.ValInteger 2) (L.UDiv True))
        [("udiv2_exact", isUnclassified)], -- TODO Goal: isSafeWithPreconditions
      inModule
        "sdiv0.c"
        (oneArith "sdiv0" i32 (L.ValInteger 0) (L.SDiv False))
        [("sdiv0", isUnclassified)], -- TODO Goal: hasBugs
      inModule
        "sdiv1.c"
        (oneArith "sdiv1" i32 (L.ValInteger 1) (L.SDiv False))
        [("sdiv1", isSafe)],
      inModule
        "sdiv1_exact.c"
        (oneArith "sdiv1_exact" i32 (L.ValInteger 1) (L.SDiv True))
        [("sdiv1_exact", isSafe)],
      inModule
        "sdiv2.c"
        (oneArith "sdiv2" i32 (L.ValInteger 2) (L.SDiv False))
        [("sdiv2", isSafe)],
      inModule
        "sdiv2_exact.c"
        (oneArith "sdiv2_exact" i32 (L.ValInteger 2) (L.SDiv True))
        [("sdiv2_exact", isUnclassified)], -- TODO Goal: isSafeWithPreconditions
      inModule
        "urem0.c"
        (oneArith "urem0" i32 (L.ValInteger 0) L.URem)
        [("urem0", isUnclassified)], -- TODO Goal: hasBugs
      inModule
        "urem1.c"
        (oneArith "urem1" i32 (L.ValInteger 1) L.URem)
        [("urem1", isSafe)],
      inModule
        "urem2.c"
        (oneArith "urem2" i32 (L.ValInteger 2) L.URem)
        [("urem2", isSafe)],
      inModule
        "srem0.c"
        (oneArith "srem0" i32 (L.ValInteger 0) L.SRem)
        [("srem0", isUnclassified)], -- TODO Goal: hasBugs
      inModule
        "srem1.c"
        (oneArith "srem1" i32 (L.ValInteger 1) L.SRem)
        [("srem1", isSafe)],
      inModule
        "srem2.c"
        (oneArith "srem2" i32 (L.ValInteger 2) L.SRem)
        [("srem2", isSafe)]
    ]

main :: IO ()
main =
  TT.defaultMain $
    TT.testGroup
      "uc-crux-llvm"
      [ inFileTests,
        moduleTests,
        isUnimplemented "call_function_pointer.c" "call_function_pointer" -- goal: ???
      ]
