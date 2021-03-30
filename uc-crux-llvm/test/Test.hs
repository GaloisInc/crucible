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
import qualified Data.Text as Text
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, isNothing)
import qualified Data.Set as Set
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
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName(..))
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName(..))
import           UCCrux.LLVM.Run.Result (DidHitBounds(DidHitBounds, DidntHitBounds))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness(..))
{- ORMOLU_ENABLE -}

-- Just test that a few things typecheck as expected

exampleHere :: Cursor m ('FTInt 64) ('FTInt 64)
exampleHere = Here (FTIntRepr knownNat)

_exampleArray :: Cursor m ('FTArray ('Just 8) ('FTInt 64)) ('FTInt 64)
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

-- | TODO: Take a list of TruePositiveTag, verify that those are the bugs.
hasBugs :: String -> Result.SomeBugfindingResult -> IO ()
hasBugs fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.FoundBugs _bugs -> pure ()
      _ -> TH.assertFailure (unwords ["Expected", fn, "to have bugs"])

isSafe :: Unsoundness -> String -> Result.SomeBugfindingResult -> IO ()
isSafe unsoundness fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.AlwaysSafe u -> unsoundness TH.@=? u
      _ ->
        TH.assertFailure
          ( unwords
              [ "Expected",
                fn,
                "to be safe but the result was:\n",
                Text.unpack (Result.printFunctionSummary (Result.summary result))
              ]
          )

isSafeToBounds :: Unsoundness -> String -> Result.SomeBugfindingResult -> IO ()
isSafeToBounds unsoundness fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.SafeUpToBounds u -> unsoundness TH.@=? u
      _ ->
        TH.assertFailure
          ( unwords
              [ "Expected",
                fn,
                "to be safe up to recursion/loop bounds but the result was\n",
                Text.unpack (Result.printFunctionSummary (Result.summary result))
              ]
          )

-- | TODO: Take a list of MissingPreconditionTag, check that they match.
isSafeWithPreconditions :: Unsoundness -> DidHitBounds -> String -> Result.SomeBugfindingResult -> IO ()
isSafeWithPreconditions unsoundness hitBounds fn (Result.SomeBugfindingResult result) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.SafeWithPreconditions didExhaust u _preconditions ->
        do
          unsoundness TH.@=? u
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

_isUnannotated :: String -> Result.SomeBugfindingResult -> IO ()
_isUnannotated fn (Result.SomeBugfindingResult result) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable, timeouts) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show unclass
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    [] TH.@=? map show timeouts
    0 < length missingAnn
      TH.@? unwords
        [ "Expected",
          fn,
          "to be unannotated but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

_hasFailedAssert :: String -> Result.SomeBugfindingResult -> IO ()
_hasFailedAssert fn (Result.SomeBugfindingResult result) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable, timeouts) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show unclass
    [] TH.@=? map show missingAnn
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    [] TH.@=? map show timeouts
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
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable, timeouts) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show missingAnn
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    [] TH.@=? map show timeouts
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
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable, timeouts) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unclass
    [] TH.@=? map show unimpl
    [] TH.@=? map show unfixed
    [] TH.@=? map show unfixable
    [] TH.@=? map show timeouts
    0 < length missingAnn
      TH.@? unwords
        [ "Expected",
          fn,
          "to have a missing annotation but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

-- | TODO: Take an unimplemented feature tag, check that it matches
isUnimplemented :: FilePath -> String -> TT.TestTree
isUnimplemented file fn =
  TH.testCase (fn <> " exercises unimplemented functionality") $
    catchUnimplemented
      ( do
          results <- findBugs Nothing file [fn]
          Result.SomeBugfindingResult result <- pure $ fromMaybe (error "No result") (Map.lookup fn results)
          let (_unclass, _missingAnn, _failedAssert, unimpl, _unfixed, _unfixable, _timeouts) =
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

skipOverride :: String -> Unsoundness
skipOverride name =
  Unsoundness Set.empty (Set.singleton (SkipOverrideName (Text.pack name)))

unsoundOverride :: String -> Unsoundness
unsoundOverride name =
  Unsoundness (Set.singleton (UnsoundOverrideName (Text.pack name))) Set.empty

inFileTests :: TT.TestTree
inFileTests =
  TT.testGroup "file based tests" $
    map
      (uncurry inFile)
      [ ("assert_false.c", [("assert_false", hasBugs)]),
        ("assert_arg_eq.c", [("assert_arg_eq", hasBugs)]), -- goal: hasFailedAssert
        ("double_free.c", [("double_free", hasBugs)]),
        ("uninitialized_heap.c", [("uninitialized_heap", hasBugs)]),
        ("uninitialized_stack.c", [("uninitialized_stack", hasBugs)]),
        ("write_to_null.c", [("write_to_null", hasBugs)]),
        ("branch.c", [("branch", isSafe mempty)]),
        ("compare_to_null.c", [("compare_to_null", isSafe mempty)]),
        ("extern_void_function.c", [("extern_void_function", isSafe (skipOverride "do_stuff"))]),
        -- This override needs refinement; the following should be safe with the
        -- precondition that the argument pointer is valid.
        ("getenv_arg.c", [("getenv_arg", isSafe (unsoundOverride "getenv"))]),
        ("getenv_const.c", [("getenv_const", isSafe (unsoundOverride "getenv"))]),
        ("gethostname_const_len.c", [("gethostname_const_len", isSafe (unsoundOverride "gethostname"))]),
        ("id_function_pointer.c", [("id_function_pointer", isSafe mempty)]),
        ("opaque_struct.c", [("opaque_struct", isSafe mempty)]),
        ("print.c", [("print", isSafe mempty)]),
        ("read_global.c", [("read_global", isSafe mempty)]),
        ("write_global.c", [("write_global", isSafe mempty)]),
        ("factorial.c", [("factorial", isSafeToBounds mempty)]),
        ("loop_arg_bound.c", [("loop_arg_bound", isSafeToBounds mempty)]),
        ("loop_constant_big_bound_arg_start.c", [("loop_constant_big_bound_arg_start", isSafeToBounds mempty)]),
        ("loop_constant_bound_arg_start.c", [("loop_constant_bound_arg_start", isSafeToBounds mempty)]), -- TODO: Why not just isSafe?
        ("deref_arg.c", [("deref_arg", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("deref_arg_const_index.c", [("deref_arg_const_index", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("deref_struct_field.c", [("deref_struct_field", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("do_free.c", [("do_free", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("free_dict.c", [("free_dict", isSafeWithPreconditions mempty DidHitBounds)]),
        ("free_dict_kv.c", [("free_dict_kv", isSafeWithPreconditions mempty DidHitBounds)]),
        ("free_linked_list.c", [("free_linked_list", isSafeWithPreconditions mempty DidHitBounds)]),
        ("gethostname_arg_ptr.c", [("gethostname_arg_ptr", isSafeWithPreconditions (unsoundOverride "gethostname") DidntHitBounds)]),
        ("linked_list_sum.c", [("linked_list_sum", isSafeWithPreconditions mempty DidHitBounds)]),
        ("lots_of_loops.c", [("lots_of_loops", isSafeWithPreconditions mempty DidHitBounds)]),
        ("memset_const_len.c", [("memset_const_len", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("memset_const_len_arg_byte.c", [("memset_const_len_arg_byte", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("mutually_recursive_linked_list_sum.c", [("mutually_recursive_linked_list_sum", isSafeWithPreconditions mempty DidHitBounds)]),
        ("not_double_free.c", [("not_double_free", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("ptr_as_array.c", [("ptr_as_array", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("sized_array_arg.c", [("sized_array_arg", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("struct_with_array.c", [("struct_with_array", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("writes_to_arg.c", [("writes_to_arg", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("writes_to_arg_conditional.c", [("writes_to_arg_conditional", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("writes_to_arg_conditional_ptr.c", [("writes_to_arg_conditional_ptr", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("writes_to_arg_field.c", [("writes_to_arg_field", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("writes_to_arg_ptr.c", [("writes_to_arg_ptr", isSafeWithPreconditions mempty DidntHitBounds)]),
        -- This one is interesting... The deduced precondition is a little off,
        -- in that it "should" require the array *in* the struct to have a
        -- nonzero size, but it actually requires the input pointer to point to
        -- an *array of structs*.
        ("unsized_array.c", [("unsized_array", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("deref_func_ptr.c", [("deref_func_ptr", isUnclassified)]), -- goal: hasBugs
        ("do_getchar.c", [("do_getchar", isUnclassified)]), -- goal: isSafe
        ("free_with_offset.c", [("free_with_offset", isUnclassified)]), -- goal: hasBugs
        ("memset_arg_len.c", [("memset_arg_len", isUnclassified)]), -- goal: isSafeWP
        ("memset_func_ptr.c", [("memset_func_ptr", isUnclassified)]), -- goal: hasBugs
        ("nested_structs.c", [("nested_structs", isUnclassified)]), -- goal: ???
        ("oob_read_heap.c", [("oob_read_heap", isUnclassified)]), -- goal: hasBugs
        ("oob_read_stack.c", [("oob_read_stack", isUnclassified)]), -- goal: hasBugs
        ("signed_add_wrap_concrete.c", [("signed_add_wrap_concrete", isUnclassified)]), -- goal: hasBugs
        ("signed_mul_wrap_concrete.c", [("signed_mul_wrap_concrete", isUnclassified)]), -- goal: hasBugs
        ("signed_sub_wrap_concrete.c", [("signed_sub_wrap_concrete", isUnclassified)]), -- goal: hasBugs
        ("write_const_global.c", [("write_const_global", isUnclassified)]), -- goal: hasBugs
        ("use_after_free.c", [("use_after_free", isUnclassified)]), -- goal: hasBugs
        --
        --
        -- TODO(lb): Fix upstream? Missing annotations just seems like a bug.
        ("cast_void_pointer.c", [("cast_void_pointer", hasMissingAnn)]),
        ("compare_ptr_to_int.c", [("compare_ptr_to_int", hasMissingAnn)]), -- goal: hasBugs
        ("compare_ptrs_different_heap_allocs.c", [("compare_ptrs_different_heap_allocs", hasMissingAnn)]), -- goal: hasBugs
        ("compare_ptrs_different_stack_allocs.c", [("compare_ptrs_different_stack_allocs", hasMissingAnn)]), -- goal: hasBugs
        ("memcpy_const_len.c", [("memcpy_const_len", hasMissingAnn)]),
        ("deref_arg_arg_index.c", [("deref_arg_arg_index", hasMissingAnn)]),
        -- This one could use an override. Currently fails because it's
        -- skipped, and so unreachable code gets reached.
        ("do_exit.c", [("do_exit", hasMissingAnn)]) -- goal: isSafe
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

result' :: L.Ident -> L.Instr -> L.Stmt
result' ident inst = L.Result ident inst []

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

-- | A module with one function of one argument that applies an arithmetic
-- operation to a constant and its argument and returns the value.
--
-- This version has the argument "on the left".
oneArithLeft ::
  String ->
  L.Type ->
  L.Value ->
  L.ArithOp ->
  L.Module
oneArithLeft name ty val op =
  oneDefine
    name
    [L.Typed ty (L.Ident "arg")]
    ty
    [ L.BasicBlock
        (Just "bb")
        [ result'
            "retVal"
            (L.Arith op (L.Typed ty (L.ValIdent (L.Ident "arg"))) val),
          effect (L.Ret (L.Typed ty (L.ValIdent (L.Ident "retVal"))))
        ]
    ]

-- | A module with one function of one argument that applies an arithmetic
-- operation to a constant and its argument and returns the value.
--
-- This version has the argument "on the right".
oneArithRight ::
  String ->
  L.Type ->
  L.Value ->
  L.ArithOp ->
  L.Module
oneArithRight name ty val op =
  oneDefine
    name
    [L.Typed ty (L.Ident "arg")]
    ty
    [ L.BasicBlock
        (Just "bb")
        [ result'
            "retVal"
            (L.Arith op (L.Typed ty val) (L.ValIdent (L.Ident "arg"))),
          effect (L.Ret (L.Typed ty (L.ValIdent (L.Ident "retVal"))))
        ]
    ]

moduleTests :: TT.TestTree
moduleTests =
  TT.testGroup
    "module based tests"
    -- A lot of these are tests of various arithmetic operations. The conceptual
    -- "matrix"/cross-product considered is roughly as follows:
    --
    -- For each operation,
    --
    -- - Some combinations of "flags" (nsw, nuw, exact, etc.)
    -- - The four essential common values: -2, -1, 0, 1, 2 (with -2 omitted for
    --   unsigned operations) (this list covers identity elements and
    --   non-identity elements for most operations)
    -- - Having the symbolic and concrete values on the "left" and the "right", e.g.
    --   "symbolic - concrete" *and* "concrete - symbolic".
    --
    -- Several cases aren't considered, it would be nice to auto-generate these...
    --
    -- For the cases of srem_neg1, sdiv_neg1, etc. see the following explanation
    -- from the LLVM Language Reference:
    --
    --   Overflow also leads to undefined behavior; this is a rare case, but can
    --   occur, for example, by taking the remainder of a 32-bit division of
    --   -2147483648 by -1.
    --
    -- Lest this list appear gratuitously long, it first appeared with fewer
    -- cases and missed a very real bug.
    [ inModule
        "add1_left.c"
        (oneArithLeft "add1_left" i32 (L.ValInteger 1) (L.Add False False))
        [("add1_left", isSafe mempty)],
      inModule
        "add1_nsw_left.c"
        (oneArithLeft "add1_nsw_left" i32 (L.ValInteger 1) (L.Add False True))
        [("add1_nsw_left", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "add1_nuw_left.c"
        (oneArithLeft "add1_nuw_left" i32 (L.ValInteger 1) (L.Add True False))
        [("add1_nuw_left", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add_neg1_left.c"
        (oneArithLeft "add_neg1_left" i32 (L.ValInteger (-1)) (L.Add False False))
        [("add_neg1_left", isSafe mempty)],
      inModule
        "add_neg1_nsw_left.c"
        (oneArithLeft "add_neg1_nsw_left" i32 (L.ValInteger (-1)) (L.Add False True))
        [("add_neg1_nsw_left", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "add_neg1_nuw_left.c"
        (oneArithLeft "add_neg1_nuw_left" i32 (L.ValInteger (-1)) (L.Add True False))
        [("add_neg1_nuw_left", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add1_float_left.c"
        (oneArithLeft "add1_float_left" float (L.ValFloat 1.0) L.FAdd)
        [("add1_float_left", isSafe mempty)],
      inModule
        "add_neg1_float_left.c"
        (oneArithLeft "add_neg1_float_left" float (L.ValFloat (-1.0)) L.FAdd)
        [("add_neg1_float_left", isSafe mempty)],
      inModule
        "add1_double_left.c"
        (oneArithLeft "add1_double_left" double (L.ValDouble 1.0) L.FAdd)
        [("add1_double_left", isSafe mempty)],
      inModule
        "add_neg1_double_left.c"
        (oneArithLeft "add_neg1_double_left" double (L.ValDouble (-1.0)) L.FAdd)
        [("add_neg1_double_left", isSafe mempty)],
      inModule
        "sub1_left.c"
        (oneArithLeft "sub1_left" i32 (L.ValInteger 1) (L.Sub False False))
        [("sub1_left", isSafe mempty)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub1_nsw_left.c"
        (oneArithLeft "sub1_nsw_left" i32 (L.ValInteger 1) (L.Sub False True))
        [("sub1_nsw_left", isUnclassified)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub1_nuw_left.c"
        (oneArithLeft "sub1_nuw_left" i32 (L.ValInteger 1) (L.Sub True False))
        [("sub1_nuw_left", isUnclassified)],
      inModule
        "sub_neg1_left.c"
        (oneArithLeft "sub_neg1_left" i32 (L.ValInteger (-1)) (L.Sub False False))
        [("sub_neg1_left", isSafe mempty)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub_neg1_nsw_left.c"
        (oneArithLeft "sub_neg1_nsw_left" i32 (L.ValInteger (-1)) (L.Sub False True))
        [("sub_neg1_nsw_left", isUnclassified)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub_neg1_nuw_left.c"
        (oneArithLeft "sub_neg1_nuw_left" i32 (L.ValInteger (-1)) (L.Sub True False))
        [("sub_neg1_nuw_left", isUnclassified)],
      inModule
        "sub1_float_left.c"
        (oneArithLeft "sub1_float_left" float (L.ValFloat 1.0) L.FSub)
        [("sub1_float_left", isSafe mempty)],
      inModule
        "sub_neg1_float_left.c"
        (oneArithLeft "sub_neg1_float_left" float (L.ValFloat (-1.0)) L.FSub)
        [("sub_neg1_float_left", isSafe mempty)],
      inModule
        "sub1_double_left.c"
        (oneArithLeft "sub1_double_left" double (L.ValDouble 1.0) L.FSub)
        [("sub1_double_left", isSafe mempty)],
      inModule
        "sub_neg1_double_left.c"
        (oneArithLeft "sub_neg1_double_left" double (L.ValDouble (-1.0)) L.FSub)
        [("sub_neg1_double_left", isSafe mempty)],
      inModule
        "mul0_left.c"
        (oneArithLeft "mul0_left" i32 (L.ValInteger 0) (L.Mul True True))
        [("mul0_left", isSafe mempty)],
      inModule
        "mul1_left.c"
        (oneArithLeft "mul1_left" i32 (L.ValInteger 1) (L.Mul False False))
        [("mul1_left", isSafe mempty)],
      inModule
        "mul1_nsw_left.c"
        (oneArithLeft "mul1_nsw_left" i32 (L.ValInteger 1) (L.Mul False True))
        [("mul1_nsw_left", isSafe mempty)],
      inModule
        "mul1_nuw_left.c"
        (oneArithLeft "mul1_nuw_left" i32 (L.ValInteger 1) (L.Mul True False))
        [("mul1_nuw_left", isSafe mempty)],
      inModule
        "mul_neg1_left.c"
        (oneArithLeft "mul_neg1_left" i32 (L.ValInteger (-1)) (L.Mul False False))
        [("mul_neg1_left", isSafe mempty)],
      inModule
        "mul_neg1_nsw_left.c"
        (oneArithLeft "mul_neg1_nsw_left" i32 (L.ValInteger (-1)) (L.Mul False True))
        [("mul_neg1_nsw_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "mul_neg1_nuw_left.c"
        (oneArithLeft "mul_neg1_nuw_left" i32 (L.ValInteger (-1)) (L.Mul True False))
        [("mul_neg1_nuw_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv0_left.c"
        (oneArithLeft "udiv0_left" i32 (L.ValInteger 0) (L.UDiv False))
        [("udiv0_left", hasBugs)],
      inModule
        "udiv1_left.c"
        (oneArithLeft "udiv1_left" i32 (L.ValInteger 1) (L.UDiv False))
        [("udiv1_left", isSafe mempty)],
      inModule
        "udiv1_exact_left.c"
        (oneArithLeft "udiv1_exact_left" i32 (L.ValInteger 1) (L.UDiv True))
        [("udiv1_exact_left", isSafe mempty)],
      inModule
        "udiv2_left.c"
        (oneArithLeft "udiv2_left" i32 (L.ValInteger 2) (L.UDiv False))
        [("udiv2_left", isSafe mempty)],
      inModule
        "udiv2_exact_left.c"
        (oneArithLeft "udiv2_exact_left" i32 (L.ValInteger 2) (L.UDiv True))
        [("udiv2_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv_neg1_left.c"
        (oneArithLeft "udiv_neg1_left" i32 (L.ValInteger (-1)) (L.UDiv False))
        [("udiv_neg1_left", isSafe mempty)],
      inModule
        "udiv_neg1_exact_left.c"
        (oneArithLeft "udiv_neg1_exact_left" i32 (L.ValInteger (-1)) (L.UDiv True))
        [("udiv_neg1_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv0_left.c"
        (oneArithLeft "sdiv0_left" i32 (L.ValInteger 0) (L.SDiv False))
        [("sdiv0_left", hasBugs)],
      inModule
        "sdiv1_left.c"
        (oneArithLeft "sdiv1_left" i32 (L.ValInteger 1) (L.SDiv False))
        [("sdiv1_left", isSafe mempty)],
      inModule
        "sdiv1_exact_left.c"
        (oneArithLeft "sdiv1_exact_left" i32 (L.ValInteger 1) (L.SDiv True))
        [("sdiv1_exact_left", isSafe mempty)],
      inModule
        "sdiv_neg1_left.c"
        (oneArithLeft "sdiv_neg1_left" i32 (L.ValInteger (-1)) (L.SDiv False))
        [("sdiv_neg1_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg1_exact_left.c"
        (oneArithLeft "sdiv_neg1_exact_left" i32 (L.ValInteger (-1)) (L.SDiv True))
        [("sdiv_neg1_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv2_left.c"
        (oneArithLeft "sdiv2_left" i32 (L.ValInteger 2) (L.SDiv False))
        [("sdiv2_left", isSafe mempty)],
      inModule
        "sdiv2_exact_left.c"
        (oneArithLeft "sdiv2_exact_left" i32 (L.ValInteger 2) (L.SDiv True))
        [("sdiv2_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg2_left.c"
        (oneArithLeft "sdiv_neg2_left" i32 (L.ValInteger (-2)) (L.SDiv False))
        [("sdiv_neg2_left", isSafe mempty)],
      inModule
        "sdiv_neg2_exact_left.c"
        (oneArithLeft "sdiv_neg2_exact_left" i32 (L.ValInteger (-2)) (L.SDiv True))
        [("sdiv_neg2_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "urem0_left.c"
        (oneArithLeft "urem0_left" i32 (L.ValInteger 0) L.URem)
        [("urem0_left", hasBugs)],
      inModule
        "urem1_left.c"
        (oneArithLeft "urem1_left" i32 (L.ValInteger 1) L.URem)
        [("urem1_left", isSafe mempty)],
      inModule
        "urem_neg1_left.c"
        (oneArithLeft "urem_neg1_left" i32 (L.ValInteger (-1)) L.URem)
        [("urem_neg1_left", isSafe mempty)],
      inModule
        "urem2_left.c"
        (oneArithLeft "urem2_left" i32 (L.ValInteger 2) L.URem)
        [("urem2_left", isSafe mempty)],
      inModule
        "srem0_left.c"
        (oneArithLeft "srem0_left" i32 (L.ValInteger 0) L.SRem)
        [("srem0_left", hasBugs)],
      inModule
        "srem1_left.c"
        (oneArithLeft "srem1_left" i32 (L.ValInteger 1) L.SRem)
        [("srem1_left", isSafe mempty)],
      inModule
        "srem_neg1_left.c"
        (oneArithLeft "srem_neg1_left" i32 (L.ValInteger (-1)) L.SRem)
        [("srem_neg1_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "srem2_left.c"
        (oneArithLeft "srem2_left" i32 (L.ValInteger 2) L.SRem)
        [("srem2_left", isSafe mempty)],
      inModule
        "srem_neg2_left.c"
        (oneArithLeft "srem_neg2_left" i32 (L.ValInteger (-2)) L.SRem)
        [("srem_neg2_left", isSafe mempty)],
      -- --------------------------------------------------- On the right
      inModule
        "add1_right.c"
        (oneArithRight "add1_right" i32 (L.ValInteger 1) (L.Add False False))
        [("add1_right", isSafe mempty)],
      inModule
        "add1_nsw_right.c"
        (oneArithRight "add1_nsw_right" i32 (L.ValInteger 1) (L.Add False True))
        [("add1_nsw_right", isSafeWithPreconditions mempty DidntHitBounds)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "add1_nuw_right.c"
        (oneArithRight "add1_nuw_right" i32 (L.ValInteger 1) (L.Add True False))
        [("add1_nuw_right", isUnclassified)],
      inModule
        "add_neg1_right.c"
        (oneArithRight "add_neg1_right" i32 (L.ValInteger (-1)) (L.Add False False))
        [("add_neg1_right", isSafe mempty)],
      inModule
        "add_neg1_nsw_right.c"
        (oneArithRight "add_neg1_nsw_right" i32 (L.ValInteger (-1)) (L.Add False True))
        [("add_neg1_nsw_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "add_neg1_nuw_right.c"
        (oneArithRight "add_neg1_nuw_right" i32 (L.ValInteger (-1)) (L.Add True False))
        [("add_neg1_nuw_right", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add1_float_right.c"
        (oneArithRight "add1_float_right" float (L.ValFloat 1.0) L.FAdd)
        [("add1_float_right", isSafe mempty)],
      inModule
        "add_neg1_float_right.c"
        (oneArithRight "add_neg1_float_right" float (L.ValFloat (-1.0)) L.FAdd)
        [("add_neg1_float_right", isSafe mempty)],
      inModule
        "add1_double_right.c"
        (oneArithRight "add1_double_right" double (L.ValDouble 1.0) L.FAdd)
        [("add1_double_right", isSafe mempty)],
      inModule
        "add_neg1_double_right.c"
        (oneArithRight "add_neg1_double_right" double (L.ValDouble (-1.0)) L.FAdd)
        [("add_neg1_double_right", isSafe mempty)],
      inModule
        "sub1_right.c"
        (oneArithRight "sub1_right" i32 (L.ValInteger 1) (L.Sub False False))
        [("sub1_right", isSafe mempty)],
      inModule
        "sub1_nsw_right.c"
        (oneArithRight "sub1_nsw_right" i32 (L.ValInteger 1) (L.Sub False True))
        [("sub1_nsw_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sub1_nuw_right.c"
        (oneArithRight "sub1_nuw_right" i32 (L.ValInteger 1) (L.Sub True False))
        [("sub1_nuw_right", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "sub_neg1_right.c"
        (oneArithRight "sub_neg1_right" i32 (L.ValInteger (-1)) (L.Sub False False))
        [("sub_neg1_right", isSafe mempty)],
      inModule
        "sub_neg1_nsw_right.c"
        (oneArithRight "sub_neg1_nsw_right" i32 (L.ValInteger (-1)) (L.Sub False True))
        [("sub_neg1_nsw_right", isSafe mempty)], -- TODO Is this right?
      inModule
        "sub_neg1_nuw_right.c"
        (oneArithRight "sub_neg1_nuw_right" i32 (L.ValInteger (-1)) (L.Sub True False))
        [("sub_neg1_nuw_right", isSafe mempty)],
      inModule
        "sub1_float_right.c"
        (oneArithRight "sub1_float_right" float (L.ValFloat 1.0) L.FSub)
        [("sub1_float_right", isSafe mempty)],
      inModule
        "sub_neg1_float_right.c"
        (oneArithRight "sub_neg1_float_right" float (L.ValFloat (-1.0)) L.FSub)
        [("sub_neg1_float_right", isSafe mempty)],
      inModule
        "sub1_double_right.c"
        (oneArithRight "sub1_double_right" double (L.ValDouble 1.0) L.FSub)
        [("sub1_double_right", isSafe mempty)],
      inModule
        "sub_neg1_double_right.c"
        (oneArithRight "sub_neg1_double_right" double (L.ValDouble (-1.0)) L.FSub)
        [("sub_neg1_double_right", isSafe mempty)],
      inModule
        "mul0_right.c"
        (oneArithRight "mul0_right" i32 (L.ValInteger 0) (L.Mul True True))
        [("mul0_right", isSafe mempty)],
      inModule
        "mul1_right.c"
        (oneArithRight "mul1_right" i32 (L.ValInteger 1) (L.Mul False False))
        [("mul1_right", isSafe mempty)],
      inModule
        "mul1_nsw_right.c"
        (oneArithRight "mul1_nsw_right" i32 (L.ValInteger 1) (L.Mul False True))
        [("mul1_nsw_right", isSafe mempty)],
      inModule
        "mul1_nuw_right.c"
        (oneArithRight "mul1_nuw_right" i32 (L.ValInteger 1) (L.Mul True False))
        [("mul1_nuw_right", isSafe mempty)],
      inModule
        "mul_neg1_right.c"
        (oneArithRight "mul_neg1_right" i32 (L.ValInteger (-1)) (L.Mul False False))
        [("mul_neg1_right", isSafe mempty)],
      inModule
        "mul_neg1_nsw_right.c"
        (oneArithRight "mul_neg1_nsw_right" i32 (L.ValInteger (-1)) (L.Mul False True))
        [("mul_neg1_nsw_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "mul_neg1_nuw_right.c"
        (oneArithRight "mul_neg1_nuw_right" i32 (L.ValInteger (-1)) (L.Mul True False))
        [("mul_neg1_nuw_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv0_right.c"
        (oneArithRight "udiv0_right" i32 (L.ValInteger 0) (L.UDiv False))
        [("udiv0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv1_right.c"
        (oneArithRight "udiv1_right" i32 (L.ValInteger 1) (L.UDiv False))
        [("udiv1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv1_exact_right.c"
        (oneArithRight "udiv1_exact_right" i32 (L.ValInteger 1) (L.UDiv True))
        [("udiv1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv2_right.c"
        (oneArithRight "udiv2_right" i32 (L.ValInteger 2) (L.UDiv False))
        [("udiv2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv2_exact_right.c"
        (oneArithRight "udiv2_exact_right" i32 (L.ValInteger 2) (L.UDiv True))
        [("udiv2_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv_neg1_right.c"
        (oneArithRight "udiv_neg1_right" i32 (L.ValInteger (-1)) (L.UDiv False))
        [("udiv_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv_neg1_exact_right.c"
        (oneArithRight "udiv_neg1_exact_right" i32 (L.ValInteger (-1)) (L.UDiv True))
        [("udiv_neg1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv0_right.c"
        (oneArithRight "sdiv0_right" i32 (L.ValInteger 0) (L.SDiv False))
        [("sdiv0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv1_right.c"
        (oneArithRight "sdiv1_right" i32 (L.ValInteger 1) (L.SDiv False))
        [("sdiv1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv1_exact_right.c"
        (oneArithRight "sdiv1_exact_right" i32 (L.ValInteger 1) (L.SDiv True))
        [("sdiv1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg1_right.c"
        (oneArithRight "sdiv_neg1_right" i32 (L.ValInteger (-1)) (L.SDiv False))
        [("sdiv_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv_neg1_exact_right.c"
        (oneArithRight "sdiv_neg1_exact_right" i32 (L.ValInteger (-1)) (L.SDiv True))
        [("sdiv_neg1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv2_right.c"
        (oneArithRight "sdiv2_right" i32 (L.ValInteger 2) (L.SDiv False))
        [("sdiv2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv2_exact_right.c"
        (oneArithRight "sdiv2_exact_right" i32 (L.ValInteger 2) (L.SDiv True))
        [("sdiv2_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg2_right.c"
        (oneArithRight "sdiv_neg2_right" i32 (L.ValInteger (-2)) (L.SDiv False))
        [("sdiv_neg2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv_neg2_exact_right.c"
        (oneArithRight "sdiv_neg2_exact_right" i32 (L.ValInteger (-2)) (L.SDiv True))
        [("sdiv_neg2_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "urem0_right.c"
        (oneArithRight "urem0_right" i32 (L.ValInteger 0) L.URem)
        [("urem0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "urem1_right.c"
        (oneArithRight "urem1_right" i32 (L.ValInteger 1) L.URem)
        [("urem1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "urem_neg1_right.c"
        (oneArithRight "urem_neg1_right" i32 (L.ValInteger (-1)) L.URem)
        [("urem_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "urem2_right.c"
        (oneArithRight "urem2_right" i32 (L.ValInteger 2) L.URem)
        [("urem2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem0_right.c"
        (oneArithRight "srem0_right" i32 (L.ValInteger 0) L.SRem)
        [("srem0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem1_right.c"
        (oneArithRight "srem1_right" i32 (L.ValInteger 1) L.SRem)
        [("srem1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem_neg1_right.c"
        (oneArithRight "srem_neg1_right" i32 (L.ValInteger (-1)) L.SRem)
        [("srem_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem2_right.c"
        (oneArithRight "srem2_right" i32 (L.ValInteger 2) L.SRem)
        [("srem2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem_neg2_right.c"
        (oneArithRight "srem_neg2_right" i32 (L.ValInteger (-2)) L.SRem)
        [("srem_neg2_right", isSafeWithPreconditions mempty DidntHitBounds)]
    ]

main :: IO ()
main =
  TT.defaultMain $
    TT.testGroup
      "uc-crux-llvm"
      [ inFileTests,
        moduleTests,
        isUnimplemented "call_function_pointer.c" "call_function_pointer", -- goal: ???
        isUnimplemented "call_varargs_function_pointer.c" "call_varargs_function_pointer", -- goal: ???
        isUnimplemented "id_varargs_function_pointer.c" "id_varargs_function_pointer", -- goal: isSafe
        isUnimplemented "do_fork.c" "do_fork", -- goal: ???
        isUnimplemented "do_recv.c" "do_recv",
        isUnimplemented "do_strdup.c" "do_strdup", -- goal: isSafe
        isUnimplemented "do_strcmp.c" "do_strcmp", -- goal: isSafe
        isUnimplemented "do_strncmp.c" "do_strncmp", -- goal: isSafe
        isUnimplemented "extern_non_void_function.c" "extern_non_void_function", -- goal: isSafeWithPreconditions
        isUnimplemented "read_errno.c" "read_errno", -- goal: isSafe

        -- Strangely, this compiles to a function that takes a variable-arity
        -- function as an argument?
        isUnimplemented
          "set_errno.c"
          "set_errno", -- goal: ???
        isUnimplemented
          "gethostname_neg_len.c"
          "gethostname_neg_len", -- goal: ???
        isUnimplemented
          "gethostname_arg_ptr_len.c"
          "gethostname_arg_ptr_len", -- goal: ???
        isUnimplemented
          "cast_int_to_pointer_dereference.c"
          "cast_int_to_pointer_dereference", -- goal: isSafeWithPreconditions
        isUnimplemented
          "cast_int_to_pointer_memset.c"
          "cast_int_to_pointer_memset", -- goal: isSafeWithPreconditions
        isUnimplemented
          "gethostname_arg_len.c"
          "gethostname_arg_len" -- goal: ???
      ]
