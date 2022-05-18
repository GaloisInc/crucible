{-
Module           : Main
Description      : Tests
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

For now, this test suite mostly has \"acceptance tests\", i.e. tests that
describe very high-level behavior.

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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Main (main) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Control.Monad (unless)
import           Data.Foldable (for_)
import qualified Data.Text as Text
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH
import qualified Test.Tasty.QuickCheck as TQ

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (NatRepr, knownNat)

-- Code being tested
import           UCCrux.LLVM.Main (loopOnFunctions)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (defnTypes)
import           UCCrux.LLVM.Equivalence (NonEmptyCrashDiff, reportDiffs, getCrashDiffs)
import           UCCrux.LLVM.Errors.Unimplemented (catchUnimplemented)
import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.Classify.Types (partitionUncertainty)
import           UCCrux.LLVM.FullType (FullType(..), FullTypeRepr(..), type StructPacked(UnpackedStruct))
import           UCCrux.LLVM.Module (defnSymbolToString)
import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName, functionNameFromString)
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName(..))
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName(..))
import           UCCrux.LLVM.Run.EntryPoints (makeEntryPointsOrThrow)
import           UCCrux.LLVM.Run.Result (SomeBugfindingResult', DidHitBounds(DidHitBounds, DidntHitBounds))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness(..))

import qualified Callgraph
import qualified Check
import qualified Postcond
import qualified Utils
{- ORMOLU_ENABLE -}

-- Just test that a few things typecheck as expected

exampleHere :: Cursor m ('FTInt 64) ('FTInt 64)
exampleHere = Here (FTIntRepr knownNat)

_exampleArray :: Cursor m ('FTArray ('Just 8) ('FTInt 64)) ('FTInt 64)
_exampleArray = Index (knownNat :: NatRepr 7) knownNat exampleHere

_exampleStruct ::
  Cursor
    m
    ('FTStruct 'UnpackedStruct ('Ctx.EmptyCtx Ctx.::> 'FTInt 32 Ctx.::> 'FTInt 64))
    ('FTInt 64)
_exampleStruct =
  Field
    (Ctx.extend (Ctx.extend Ctx.empty (FTIntRepr knownNat)) (FTIntRepr knownNat))
    (Ctx.lastIndex Ctx.knownSize)
    exampleHere

findBugs ::
  Maybe L.Module ->
  FilePath ->
  [FunctionName] ->
  IO (Map.Map String Result.SomeBugfindingResult')
findBugs llvmModule file fns =
  Utils.withOptions llvmModule file $
    \appCtx modCtx halloc cruxOpts llOpts ->
      fmap (Map.mapKeys defnSymbolToString . Map.map Result.SomeBugfindingResult') <$>
        loopOnFunctions
          appCtx
          modCtx
          halloc
          cruxOpts
          llOpts
          =<< makeEntryPointsOrThrow (modCtx ^. defnTypes) fns

getCrashDiff ::
  FilePath ->
  L.Module ->
  FilePath ->
  L.Module ->
  IO (AppContext, ([(FunctionName, NonEmptyCrashDiff)], [(FunctionName, NonEmptyCrashDiff)]))
getCrashDiff path1 mod1 path2 mod2 =
  Utils.withOptions (Just mod1) path1 $
    \_ modCtx1 _ _ _ ->
      Utils.withOptions (Just mod2) path2 $
        \appCtx modCtx2 halloc cruxOpts llOpts ->
           (appCtx,) <$>
             getCrashDiffs
               appCtx
               modCtx1
               modCtx2
               halloc
               cruxOpts
               llOpts
               [] -- All functions in the intersection of both modules

checkCrashDiff ::
  FilePath ->
  L.Module ->
  FilePath ->
  L.Module ->
  -- | Should the check be for strict equivalence?
  Bool ->
  -- | Should the result be inverted?
  Bool ->
  TT.TestTree
checkCrashDiff path1 mod1 path2 mod2 equivalent invert =
  TH.testCase
    ( unwords
        [ path1,
          if equivalent
            then "is crash-equivalent to"
            else "crashes less than",
          path2
        ]
    )
    $ do
      (appCtx, (diffs12, diffs21)) <- getCrashDiff path1 mod1 path2 mod2
      let diffs21' = if equivalent then diffs21 else []
      reportDiffs appCtx diffs12 diffs21'
      unless ((if invert then not else id) (null diffs12 && null diffs21')) $
        TH.assertFailure
          ( unwords
              [ "Expected",
                path1,
                "and",
                path2,
                "to",
                (if invert then "not " else "") ++ "be crash-equivalent."
              ]
          )

inFile :: FilePath -> [(String, String -> SomeBugfindingResult' -> IO ())] -> TT.TestTree
inFile file specs =
  TH.testCase file $
    do
      results <-
        findBugs Nothing file (map (functionNameFromString . fst) specs)
      for_ specs $
        \(fn, spec) ->
          spec fn $
            fromMaybe (error ("Couldn't find result for function" ++ fn)) $
              Map.lookup fn results

inModule :: FilePath -> L.Module -> [(String, String -> SomeBugfindingResult' -> IO ())] -> TT.TestTree
inModule fakePath llvmModule specs =
  TH.testCase fakePath $
    do
      results <-
        findBugs (Just llvmModule) fakePath (map (functionNameFromString . fst) specs)
      for_ specs $
        \(fn, spec) ->
          spec fn $ fromMaybe (error ("Couldn't find result for function" ++ fn)) $ Map.lookup fn results

-- | TODO: Take a list of TruePositiveTag, verify that those are the bugs.
hasBugs :: String -> SomeBugfindingResult' -> IO ()
hasBugs fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
  do
    [] TH.@=? map show (Result.uncertainResults result)
    case Result.summary result of
      Result.FoundBugs _bugs -> pure ()
      _ -> TH.assertFailure (unwords ["Expected", fn, "to have bugs"])

isSafe :: Unsoundness -> String -> SomeBugfindingResult' -> IO ()
isSafe unsoundness fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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

isSafeToBounds :: Unsoundness -> String -> SomeBugfindingResult' -> IO ()
isSafeToBounds unsoundness fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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
isSafeWithPreconditions :: Unsoundness -> DidHitBounds -> String -> SomeBugfindingResult' -> IO ()
isSafeWithPreconditions unsoundness hitBounds fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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

_isUnannotated :: String -> SomeBugfindingResult' -> IO ()
_isUnannotated fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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

_hasFailedAssert :: String -> SomeBugfindingResult' -> IO ()
_hasFailedAssert fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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

isUnclassified :: String -> SomeBugfindingResult' -> IO ()
isUnclassified fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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

isUnfixed :: String -> SomeBugfindingResult' -> IO ()
isUnfixed fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
  do
    let (missingAnn, failedAssert, unimpl, unclass, unfixed, unfixable, timeouts) =
          partitionUncertainty (Result.uncertainResults result)
    [] TH.@=? map show missingAnn
    [] TH.@=? map show failedAssert
    [] TH.@=? map show unimpl
    [] TH.@=? map show unclass
    [] TH.@=? map show unfixable
    [] TH.@=? map show timeouts
    0 < length unfixed
      TH.@? unwords
        [ "Expected",
          fn,
          "to be unfixed but the result was:\n",
          Text.unpack (Result.printFunctionSummary (Result.summary result))
        ]

hasMissingAnn :: String -> SomeBugfindingResult' -> IO ()
hasMissingAnn fn (Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _)) =
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
          results <- findBugs Nothing file [functionNameFromString fn]
          Result.SomeBugfindingResult' (Result.SomeBugfindingResult _ result _) <-
            pure $ fromMaybe (error "No result") (Map.lookup fn results)
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

skipOverrides :: [String] -> Unsoundness
skipOverrides names =
  Unsoundness Set.empty (Set.fromList (map (SkipOverrideName . Text.pack) names))

skipOverride :: String -> Unsoundness
skipOverride = skipOverrides . (: [])

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
        ("call_non_function_pointer.c", [("call_non_function_pointer", hasBugs)]),
        ("cast_float_to_pointer_deref.c", [("cast_float_to_pointer_deref", hasBugs)]),
        ("deref_func_ptr.c", [("deref_func_ptr", hasBugs)]),
        ("double_free.c", [("double_free", hasBugs)]),
        ("uninitialized_heap.c", [("uninitialized_heap", hasBugs)]),
        ("uninitialized_stack.c", [("uninitialized_stack", hasBugs)]),
        ("write_to_null.c", [("write_to_null", hasBugs)]),
        ("read_extern_global.c", [("read_extern_global", isSafe mempty)]),
        ("read_extern_global_sized_array.c", [("read_extern_global_sized_array", isSafe mempty)]),
        ("branch.c", [("branch", isSafe mempty)]),
        -- Unclear whether this is undefined behavior. C11 section 6.5.4 says
        -- floats can't be cast to pointers, but this one goes through an
        -- integer first which may be OK.
        ("cast_float_to_pointer.c", [("cast_float_to_pointer", isSafe mempty)]),
        ("compare_to_null.c", [("compare_to_null", isSafe mempty)]),
        ("do_getchar.c", [("do_getchar", isSafe (skipOverride "getc"))]),
        ("do_fork.c", [("do_fork", isSafe (skipOverride "fork"))]),
        -- TODO(lb): This test skips an additional function (bcmp) in CI. Not
        -- sure what the cause for the discrepancy is.
        -- ("do_recv.c", [("do_recv", isSafe (skipOverrides ["accept", "bind", "close", "listen", "memcmp", "recv", "shutdown", "socket"]))]),
        ("do_strdup.c", [("do_strdup", isSafe (skipOverride "strdup"))]),
        ("do_strcmp.c", [("do_strcmp", isSafe (skipOverride "strcmp"))]),
        ("do_strncmp.c", [("do_strncmp", isSafe (skipOverride "strncmp"))]),
        ("extern_non_void_function.c", [("extern_non_void_function", isSafe (skipOverride "do_stuff"))]),
        ("extern_void_function.c", [("extern_void_function", isSafe (skipOverride "do_stuff"))]),
        -- This override needs refinement; the following should be safe with the
        -- precondition that the argument pointer is valid.
        ("getenv_arg.c", [("getenv_arg", isSafe (unsoundOverride "getenv"))]),
        ("getenv_const.c", [("getenv_const", isSafe (unsoundOverride "getenv"))]),
        ("gethostname_const_len.c", [("gethostname_const_len", isSafe (unsoundOverride "gethostname"))]),
        ("id_function_pointer.c", [("id_function_pointer", isSafe mempty)]),
        ("id_varargs_function_pointer.c", [("id_varargs_function_pointer", isSafe mempty)]),
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
        ("read_errno.c", [("read_errno", isSafeWithPreconditions (skipOverride "__errno_location") DidntHitBounds)]),
        ("read_pointer_from_global_struct.c", [("read_pointer_from_global_struct", isSafeWithPreconditions mempty DidntHitBounds)]),
        ("read_null_global_pointer.c", [("read_null_global_pointer", isSafeWithPreconditions mempty DidntHitBounds)]),
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
        ("cast_float_to_pointer_free.c", [("cast_float_to_pointer_free", isUnclassified)]),
        ("cast_float_to_pointer_write.c", [("cast_float_to_pointer_write", isUnclassified)]),
        ("free_with_offset.c", [("free_with_offset", isUnclassified)]), -- goal: hasBugs
        ("memset_arg_len.c", [("memset_arg_len", isUnclassified)]), -- goal: isSafeWP
        ("memset_func_ptr.c", [("memset_func_ptr", isUnclassified)]), -- goal: hasBugs
        ("memset_void_ptr.c", [("memset_void_ptr", isUnclassified)]), -- goal: isSafeWP
        ("nested_structs.c", [("nested_structs", isUnclassified)]), -- goal: ???
        ("oob_read_heap.c", [("oob_read_heap", isUnclassified)]), -- goal: hasBugs
        ("oob_read_stack.c", [("oob_read_stack", isUnclassified)]), -- goal: hasBugs
        ("read_global_neg_offset.c", [("read_global_neg_offset", isUnclassified)]), -- goal: hasBugs
        ("read_global_neg_offset_strlen.c", [("read_global_neg_offset_strlen", isUnclassified)]), -- goal: hasBugs
        ("signed_add_wrap_concrete.c", [("signed_add_wrap_concrete", isUnclassified)]), -- goal: hasBugs
        ("signed_mul_wrap_concrete.c", [("signed_mul_wrap_concrete", isUnclassified)]), -- goal: hasBugs
        ("signed_sub_wrap_concrete.c", [("signed_sub_wrap_concrete", isUnclassified)]), -- goal: hasBugs
        ("write_const_global.c", [("write_const_global", isUnclassified)]), -- goal: hasBugs
        ("use_after_free.c", [("use_after_free", isUnclassified)]), -- goal: hasBugs
        --
        --
        -- TODO(lb): Fix upstream? Missing annotations just seems like a bug.
        ("cast_void_pointer.c", [("cast_void_pointer", hasMissingAnn)]),
        ("cast_pointer_to_float.c", [("cast_pointer_to_float", hasMissingAnn)]), -- goal: hasBugs
        ("compare_ptr_to_int.c", [("compare_ptr_to_int", hasMissingAnn)]), -- goal: hasBugs
        ("compare_ptr_to_size_t.c", [("compare_ptr_to_size_t", hasMissingAnn)]), -- goal: hasBugs
        ("compare_ptrs_different_heap_allocs.c", [("compare_ptrs_different_heap_allocs", hasMissingAnn)]), -- goal: hasBugs
        ("compare_ptrs_different_stack_allocs.c", [("compare_ptrs_different_stack_allocs", hasMissingAnn)]), -- goal: hasBugs
        ("memcpy_const_len.c", [("memcpy_const_len", hasMissingAnn)]),
        ("deref_arg_arg_index.c", [("deref_arg_arg_index", hasMissingAnn)]),
        -- This one could use an override. Currently fails because it's
        -- skipped, and so unreachable code gets reached.
        ("do_exit.c", [("do_exit", hasMissingAnn)]), -- goal: isSafe
        -- TODO: https://github.com/GaloisInc/crucible/issues/651
        -- , isSafeWithPreconditions "do_strlen.c" "do_strlen" False
        ("call_function_pointer.c", [("call_function_pointer", isUnfixed)]), -- goal: ???
        ("call_varargs_function_pointer.c", [("call_varargs_function_pointer", isUnfixed)]), -- goal: ???
        -- Strangely, this compiles to a function that takes a variable-arity
        -- function as an argument?
        ("set_errno.c", [("set_errno", isUnfixed)]) -- goal: ???

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
      L.defVisibility = Nothing,
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

add1Left :: L.Module
add1Left = oneArithLeft "add1_left" i32 (L.ValInteger 1) (L.Add False False)

add1NswLeft :: L.Module
add1NswLeft = oneArithLeft "add1_nsw_left" i32 (L.ValInteger 1) (L.Add False True)

add1NuwLeft :: L.Module
add1NuwLeft = oneArithLeft "add1_nuw_left" i32 (L.ValInteger 1) (L.Add True False)

addNeg1Left :: L.Module
addNeg1Left = oneArithLeft "add_neg1_left" i32 (L.ValInteger (-1)) (L.Add False False)

addNeg1NswLeft :: L.Module
addNeg1NswLeft = oneArithLeft "add_neg1_nsw_left" i32 (L.ValInteger (-1)) (L.Add False True)

addNeg1NuwLeft :: L.Module
addNeg1NuwLeft = oneArithLeft "add_neg1_nuw_left" i32 (L.ValInteger (-1)) (L.Add True False)

add1FloatLeft :: L.Module
add1FloatLeft = oneArithLeft "add1_float_left" float (L.ValFloat 1.0) L.FAdd

addNeg1FloatLeft :: L.Module
addNeg1FloatLeft = oneArithLeft "add_neg1_float_left" float (L.ValFloat (-1.0)) L.FAdd

add1DoubleLeft :: L.Module
add1DoubleLeft = oneArithLeft "add1_double_left" double (L.ValDouble 1.0) L.FAdd

addNeg1DoubleLeft :: L.Module
addNeg1DoubleLeft = oneArithLeft "add_neg1_double_left" double (L.ValDouble (-1.0)) L.FAdd

sub1Left :: L.Module
sub1Left = oneArithLeft "sub1_left" i32 (L.ValInteger 1) (L.Sub False False)

sub1NswLeft :: L.Module
sub1NswLeft = oneArithLeft "sub1_nsw_left" i32 (L.ValInteger 1) (L.Sub False True)

sub1NuwLeft :: L.Module
sub1NuwLeft = oneArithLeft "sub1_nuw_left" i32 (L.ValInteger 1) (L.Sub True False)

subNeg1Left :: L.Module
subNeg1Left = oneArithLeft "sub_neg1_left" i32 (L.ValInteger (-1)) (L.Sub False False)

subNeg1NswLeft :: L.Module
subNeg1NswLeft = oneArithLeft "sub_neg1_nsw_left" i32 (L.ValInteger (-1)) (L.Sub False True)

subNeg1NuwLeft :: L.Module
subNeg1NuwLeft = oneArithLeft "sub_neg1_nuw_left" i32 (L.ValInteger (-1)) (L.Sub True False)

sub1FloatLeft :: L.Module
sub1FloatLeft = oneArithLeft "sub1_float_left" float (L.ValFloat 1.0) L.FSub

subNeg1FloatLeft :: L.Module
subNeg1FloatLeft = oneArithLeft "sub_neg1_float_left" float (L.ValFloat (-1.0)) L.FSub

sub1DoubleLeft :: L.Module
sub1DoubleLeft = oneArithLeft "sub1_double_left" double (L.ValDouble 1.0) L.FSub

subNeg1DoubleLeft :: L.Module
subNeg1DoubleLeft = oneArithLeft "sub_neg1_double_left" double (L.ValDouble (-1.0)) L.FSub

mul0Left :: L.Module
mul0Left = oneArithLeft "mul0_left" i32 (L.ValInteger 0) (L.Mul True True)

mul1Left :: L.Module
mul1Left = oneArithLeft "mul1_left" i32 (L.ValInteger 1) (L.Mul False False)

mul1NswLeft :: L.Module
mul1NswLeft = oneArithLeft "mul1_nsw_left" i32 (L.ValInteger 1) (L.Mul False True)

mul1NuwLeft :: L.Module
mul1NuwLeft = oneArithLeft "mul1_nuw_left" i32 (L.ValInteger 1) (L.Mul True False)

mulNeg1Left :: L.Module
mulNeg1Left = oneArithLeft "mul_neg1_left" i32 (L.ValInteger (-1)) (L.Mul False False)

mulNeg1NswLeft :: L.Module
mulNeg1NswLeft = oneArithLeft "mul_neg1_nsw_left" i32 (L.ValInteger (-1)) (L.Mul False True)

mulNeg1NuwLeft :: L.Module
mulNeg1NuwLeft = oneArithLeft "mul_neg1_nuw_left" i32 (L.ValInteger (-1)) (L.Mul True False)

udiv0Left :: L.Module
udiv0Left = oneArithLeft "udiv0_left" i32 (L.ValInteger 0) (L.UDiv False)

udiv1Left :: L.Module
udiv1Left = oneArithLeft "udiv1_left" i32 (L.ValInteger 1) (L.UDiv False)

udiv1ExactLeft :: L.Module
udiv1ExactLeft = oneArithLeft "udiv1_exact_left" i32 (L.ValInteger 1) (L.UDiv True)

udiv2Left :: L.Module
udiv2Left = oneArithLeft "udiv2_left" i32 (L.ValInteger 2) (L.UDiv False)

udiv2ExactLeft :: L.Module
udiv2ExactLeft = oneArithLeft "udiv2_exact_left" i32 (L.ValInteger 2) (L.UDiv True)

udivNeg1Left :: L.Module
udivNeg1Left = oneArithLeft "udiv_neg1_left" i32 (L.ValInteger (-1)) (L.UDiv False)

udivNeg1ExactLeft :: L.Module
udivNeg1ExactLeft = oneArithLeft "udiv_neg1_exact_left" i32 (L.ValInteger (-1)) (L.UDiv True)

sdiv0Left :: L.Module
sdiv0Left = oneArithLeft "sdiv0_left" i32 (L.ValInteger 0) (L.SDiv False)

sdiv1Left :: L.Module
sdiv1Left = oneArithLeft "sdiv1_left" i32 (L.ValInteger 1) (L.SDiv False)

sdiv1ExactLeft :: L.Module
sdiv1ExactLeft = oneArithLeft "sdiv1_exact_left" i32 (L.ValInteger 1) (L.SDiv True)

sdivNeg1Left :: L.Module
sdivNeg1Left = oneArithLeft "sdiv_neg1_left" i32 (L.ValInteger (-1)) (L.SDiv False)

sdivNeg1ExactLeft :: L.Module
sdivNeg1ExactLeft = oneArithLeft "sdiv_neg1_exact_left" i32 (L.ValInteger (-1)) (L.SDiv True)

sdiv2Left :: L.Module
sdiv2Left = oneArithLeft "sdiv2_left" i32 (L.ValInteger 2) (L.SDiv False)

sdiv2ExactLeft :: L.Module
sdiv2ExactLeft = oneArithLeft "sdiv2_exact_left" i32 (L.ValInteger 2) (L.SDiv True)

sdivNeg2Left :: L.Module
sdivNeg2Left = oneArithLeft "sdiv_neg2_left" i32 (L.ValInteger (-2)) (L.SDiv False)

sdivNeg2ExactLeft :: L.Module
sdivNeg2ExactLeft = oneArithLeft "sdiv_neg2_exact_left" i32 (L.ValInteger (-2)) (L.SDiv True)

urem0Left :: L.Module
urem0Left = oneArithLeft "urem0_left" i32 (L.ValInteger 0) L.URem

urem1Left :: L.Module
urem1Left = oneArithLeft "urem1_left" i32 (L.ValInteger 1) L.URem

uremNeg1Left :: L.Module
uremNeg1Left = oneArithLeft "urem_neg1_left" i32 (L.ValInteger (-1)) L.URem

urem2Left :: L.Module
urem2Left = oneArithLeft "urem2_left" i32 (L.ValInteger 2) L.URem

srem0Left :: L.Module
srem0Left = oneArithLeft "srem0_left" i32 (L.ValInteger 0) L.SRem

srem1Left :: L.Module
srem1Left = oneArithLeft "srem1_left" i32 (L.ValInteger 1) L.SRem

sremNeg1Left :: L.Module
sremNeg1Left = oneArithLeft "srem_neg1_left" i32 (L.ValInteger (-1)) L.SRem

srem2Left :: L.Module
srem2Left = oneArithLeft "srem2_left" i32 (L.ValInteger 2) L.SRem

sremNeg2Left :: L.Module
sremNeg2Left = oneArithLeft "srem_neg2_left" i32 (L.ValInteger (-2)) L.SRem

add1Right :: L.Module
add1Right = oneArithRight "add1_right" i32 (L.ValInteger 1) (L.Add False False)

add1NswRight :: L.Module
add1NswRight = oneArithRight "add1_nsw_right" i32 (L.ValInteger 1) (L.Add False True)

add1NuwRight :: L.Module
add1NuwRight = oneArithRight "add1_nuw_right" i32 (L.ValInteger 1) (L.Add True False)

addNeg1Right :: L.Module
addNeg1Right = oneArithRight "add_neg1_right" i32 (L.ValInteger (-1)) (L.Add False False)

addNeg1NswRight :: L.Module
addNeg1NswRight = oneArithRight "add_neg1_nsw_right" i32 (L.ValInteger (-1)) (L.Add False True)

addNeg1NuwRight :: L.Module
addNeg1NuwRight = oneArithRight "add_neg1_nuw_right" i32 (L.ValInteger (-1)) (L.Add True False)

add1FloatRight :: L.Module
add1FloatRight = oneArithRight "add1_float_right" float (L.ValFloat 1.0) L.FAdd

addNeg1FloatRight :: L.Module
addNeg1FloatRight = oneArithRight "add_neg1_float_right" float (L.ValFloat (-1.0)) L.FAdd

add1DoubleRight :: L.Module
add1DoubleRight = oneArithRight "add1_double_right" double (L.ValDouble 1.0) L.FAdd

addNeg1DoubleRight :: L.Module
addNeg1DoubleRight = oneArithRight "add_neg1_double_right" double (L.ValDouble (-1.0)) L.FAdd

sub1Right :: L.Module
sub1Right = oneArithRight "sub1_right" i32 (L.ValInteger 1) (L.Sub False False)

sub1NswRight :: L.Module
sub1NswRight = oneArithRight "sub1_nsw_right" i32 (L.ValInteger 1) (L.Sub False True)

sub1NuwRight :: L.Module
sub1NuwRight = oneArithRight "sub1_nuw_right" i32 (L.ValInteger 1) (L.Sub True False)

subNeg1Right :: L.Module
subNeg1Right = oneArithRight "sub_neg1_right" i32 (L.ValInteger (-1)) (L.Sub False False)

subNeg1NswRight :: L.Module
subNeg1NswRight = oneArithRight "sub_neg1_nsw_right" i32 (L.ValInteger (-1)) (L.Sub False True)

subNeg1NuwRight :: L.Module
subNeg1NuwRight = oneArithRight "sub_neg1_nuw_right" i32 (L.ValInteger (-1)) (L.Sub True False)

sub1FloatRight :: L.Module
sub1FloatRight = oneArithRight "sub1_float_right" float (L.ValFloat 1.0) L.FSub

subNeg1FloatRight :: L.Module
subNeg1FloatRight = oneArithRight "sub_neg1_float_right" float (L.ValFloat (-1.0)) L.FSub

sub1DoubleRight :: L.Module
sub1DoubleRight = oneArithRight "sub1_double_right" double (L.ValDouble 1.0) L.FSub

subNeg1DoubleRight :: L.Module
subNeg1DoubleRight = oneArithRight "sub_neg1_double_right" double (L.ValDouble (-1.0)) L.FSub

mul0Right :: L.Module
mul0Right = oneArithRight "mul0_right" i32 (L.ValInteger 0) (L.Mul True True)

mul1Right :: L.Module
mul1Right = oneArithRight "mul1_right" i32 (L.ValInteger 1) (L.Mul False False)

mul1NswRight :: L.Module
mul1NswRight = oneArithRight "mul1_nsw_right" i32 (L.ValInteger 1) (L.Mul False True)

mul1NuwRight :: L.Module
mul1NuwRight = oneArithRight "mul1_nuw_right" i32 (L.ValInteger 1) (L.Mul True False)

mulNeg1Right :: L.Module
mulNeg1Right = oneArithRight "mul_neg1_right" i32 (L.ValInteger (-1)) (L.Mul False False)

mulNeg1NswRight :: L.Module
mulNeg1NswRight = oneArithRight "mul_neg1_nsw_right" i32 (L.ValInteger (-1)) (L.Mul False True)

mulNeg1NuwRight :: L.Module
mulNeg1NuwRight = oneArithRight "mul_neg1_nuw_right" i32 (L.ValInteger (-1)) (L.Mul True False)

udiv0Right :: L.Module
udiv0Right = oneArithRight "udiv0_right" i32 (L.ValInteger 0) (L.UDiv False)

udiv1Right :: L.Module
udiv1Right = oneArithRight "udiv1_right" i32 (L.ValInteger 1) (L.UDiv False)

udiv1ExactRight :: L.Module
udiv1ExactRight = oneArithRight "udiv1_exact_right" i32 (L.ValInteger 1) (L.UDiv True)

udiv2Right :: L.Module
udiv2Right = oneArithRight "udiv2_right" i32 (L.ValInteger 2) (L.UDiv False)

udiv2ExactRight :: L.Module
udiv2ExactRight = oneArithRight "udiv2_exact_right" i32 (L.ValInteger 2) (L.UDiv True)

udivNeg1Right :: L.Module
udivNeg1Right = oneArithRight "udiv_neg1_right" i32 (L.ValInteger (-1)) (L.UDiv False)

udivNeg1ExactRight :: L.Module
udivNeg1ExactRight = oneArithRight "udiv_neg1_exact_right" i32 (L.ValInteger (-1)) (L.UDiv True)

sdiv0Right :: L.Module
sdiv0Right = oneArithRight "sdiv0_right" i32 (L.ValInteger 0) (L.SDiv False)

sdiv1Right :: L.Module
sdiv1Right = oneArithRight "sdiv1_right" i32 (L.ValInteger 1) (L.SDiv False)

sdiv1ExactRight :: L.Module
sdiv1ExactRight = oneArithRight "sdiv1_exact_right" i32 (L.ValInteger 1) (L.SDiv True)

sdivNeg1Right :: L.Module
sdivNeg1Right = oneArithRight "sdiv_neg1_right" i32 (L.ValInteger (-1)) (L.SDiv False)

sdivNeg1ExactRight :: L.Module
sdivNeg1ExactRight = oneArithRight "sdiv_neg1_exact_right" i32 (L.ValInteger (-1)) (L.SDiv True)

sdiv2Right :: L.Module
sdiv2Right = oneArithRight "sdiv2_right" i32 (L.ValInteger 2) (L.SDiv False)

sdiv2ExactRight :: L.Module
sdiv2ExactRight = oneArithRight "sdiv2_exact_right" i32 (L.ValInteger 2) (L.SDiv True)

sdivNeg2Right :: L.Module
sdivNeg2Right = oneArithRight "sdiv_neg2_right" i32 (L.ValInteger (-2)) (L.SDiv False)

sdivNeg2ExactRight :: L.Module
sdivNeg2ExactRight = oneArithRight "sdiv_neg2_exact_right" i32 (L.ValInteger (-2)) (L.SDiv True)

urem0Right :: L.Module
urem0Right = oneArithRight "urem0_right" i32 (L.ValInteger 0) L.URem

urem1Right :: L.Module
urem1Right = oneArithRight "urem1_right" i32 (L.ValInteger 1) L.URem

uremNeg1Right :: L.Module
uremNeg1Right = oneArithRight "urem_neg1_right" i32 (L.ValInteger (-1)) L.URem

urem2Right :: L.Module
urem2Right = oneArithRight "urem2_right" i32 (L.ValInteger 2) L.URem

srem0Right :: L.Module
srem0Right = oneArithRight "srem0_right" i32 (L.ValInteger 0) L.SRem

srem1Right :: L.Module
srem1Right = oneArithRight "srem1_right" i32 (L.ValInteger 1) L.SRem

sremNeg1Right :: L.Module
sremNeg1Right = oneArithRight "srem_neg1_right" i32 (L.ValInteger (-1)) L.SRem

srem2Right :: L.Module
srem2Right = oneArithRight "srem2_right" i32 (L.ValInteger 2) L.SRem

sremNeg2Right :: L.Module
sremNeg2Right = oneArithRight "srem_neg2_right" i32 (L.ValInteger (-2)) L.SRem

arithModules :: [L.Module]
arithModules =
  [ add1Left,
    add1NswLeft,
    add1NuwLeft,
    addNeg1Left,
    addNeg1NswLeft,
    addNeg1NuwLeft,
    add1FloatLeft,
    addNeg1FloatLeft,
    add1DoubleLeft,
    addNeg1DoubleLeft,
    sub1Left,
    sub1NswLeft,
    sub1NuwLeft,
    subNeg1Left,
    subNeg1NswLeft,
    subNeg1NuwLeft,
    sub1FloatLeft,
    subNeg1FloatLeft,
    sub1DoubleLeft,
    subNeg1DoubleLeft,
    mul0Left,
    mul1Left,
    mul1NswLeft,
    mul1NuwLeft,
    mulNeg1Left,
    mulNeg1NswLeft,
    mulNeg1NuwLeft,
    udiv0Left,
    udiv1Left,
    udiv1ExactLeft,
    udiv2Left,
    udiv2ExactLeft,
    udivNeg1Left,
    udivNeg1ExactLeft,
    sdiv0Left,
    sdiv1Left,
    sdiv1ExactLeft,
    sdivNeg1Left,
    sdivNeg1ExactLeft,
    sdiv2Left,
    sdiv2ExactLeft,
    sdivNeg2Left,
    sdivNeg2ExactLeft,
    urem0Left,
    urem1Left,
    uremNeg1Left,
    urem2Left,
    srem0Left,
    srem1Left,
    sremNeg1Left,
    srem2Left,
    sremNeg2Left,
    add1Right,
    add1NswRight,
    add1NuwRight,
    addNeg1Right,
    addNeg1NswRight,
    addNeg1NuwRight,
    add1FloatRight,
    addNeg1FloatRight,
    add1DoubleRight,
    addNeg1DoubleRight,
    sub1Right,
    sub1NswRight,
    sub1NuwRight,
    subNeg1Right,
    subNeg1NswRight,
    subNeg1NuwRight,
    sub1FloatRight,
    subNeg1FloatRight,
    sub1DoubleRight,
    subNeg1DoubleRight,
    mul0Right,
    mul1Right,
    mul1NswRight,
    mul1NuwRight,
    mulNeg1Right,
    mulNeg1NswRight,
    mulNeg1NuwRight,
    udiv0Right,
    udiv1Right,
    udiv1ExactRight,
    udiv2Right,
    udiv2ExactRight,
    udivNeg1Right,
    udivNeg1ExactRight,
    sdiv0Right,
    sdiv1Right,
    sdiv1ExactRight,
    sdivNeg1Right,
    sdivNeg1ExactRight,
    sdiv2Right,
    sdiv2ExactRight,
    sdivNeg2Right,
    sdivNeg2ExactRight,
    urem0Right,
    urem1Right,
    uremNeg1Right,
    urem2Right,
    srem0Right,
    srem1Right,
    sremNeg1Right,
    srem2Right,
    sremNeg2Right
  ]

newtype ArithModule = ArithModule L.Module
  deriving (Eq, Ord, Show)

instance TQ.Arbitrary ArithModule where
  arbitrary = TQ.oneof (map (pure . ArithModule) arithModules)

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
        add1Left
        [("add1_left", isSafe mempty)],
      inModule
        "add1_nsw_left.c"
        add1NswLeft
        [("add1_nsw_left", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "add1_nuw_left.c"
        add1NuwLeft
        [("add1_nuw_left", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add_neg1_left.c"
        addNeg1Left
        [("add_neg1_left", isSafe mempty)],
      inModule
        "add_neg1_nsw_left.c"
        addNeg1NswLeft
        [("add_neg1_nsw_left", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "add_neg1_nuw_left.c"
        addNeg1NuwLeft
        [("add_neg1_nuw_left", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add1_float_left.c"
        add1FloatLeft
        [("add1_float_left", isSafe mempty)],
      inModule
        "add_neg1_float_left.c"
        addNeg1FloatLeft
        [("add_neg1_float_left", isSafe mempty)],
      inModule
        "add1_double_left.c"
        add1DoubleLeft
        [("add1_double_left", isSafe mempty)],
      inModule
        "add_neg1_double_left.c"
        addNeg1DoubleLeft
        [("add_neg1_double_left", isSafe mempty)],
      inModule
        "sub1_left.c"
        sub1Left
        [("sub1_left", isSafe mempty)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub1_nsw_left.c"
        sub1NswLeft
        [("sub1_nsw_left", isUnclassified)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub1_nuw_left.c"
        sub1NuwLeft
        [("sub1_nuw_left", isUnclassified)],
      inModule
        "sub_neg1_left.c"
        subNeg1Left
        [("sub_neg1_left", isSafe mempty)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub_neg1_nsw_left.c"
        subNeg1NswLeft
        [("sub_neg1_nsw_left", isUnclassified)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "sub_neg1_nuw_left.c"
        subNeg1NuwLeft
        [("sub_neg1_nuw_left", isUnclassified)],
      inModule
        "sub1_float_left.c"
        sub1FloatLeft
        [("sub1_float_left", isSafe mempty)],
      inModule
        "sub_neg1_float_left.c"
        subNeg1FloatLeft
        [("sub_neg1_float_left", isSafe mempty)],
      inModule
        "sub1_double_left.c"
        sub1DoubleLeft
        [("sub1_double_left", isSafe mempty)],
      inModule
        "sub_neg1_double_left.c"
        subNeg1DoubleLeft
        [("sub_neg1_double_left", isSafe mempty)],
      inModule
        "mul0_left.c"
        mul0Left
        [("mul0_left", isSafe mempty)],
      inModule
        "mul1_left.c"
        mul1Left
        [("mul1_left", isSafe mempty)],
      inModule
        "mul1_nsw_left.c"
        mul1NswLeft
        [("mul1_nsw_left", isSafe mempty)],
      inModule
        "mul1_nuw_left.c"
        mul1NuwLeft
        [("mul1_nuw_left", isSafe mempty)],
      inModule
        "mul_neg1_left.c"
        mulNeg1Left
        [("mul_neg1_left", isSafe mempty)],
      inModule
        "mul_neg1_nsw_left.c"
        mulNeg1NswLeft
        [("mul_neg1_nsw_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "mul_neg1_nuw_left.c"
        mulNeg1NuwLeft
        [("mul_neg1_nuw_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv0_left.c"
        udiv0Left
        [("udiv0_left", hasBugs)],
      inModule
        "udiv1_left.c"
        udiv1Left
        [("udiv1_left", isSafe mempty)],
      inModule
        "udiv1_exact_left.c"
        udiv1ExactLeft
        [("udiv1_exact_left", isSafe mempty)],
      inModule
        "udiv2_left.c"
        udiv2Left
        [("udiv2_left", isSafe mempty)],
      inModule
        "udiv2_exact_left.c"
        udiv2ExactLeft
        [("udiv2_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv_neg1_left.c"
        udivNeg1Left
        [("udiv_neg1_left", isSafe mempty)],
      inModule
        "udiv_neg1_exact_left.c"
        udivNeg1ExactLeft
        [("udiv_neg1_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv0_left.c"
        sdiv0Left
        [("sdiv0_left", hasBugs)],
      inModule
        "sdiv1_left.c"
        sdiv1Left
        [("sdiv1_left", isSafe mempty)],
      inModule
        "sdiv1_exact_left.c"
        sdiv1ExactLeft
        [("sdiv1_exact_left", isSafe mempty)],
      inModule
        "sdiv_neg1_left.c"
        sdivNeg1Left
        [("sdiv_neg1_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg1_exact_left.c"
        sdivNeg1ExactLeft
        [("sdiv_neg1_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv2_left.c"
        sdiv2Left
        [("sdiv2_left", isSafe mempty)],
      inModule
        "sdiv2_exact_left.c"
        sdiv2ExactLeft
        [("sdiv2_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg2_left.c"
        sdivNeg2Left
        [("sdiv_neg2_left", isSafe mempty)],
      inModule
        "sdiv_neg2_exact_left.c"
        sdivNeg2ExactLeft
        [("sdiv_neg2_exact_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "urem0_left.c"
        urem0Left
        [("urem0_left", hasBugs)],
      inModule
        "urem1_left.c"
        urem1Left
        [("urem1_left", isSafe mempty)],
      inModule
        "urem_neg1_left.c"
        uremNeg1Left
        [("urem_neg1_left", isSafe mempty)],
      inModule
        "urem2_left.c"
        urem2Left
        [("urem2_left", isSafe mempty)],
      inModule
        "srem0_left.c"
        srem0Left
        [("srem0_left", hasBugs)],
      inModule
        "srem1_left.c"
        srem1Left
        [("srem1_left", isSafe mempty)],
      inModule
        "srem_neg1_left.c"
        sremNeg1Left
        [("srem_neg1_left", isUnclassified)], -- TODO Goal: ???
      inModule
        "srem2_left.c"
        srem2Left
        [("srem2_left", isSafe mempty)],
      inModule
        "srem_neg2_left.c"
        sremNeg2Left
        [("srem_neg2_left", isSafe mempty)],
      -- --------------------------------------------------- On the right
      inModule
        "add1_right.c"
        add1Right
        [("add1_right", isSafe mempty)],
      inModule
        "add1_nsw_right.c"
        add1NswRight
        [("add1_nsw_right", isSafeWithPreconditions mempty DidntHitBounds)],
      -- TODO(lb) Goal: isSafeWithPreconditions, precondition is that the
      -- argument isn't near the min/max value.
      inModule
        "add1_nuw_right.c"
        add1NuwRight
        [("add1_nuw_right", isUnclassified)],
      inModule
        "add_neg1_right.c"
        addNeg1Right
        [("add_neg1_right", isSafe mempty)],
      inModule
        "add_neg1_nsw_right.c"
        addNeg1NswRight
        [("add_neg1_nsw_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "add_neg1_nuw_right.c"
        addNeg1NuwRight
        [("add_neg1_nuw_right", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "add1_float_right.c"
        add1FloatRight
        [("add1_float_right", isSafe mempty)],
      inModule
        "add_neg1_float_right.c"
        addNeg1FloatRight
        [("add_neg1_float_right", isSafe mempty)],
      inModule
        "add1_double_right.c"
        add1DoubleRight
        [("add1_double_right", isSafe mempty)],
      inModule
        "add_neg1_double_right.c"
        addNeg1DoubleRight
        [("add_neg1_double_right", isSafe mempty)],
      inModule
        "sub1_right.c"
        sub1Right
        [("sub1_right", isSafe mempty)],
      inModule
        "sub1_nsw_right.c"
        sub1NswRight
        [("sub1_nsw_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sub1_nuw_right.c"
        sub1NuwRight
        [("sub1_nuw_right", isUnclassified)], -- TODO(lb) Goal: isSafeWithPreconditions
      inModule
        "sub_neg1_right.c"
        subNeg1Right
        [("sub_neg1_right", isSafe mempty)],
      inModule
        "sub_neg1_nsw_right.c"
        subNeg1NswRight
        [("sub_neg1_nsw_right", isSafe mempty)], -- TODO Is this right?
      inModule
        "sub_neg1_nuw_right.c"
        subNeg1NuwRight
        [("sub_neg1_nuw_right", isSafe mempty)],
      inModule
        "sub1_float_right.c"
        sub1FloatRight
        [("sub1_float_right", isSafe mempty)],
      inModule
        "sub_neg1_float_right.c"
        subNeg1FloatRight
        [("sub_neg1_float_right", isSafe mempty)],
      inModule
        "sub1_double_right.c"
        sub1DoubleRight
        [("sub1_double_right", isSafe mempty)],
      inModule
        "sub_neg1_double_right.c"
        subNeg1DoubleRight
        [("sub_neg1_double_right", isSafe mempty)],
      inModule
        "mul0_right.c"
        mul0Right
        [("mul0_right", isSafe mempty)],
      inModule
        "mul1_right.c"
        mul1Right
        [("mul1_right", isSafe mempty)],
      inModule
        "mul1_nsw_right.c"
        mul1NswRight
        [("mul1_nsw_right", isSafe mempty)],
      inModule
        "mul1_nuw_right.c"
        mul1NuwRight
        [("mul1_nuw_right", isSafe mempty)],
      inModule
        "mul_neg1_right.c"
        mulNeg1Right
        [("mul_neg1_right", isSafe mempty)],
      inModule
        "mul_neg1_nsw_right.c"
        mulNeg1NswRight
        [("mul_neg1_nsw_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "mul_neg1_nuw_right.c"
        mulNeg1NuwRight
        [("mul_neg1_nuw_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv0_right.c"
        udiv0Right
        [("udiv0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv1_right.c"
        udiv1Right
        [("udiv1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv1_exact_right.c"
        udiv1ExactRight
        [("udiv1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv2_right.c"
        udiv2Right
        [("udiv2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv2_exact_right.c"
        udiv2ExactRight
        [("udiv2_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "udiv_neg1_right.c"
        udivNeg1Right
        [("udiv_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "udiv_neg1_exact_right.c"
        udivNeg1ExactRight
        [("udiv_neg1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv0_right.c"
        sdiv0Right
        [("sdiv0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv1_right.c"
        sdiv1Right
        [("sdiv1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv1_exact_right.c"
        sdiv1ExactRight
        [("sdiv1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg1_right.c"
        sdivNeg1Right
        [("sdiv_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv_neg1_exact_right.c"
        sdivNeg1ExactRight
        [("sdiv_neg1_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv2_right.c"
        sdiv2Right
        [("sdiv2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv2_exact_right.c"
        sdiv2ExactRight
        [("sdiv2_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "sdiv_neg2_right.c"
        sdivNeg2Right
        [("sdiv_neg2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "sdiv_neg2_exact_right.c"
        sdivNeg2ExactRight
        [("sdiv_neg2_exact_right", isUnclassified)], -- TODO Goal: ???
      inModule
        "urem0_right.c"
        urem0Right
        [("urem0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "urem1_right.c"
        urem1Right
        [("urem1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "urem_neg1_right.c"
        uremNeg1Right
        [("urem_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "urem2_right.c"
        urem2Right
        [("urem2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem0_right.c"
        srem0Right
        [("srem0_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem1_right.c"
        srem1Right
        [("srem1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem_neg1_right.c"
        sremNeg1Right
        [("srem_neg1_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem2_right.c"
        srem2Right
        [("srem2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      inModule
        "srem_neg2_right.c"
        sremNeg2Right
        [("srem_neg2_right", isSafeWithPreconditions mempty DidntHitBounds)],
      -- This one passes because they share no functions to be tested for
      -- equivalence:
      checkCrashDiff "add1_left.c" add1Left "udiv0_left.c" udiv0Left True False,
      -- This one passes because add1_left.c doesn't crash, whereas udiv0_left.c
      -- does, so the latter's crashes are a superset of the former's. We have to
      -- rename the function in add1_left.c to match, though.
      checkCrashDiff
        "udiv0_left.c"
        udiv0Left
        "add1_left.c"
        (oneArithLeft "udiv0_left" i32 (L.ValInteger 1) (L.Add False False))
        False
        False,
      -- This is the inverse of the above: udiv0_left.c *isn't* crash-less-than
      -- add1_left.c.
      checkCrashDiff
        "add1_left.c"
        (oneArithLeft "udiv0_left" i32 (L.ValInteger 1) (L.Add False False))
        "udiv0_left.c"
        udiv0Left
        True
        True,
      TQ.testProperty "Crash equivalence is reflexive" $
        \(ArithModule llvmModule) ->
          TQ.ioProperty $
            do
              (appCtx, (diffs12, diffs21)) <-
                getCrashDiff "fake1" llvmModule "fake2" llvmModule
              reportDiffs appCtx diffs12 diffs21
              pure (null diffs12 && null diffs21)
    ]

main :: IO ()
main =
  TT.defaultMain $
    TT.testGroup
      "uc-crux-llvm"
      [ Callgraph.callgraphTests,
        Check.checkOverrideTests,
        Postcond.postcondTests,
        inFileTests,
        moduleTests,
        isUnimplemented
          "read_extern_global_unsized_array.c"
          "read_extern_global_unsized_array", -- goal: isSafeWithPreconditions
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
