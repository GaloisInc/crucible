{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Mir.Language (
    main,
    mainWithExtraOverrides,
    mainWithOutputTo,
    mainWithOutputConfig,
    runTests,
    runTestsWithExtraOverrides,
    BindExtraOverridesFn,
    Crux.InitUserState(..),
    noExtraOverrides,
    orOverride,
    MIROptions(..),
    defaultMirOptions,
    MirLogging(..),
    mirLoggingToSayWhat,
    withMirLogging,
) where

import qualified Data.Aeson as Aeson
import qualified Data.BitVector.Sized as BV
import qualified Data.Char       as Char
import           Control.Monad
import           Control.Monad.IO.Class
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List       as List
import           Data.Text (Text)
import qualified Data.Text       as Text
import           Data.Type.Equality ((:~:)(..),TestEquality(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Sequence   as Seq
import           Control.Lens ((^.), (^?), (^..), ix, each)
import           GHC.Generics (Generic)

import System.Console.ANSI
import           System.IO (Handle)
import qualified SimpleGetOpt as GetOpt
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (exitSuccess, exitWith, ExitCode(..))
import           System.FilePath ((</>))

import           Prettyprinter (pretty)

import           Control.Lens (view)

--import           GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx

-- crucible
import qualified Lang.Crucible.Simulator               as C
import qualified Lang.Crucible.CFG.Core                as C
import qualified Lang.Crucible.FunctionHandle          as C
import qualified Lang.Crucible.Backend                 as C

-- what4
import qualified What4.Expr.Builder                    as W4
import qualified What4.Interface                       as W4
import qualified What4.Config                          as W4
import qualified What4.Partial                         as W4
import qualified What4.ProgramLoc                      as W4
import qualified What4.FunctionName                    as W4

-- crux
import qualified Crux
import qualified Crux.Config.Common as Crux
import qualified Crux.Log as Log
import qualified Crux.Model as Crux
import qualified Crux.UI.JS as Crux

import Crux.Types
import Crux.Log


-- concurrency
import Crucibles.DPOR
import Crucibles.Explore
import Cruces.ExploreCrux

-- crux-mir
import           Mir.Mir
import           Mir.DefId
import           Mir.PP ()
import           Mir.Overrides
import           Mir.Intrinsics (MIR, mirExtImpl, mirIntrinsicTypes,
                    pattern RustEnumRepr, SomeRustEnumRepr(..),
                    pattern MirAggregateRepr, MirAggregate(..), MirAggregateEntry(..),
                    mirAggregate_lookup)
import           Mir.Generator
import           Mir.Generate (generateMIR)
import qualified Mir.Log as Log
import           Mir.ParseTranslate (translateMIR)
import           Mir.Trans (transStatics)
import qualified Mir.TransCustom as TransCustom
import           Mir.TransTy
import           Mir.Concurrency
import qualified Paths_crux_mir (version)

defaultOutputConfig :: IO (Maybe Crux.OutputOptions -> OutputConfig MirLogging)
defaultOutputConfig = Crux.defaultOutputConfig mirLoggingToSayWhat

main :: IO ()
main = do
    mkOutCfg <- defaultOutputConfig
    exitCode <- mainWithOutputConfig Crux.noInitUserState mkOutCfg noExtraOverrides
    exitWith exitCode

mainWithExtraOverrides :: Crux.InitUserState s -> BindExtraOverridesFn s -> IO ()
mainWithExtraOverrides initS bindExtra = do
    mkOutCfg <- defaultOutputConfig
    exitCode <- mainWithOutputConfig initS mkOutCfg bindExtra
    exitWith exitCode

mainWithOutputTo :: Crux.InitUserState s -> Handle -> BindExtraOverridesFn s -> IO ExitCode
mainWithOutputTo initS h = mainWithOutputConfig initS $
    Crux.mkOutputConfig (h, False) (h, False) mirLoggingToSayWhat

data MirLogging
    = LoggingCrux Crux.CruxLogMessage
    | LoggingMir Log.MirLogMessage
    deriving (Generic, Aeson.ToJSON)

mirLoggingToSayWhat :: MirLogging -> SayWhat
mirLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
mirLoggingToSayWhat (LoggingMir msg) = Log.mirLogMessageToSayWhat msg

withMirLogging ::
    (
        ( Log.SupportsCruxLogMessage MirLogging
        , Log.SupportsMirLogMessage MirLogging
        ) => computation
    ) -> computation
withMirLogging computation =
    let ?injectCruxLogMessage = LoggingCrux
        ?injectMirLogMessage = LoggingMir
     in computation

mainWithOutputConfig ::
    Crux.InitUserState s ->
    (Maybe Crux.OutputOptions -> OutputConfig MirLogging) ->
    BindExtraOverridesFn s -> IO ExitCode
mainWithOutputConfig initS mkOutCfg bindExtra =
    withMirLogging $
    Crux.loadOptions mkOutCfg "crux-mir" Paths_crux_mir.version mirConfig
        $ runTestsWithExtraOverrides initS bindExtra

-- | This is for extra overrides to be used by the symbolic simulator.
-- The type parameter @s@ is for any custom input that might be needed by
-- the overrides.  It is simlar to the "personality" parameter @p@, it
-- is stored in the symbolick backend instead of the simulator itself.
type BindExtraOverridesFn st = forall sym bak p t fs args ret blocks rtp a r.
    (C.IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    Maybe (Crux.SomeOnlineSolver sym bak) ->
    CollectionState ->
    Text ->
    C.CFG MIR blocks args ret ->
    Maybe (C.OverrideSim (p sym) sym MIR rtp a r ())



noExtraOverrides :: BindExtraOverridesFn s
noExtraOverrides _ _ _ _ = Nothing

orOverride ::
    BindExtraOverridesFn s -> BindExtraOverridesFn s -> BindExtraOverridesFn s
orOverride f g symOnline colState name cfg =
    case f symOnline colState name cfg of
        Just x -> Just x
        Nothing -> g symOnline colState name cfg


data SomeTestOvr alg sym ctx (ty :: C.CrucibleType) =
    SomeTestOvr
    { testOvr :: Fun (CruxPersonality alg MIR ty) sym MIR ctx ty
    , testFeatures :: [C.ExecutionFeature (CruxPersonality alg MIR ty sym) sym MIR (C.RegEntry sym ty)]
    }


runTests ::
    Crux.Logs msgs =>
    Crux.SupportsCruxLogMessage msgs =>
    Log.SupportsMirLogMessage msgs =>
    (Crux.CruxOptions, MIROptions) -> IO ExitCode
runTests = runTestsWithExtraOverrides Crux.noInitUserState noExtraOverrides

runTestsWithExtraOverrides ::
    forall st msgs.
    Crux.Logs msgs =>
    Crux.SupportsCruxLogMessage msgs =>
    Log.SupportsMirLogMessage msgs =>
    Crux.InitUserState st ->
    BindExtraOverridesFn st ->
    (Crux.CruxOptions, MIROptions) ->
    IO ExitCode
runTestsWithExtraOverrides initS bindExtra (cruxOpts, mirOpts) = do
    let ?debug              = Crux.simVerbose (Crux.outputOptions cruxOpts)
    --let ?assertFalseOnError = assertFalse mirOpts
    let ?assertFalseOnError = True
    let ?printCrucible      = printCrucible mirOpts
    let ?defaultRlibsDir    = defaultRlibsDir mirOpts
    let ?customOps          = TransCustom.customOps

    let (filename, nameFilter) = case cargoTestFile mirOpts of
            -- This case is terrible a hack.  The goal is to mimic the behavior
            -- of the test binaries produced by `cargo test`, which take a test
            -- filter string as their main argument, not a filename.  Since we
            -- can't customize the way Crux parses its non-option arguments, we
            -- just let it parse its `inputFiles` argument as normal, but we
            -- treat the value as a test filter instead of a filename.  The
            -- actual input filename is taken from the `--cargo-test-file`
            -- option.
            --
            -- TODO: Write a proper "cargo-test-like" frontend that does its
            -- own argument parsing, so we can get rid of this hack and also
            -- have better `cargo test` compatibility in general.
            Just file -> case (Crux.inputFiles cruxOpts, testFilter mirOpts) of
                ([], Nothing) -> (file, Nothing)
                ([], Just filt) -> (file, Just filt)
                ([filt], Nothing) -> (file, Just $ Text.pack filt)
                ([filt1], Just filt2) -> error $
                    "expected at most 1 test filter, but got both " ++ show filt1
                        ++ " and " ++ show filt2
                (ifs, _) -> error $
                    "expected at most 1 test filter, but got " ++ show ifs

            -- In non-`--cargo-test-file` mode, the input file and
            -- `--test-filter` options are handled as normal.
            Nothing -> case Crux.inputFiles cruxOpts of
                [x] -> (x, testFilter mirOpts)
                ifs -> error $ "expected exactly 1 input file, but got " ++ show (length ifs) ++ " files"

    -- Load the MIR collection
    col <- generateMIR cruxOpts filename False

    when (onlyPP mirOpts) $ do
      -- TODO: make this exit more gracefully somehow
      print $ pretty col
      liftIO $ exitSuccess

    -- Translate to crucible
    halloc  <- C.newHandleAllocator
    mir     <- translateMIR col halloc

    C.AnyCFG staticInitCfg <- transStatics (mir ^. rmCS) halloc
    let hi = C.cfgHandle staticInitCfg
    Refl <- failIfNotEqual (C.handleArgTypes hi) Ctx.Empty
           $ "BUG: static initializer should not require arguments"

    let cfgMap = mir ^. rmCFGs

    -- Simulate each test case
    let linkOverrides :: (C.IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
           Maybe (Crux.SomeOnlineSolver sym bak) -> C.OverrideSim (p sym) sym MIR rtp a r ()
        linkOverrides symOnline =
            forM_ (Map.toList cfgMap) $ \(fn, C.AnyCFG cfg) -> do
                case bindExtra symOnline (mir ^. rmCS) fn cfg of
                    Just f -> f
                    Nothing -> bindFn symOnline (mir ^. rmCS) fn cfg
    let entry = W4.mkProgramLoc "<entry>" W4.InternalPos
    let testStartLoc fnName =
            W4.mkProgramLoc (W4.functionNameFromText $ idText fnName) (W4.OtherPos "<start>")
    let filterTests defIds = case nameFilter of
            Just x -> filter (\d -> x `Text.isInfixOf` idText d) defIds
            Nothing -> defIds
    let filterSkipTests defIds = case testSkipFilter mirOpts of
            Just x -> filter (\d -> not (x `Text.isInfixOf` idText d)) defIds
            Nothing -> defIds
    let testNames = List.sort $ filterTests $ filterSkipTests $ col ^. tests

    -- The output for each test looks like:
    --      test foo::bar1: ok
    --      test foo::bar2: FAILED
    --      test foo::bar3: returned 123, ok
    -- This mimics the output format of `cargo test`.  "test foo::bar" is
    -- printed at the top of `simTest`, `returned 123` is printed at the bottom
    -- of `simTest` (if applicable), and `ok` / `FAILED` is printed by the loop
    -- that calls `simTest`.  Counterexamples are printed separately, and only
    -- for tests that failed.

    let ?bound = 0
    let simTestBody :: forall sym bak p t fs.
            ( C.IsSymBackend sym bak
            , sym ~ W4.ExprBuilder t st fs
            ) =>
            bak ->
            Maybe (Crux.SomeOnlineSolver sym bak) ->
            DefId ->
            Fun p sym MIR Ctx.EmptyCtx C.UnitType
        simTestBody bak symOnline fnName =
          do linkOverrides symOnline
             _ <- C.callCFG staticInitCfg C.emptyRegMap

             -- Label the current path for later use
             let sym = C.backendGetSym bak
             liftIO $ C.addAssumption bak $
                 C.BranchCondition entry (Just $ testStartLoc fnName) (W4.truePred sym)

             -- Find and run the target function
             C.AnyCFG cfg <- case Map.lookup (idText fnName) cfgMap of
                 Just x -> return x
                 Nothing -> fail $ "couldn't find cfg for " ++ show fnName
             let hf = C.cfgHandle cfg
             Refl <- failIfNotEqual (C.handleArgTypes hf) Ctx.Empty $
                 "test function " ++ show fnName ++ " should not take arguments"
             resTy <- case List.find (\fn -> fn ^. fname == fnName) (col ^. functions) of
                 Just fn -> return $ fn ^. fsig.fsreturn_ty
                 Nothing -> fail $ "couldn't find return type for " ++ show fnName
             res <- C.callCFG cfg C.emptyRegMap

             -- The below are silenced when concurrency is enabled: too much output!
             -- TODO: think about if/how to present this information when concurrency
             -- is enabled.
             when (not (concurrency mirOpts) && printResultOnly mirOpts) $ do
                 str <- showRegEntry @sym col resTy res
                 liftIO $ outputLn str

             when (not (concurrency mirOpts) && not (printResultOnly mirOpts) && resTy /= TyTuple []) $ do
                 str <- showRegEntry @sym col resTy res
                 liftIO $ output $ "returned " ++ str ++ ", "

    let printTest :: DefId -> Fun p sym ext args C.UnitType
        printTest fnName =
          when (not $ printResultOnly mirOpts) $
            liftIO $ output $ "test " ++ show fnName ++ ": "

    let simTest :: forall sym bak t fs.
            ( C.IsSymBackend sym bak
            , sym ~ W4.ExprBuilder t st fs
            , Logs msgs
            , Log.SupportsCruxLogMessage msgs
            , Log.SupportsMirLogMessage msgs
            ) =>
            bak ->
            Maybe (Crux.SomeOnlineSolver sym bak) ->
            DefId ->
            SomeTestOvr DPOR sym Ctx.EmptyCtx C.UnitType
        simTest bak symOnline fnName
          | concurrency mirOpts = SomeTestOvr
            { testOvr = do printTest fnName
                           exploreOvr bak symOnline cruxOpts $ simTestBody bak symOnline fnName
            , testFeatures = [scheduleFeature @_ @DPOR mirExplorePrimitives []]
            }
          | otherwise = SomeTestOvr
            { testOvr = do printTest fnName
                           simTestBody bak symOnline fnName
            , testFeatures = []
            }

    let simCallbacks fnName =
          Crux.SimulatorCallbacks $
            return $
              Crux.SimulatorHooks
                { Crux.setupHook =
                    \bak symOnline ->
                      case simTest bak symOnline fnName of
                        SomeTestOvr testFn features -> do
                          personality <- mkCruxPersonality @DPOR
                          let outH = view outputHandle ?outputConfig
                          let sym = C.backendGetSym bak
                          setSimulatorVerbosity (Crux.simVerbose (Crux.outputOptions cruxOpts)) sym
                          let simCtx = C.initSimContext bak mirIntrinsicTypes halloc outH
                                  (C.FnBindings C.emptyHandleMap) mirExtImpl personality
                          return (Crux.RunnableStateWithExtensions
                                  (C.InitialState simCtx C.emptyGlobals C.defaultAbortHandler C.UnitRepr $
                                   C.runOverrideSim C.UnitRepr $ testFn) features
                                 )
                , Crux.onErrorHook = \_bak -> return (\_ _ -> return mempty)
                , Crux.resultHook = \_bak result -> return result
                }

    let outputResult (CruxSimulationResult cmpl gls)
          | disproved > 0 = output "FAILED"
          | cmpl /= ProgramComplete = output "UNKNOWN"
          | proved == tot = output "ok"
          | otherwise = output "UNKNOWN"
          where
            tot = sum (fmap (totalProcessedGoals . fst) gls)
            proved = sum (fmap (provedGoals . fst) gls)
            disproved = sum (fmap (disprovedGoals . fst) gls)

    results <- forM testNames $ \fnName -> do
        let cruxOpts' = cruxOpts {
                Crux.outDir = if Crux.outDir cruxOpts == "" then ""
                    else Crux.outDir cruxOpts </> caseSensitiveTag (show fnName)
            }

        -- When profiling Crucible evaluation, also save metadata about the
        -- translation.
        when (Crux.branchCoverage cruxOpts' && not (null $ Crux.outDir cruxOpts')) $ do
            createDirectoryIfMissing True (Crux.outDir cruxOpts')
            let path = Crux.outDir cruxOpts' </> "translation.json"
            -- It's a bit redundant to emit the entire crate's translation
            -- metadata for each test, but we do it anyway.  This keeps us from
            -- overwriting the metadata when multiple tests are run with the
            -- same `outDir`.
            Aeson.encodeFile path (mir ^. rmTransInfo)

            let testFile = Crux.outDir cruxOpts' </> "tests.json"
            Aeson.encodeFile testFile (map idText testNames)

        res <- Crux.runSimulatorWithUserState initS cruxOpts' $ simCallbacks fnName
        when (not $ printResultOnly mirOpts) $ do
            clearFromCursorToLineEnd
            outputResult res
            outputLn ""
        return res

    -- Print counterexamples
    let isResultOK (CruxSimulationResult comp gls) =
            comp == ProgramComplete &&
            sum (fmap (provedGoals . fst) gls) == sum (fmap (totalProcessedGoals . fst) gls)
    let anyFailed = any (not . isResultOK) results

    let printCounterexamples gs = case gs of
            Branch g1 g2 -> printCounterexamples g1 >> printCounterexamples g2
            ProvedGoal{} -> return ()
            NotProvedGoal _ _ _ _ Nothing _ -> return ()
            NotProvedGoal _ _ _ _ (Just (m,_evs)) _ -> do
               logGoal gs
               when (showModel mirOpts) $ do
                  outputLn "Model:"
                  mjs <- Crux.modelJS m
                  outputLn (Crux.renderJS mjs)

    when anyFailed $ do
        outputLn ""
        outputLn "failures:"
        forM_ (zip testNames results) $ \(fnName, res) -> do
            when (not $ isResultOK res) $ do
                outputLn ""
                outputLn $ "---- " ++ show fnName ++ " counterexamples ----"
                mapM_ (printCounterexamples . snd) $ cruxSimResultGoals res

    -- Print final tally of proved/disproved goals (except if
    -- --print-result-only is set)
    let mergeCompleteness ProgramComplete ProgramComplete = ProgramComplete
        mergeCompleteness ProgramIncomplete _ = ProgramIncomplete
        mergeCompleteness _ ProgramIncomplete = ProgramIncomplete
    let mergeResult (CruxSimulationResult c1 g1) (CruxSimulationResult c2 g2) =
            CruxSimulationResult (mergeCompleteness c1 c2) (g1 <> g2)
    let emptyResult = CruxSimulationResult ProgramComplete mempty
    let res@(CruxSimulationResult resComp resGoals) =
            foldl mergeResult emptyResult results

    let skipSummary = printResultOnly mirOpts && resComp == ProgramComplete && Seq.null resGoals
    if not skipSummary then do
        outputLn ""
        Log.sayMir Log.FinalResults
        Crux.postprocessSimResult False cruxOpts res
      else
        return ExitSuccess

-- | Add a suffix to the string, that will be different depending on the
-- cases of the letters.  We use it to avoid name collision on case
-- insensitive file systems.  The algorithm is: consider only letters,
-- create a bit string with 1 for upper case letters, turn into 5 bit numbers
-- and encode by indexing in `['a'..'z'] ++ ['0'..'6']`.  For example:
-- > "lower_case" -> "lower_case#aa"
-- > "lower_CASE" -> "lower_CASE#ap"
-- In both cases the `_` is ignored. "lower" is all lower case, which maps
-- to 0, hence we see an `a`.  "CASE" is all upper case, so we get 4 1s,
-- which is 15, which maps to `p`.
caseSensitiveTag :: String -> String
caseSensitiveTag f = f ++ "#" ++ tag f
  where
  tag = map (toChar . toNum) . chunk . map Char.isUpper . filter Char.isAlpha
  chunk xs =
    case splitAt 5 xs of
      ([],_)  -> []
      (as,bs) -> as : chunk bs
  toNum = List.foldl' addBit 0
  toChar n
    | n < 26    = toEnum (fromEnum 'a' + n)
    | otherwise = toEnum (fromEnum '0' + (n - 26))
  addBit n x =
    let n' = 2 * n
    in if x then n' + 1 else n'




data MIROptions = MIROptions
    { onlyPP       :: Bool
    , printCrucible :: Bool
    , showModel    :: Bool
    , assertFalse  :: Bool
    -- | Print only the result of evaluation, with no additional text.  On
    -- concrete programs, this should normally produce the exact same output as
    -- `rustc prog.rs && ./prog`.
    , printResultOnly :: Bool
    -- | Generate test overrides that recognize concurrency primitives
    -- and attempt to explore all interleaving executions
    , concurrency :: Bool
    , testFilter   :: Maybe Text
    , testSkipFilter :: Maybe Text
    , cargoTestFile :: Maybe FilePath
    , defaultRlibsDir :: FilePath
    -- ^ Directory to search for builds of `crux-mir`'s custom standard
    -- library, if `$CRUX_RUST_LIBRARY_PATH` is unset.  This option exists for
    -- the purposes of the `crux-mir-comp` test suite; there's no user-facing
    -- flag to set it.
    }

defaultMirOptions :: MIROptions
defaultMirOptions = MIROptions
    { onlyPP = False
    , printCrucible = False
    , showModel = False
    , assertFalse = False
    , concurrency = False
    , printResultOnly = False
    , testFilter = Nothing
    , testSkipFilter = Nothing
    , cargoTestFile = Nothing
    , defaultRlibsDir = "rlibs"
    }

mirConfig :: Crux.Config MIROptions
mirConfig = Crux.Config
    { Crux.cfgFile = pure defaultMirOptions
    , Crux.cfgEnv = []
    , Crux.cfgCmdLineFlag =
        [ GetOpt.Option []    ["print-mir"]
            "pretty-print mir and exit"
            (GetOpt.NoArg (\opts -> Right opts { onlyPP = True }))

        , GetOpt.Option []    ["print-crucible"]
            "pretty-print crucible after translation"
            (GetOpt.NoArg (\opts -> Right opts { printCrucible = True }))

        , GetOpt.Option []    ["print-result-only"]
            "print the result of evaluation and nothing else (used for concrete tests)"
            (GetOpt.NoArg (\opts -> Right opts { printResultOnly = True }))

        , GetOpt.Option ['m']  ["show-model"]
            "show model on counter-example"
            (GetOpt.NoArg (\opts -> Right opts { showModel = True }))

        , GetOpt.Option [] ["assert-false-on-error"]
            "when translation fails, assert false in output and keep going"
            (GetOpt.NoArg (\opts -> Right opts { assertFalse = True }))

        , GetOpt.Option [] ["concurrency"]
            "run with support for concurrency primitives"
            (GetOpt.NoArg (\opts -> Right opts { concurrency = True }))

        , GetOpt.Option []  ["test-filter"]
            "run only tests whose names contain this string"
            (GetOpt.ReqArg "string" (\v opts -> Right opts { testFilter = Just $ Text.pack v }))

        , GetOpt.Option []  ["test-skip-filter"]
            "run only tests whose names do not contain this string"
            (GetOpt.ReqArg "string" (\v opts -> Right opts { testSkipFilter = Just $ Text.pack v }))

        , GetOpt.Option []  ["cargo-test-file"]
            "treat trailing args as --test-filter instead of FILES, like `cargo test`; load program from this file instead (used by `cargo crux test`)"
            (GetOpt.ReqArg "file" (\v opts -> Right opts { cargoTestFile = Just v }))
        ]
    }

-------------------------------------------------------
-- maybe add these to crux, as they are not specific to MIR?
failIfNotEqual :: forall k f m a (b :: k).
                  (Monad m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise = error $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2

setSimulatorVerbosity :: (W4.IsSymExprBuilder sym) => Int -> sym -> IO ()
setSimulatorVerbosity verbosity sym = do
  verbSetting <- W4.getOptionSetting W4.verbosity (W4.getConfiguration sym)
  _ <- W4.setOpt verbSetting (toInteger verbosity)
  return ()

-------------------------------------------------------
showRegEntry :: forall sym arg p rtp args ret
   . C.IsSymInterface sym
  => Collection
  -> Ty
  -> C.RegEntry sym arg
  -> C.OverrideSim p sym MIR rtp args ret String
showRegEntry col mty (C.RegEntry tp rv) =
  case (mty,tp) of
    (TyBool, C.BoolRepr) -> return $ case W4.asConstantPred rv of
                     Just b -> if b then "true" else "false"
                     Nothing -> "Symbolic bool"

    (TyChar, C.BVRepr _w) -> return $ case W4.asBV rv of
                     Just i  -> show (Char.chr (fromInteger (BV.asUnsigned i)))
                     Nothing -> "Symbolic char"
    (TyInt USize, C.NatRepr) -> return $ case W4.asNat rv of
                     Just n -> show n
                     Nothing -> "Symbolic nat"
    (TyUint USize, C.NatRepr) -> return $ case W4.asNat rv of
                     Just n -> show n
                     Nothing -> "Symbolic nat"
    (TyInt _sz, C.BVRepr w) -> return $ case W4.asBV rv of
                     Just i  -> show (BV.asSigned w i)
                     Nothing -> "Symbolic BV"
    (TyUint _sz, C.BVRepr _w) -> return $ case W4.asBV rv of
                     Just i  -> show (BV.asUnsigned i)
                     Nothing -> "Symbolic BV"
    (TyFloat _,  C.RealValRepr) -> return $ case W4.asRational rv of
                     Just f -> show f
                     Nothing -> "Symbolic real"

    (TyTuple [], C.UnitRepr) -> return "()"

    (TyTuple tys, MirAggregateRepr) -> do
      let MirAggregate _ m = rv
      strs <- forM (zip [0..] tys) $ \(off, ty) -> do
        case IntMap.lookup off m of
          Just (MirAggregateEntry _ elemTpr elemRvPart) ->
            goMaybe ty elemTpr elemRvPart
          Nothing -> return "<uninit>"

      return $ "(" ++ List.intercalate ", " strs ++ ")"

    -- Tagged union type
    (TyAdt name _ _, _)
      | Just adt <- List.find (\(Adt n _ _ _ _ _ _) -> name == n) (col ^. adts) -> do
        optParts <- case adt ^. adtkind of
            Struct -> do
                let var = onlyVariant adt
                C.Some fctx <- case variantFields' col var of
                    Left err -> fail ("Type not supported: " ++ err)
                    Right x -> return x
                let ctx = fieldCtxType fctx
                let expectedStructTpr = C.StructRepr ctx
                Refl <-
                  case testEquality expectedStructTpr tp of
                    Just r -> pure r
                    Nothing -> fail $
                      "expected struct to have type" ++ show expectedStructTpr ++
                      ", but got " ++ show tp
                return $ Right (var, readFields fctx rv)
            Enum _ -> do
             case enumVariants col adt of
               Left err -> fail ("Type not supported: " ++ err)
               Right (SomeRustEnumRepr discrTp vctx) -> do
                let expectedEnumTpr = RustEnumRepr discrTp vctx
                Refl <-
                  case testEquality expectedEnumTpr tp of
                    Just r -> pure r
                    Nothing -> fail $
                      "expected enum to have type" ++ show expectedEnumTpr ++
                      ", but got " ++ show tp
                -- Note we don't look at the discriminant here, because mapping
                -- a discriminant value to a variant index is somewhat complex.
                -- Instead we just find the first PartExpr that's initialized.
                case findVariant vctx (C.unRV $ rv Ctx.! Ctx.i2of2) of
                    Just (C.Some (FoundVariant idx tpr fields)) -> do
                        let i = Ctx.indexVal idx
                        let var = fromMaybe (error "bad index from findVariant?") $
                                adt ^? adtvariants . ix i
                        case variantFields' col var of
                            Left err -> return (Left ("Type not supported: " ++ err))
                            Right (C.Some fctx) -> do
                                Refl <- failIfNotEqual tpr (C.StructRepr $ fieldCtxType fctx)
                                            ("when printing enum type " ++ show name)
                                return $ Right (var, readFields fctx fields)
                    Nothing -> return $ Left "Symbolic enum"
            Union -> return $ Left "union printing is not yet implemented"
        case optParts of
            Left err -> return err
            Right (var, vals) -> do
                strs <- zipWithM (\ty (C.Some entry) -> showRegEntry col ty entry)
                    (var ^.. vfields . each . fty) vals
                let varName = Text.unpack $ cleanVariantName (var ^. vname)
                case var ^. vctorkind of
                    Just FnKind -> return $ varName ++ "(" ++ List.intercalate ", " strs ++ ")"
                    Just ConstKind -> return varName
                    Nothing ->
                        let strs' = zipWith (\fn v -> case parseFieldName fn of
                                Just x -> Text.unpack x ++ ": " ++ v
                                Nothing -> v) (var ^.. vfields . each . fName) strs
                        in return $ varName ++ " { " ++ List.intercalate ", " strs' ++ " }"

    (TyRef ty Immut, _) -> showRegEntry col ty (C.RegEntry tp rv)

    (TyArray ty len, MirAggregateRepr) -> do
      case tyToRepr col ty of
        Right (C.Some tpr) -> do
          let size = 1  -- TODO: hardcoded size=1
          values <- forM [0 .. len - 1] $ \i -> do
            case mirAggregate_lookup (fromIntegral i * size) tpr rv of
              Left e -> return $ "error accessing " ++ show (pretty mty) ++ " aggregate: " ++ e
              Right partVal -> goMaybe ty tpr partVal
          return $ "[" ++ List.intercalate ", " values ++ "]"
        Left e -> return $ "error handling type " ++ show (pretty ty) ++ ": " ++ e

    _ -> return $ "I don't know how to print result of type " ++ show (pretty mty)


  where
    readFields :: FieldCtxRepr ctx -> Ctx.Assignment (C.RegValue' sym) ctx ->
        [C.Some (C.RegEntry sym)]
    readFields Ctx.Empty Ctx.Empty = []
    readFields (fctx Ctx.:> fr) (vs Ctx.:> v) =
        readFields fctx vs ++ [readField fr (C.unRV v)]

    readField :: FieldRepr tp -> C.RegValue sym tp -> C.Some (C.RegEntry sym)
    readField (FieldRepr (FkInit tpr)) rv' = C.Some (C.RegEntry tpr rv')
    readField (FieldRepr (FkMaybe tpr)) (W4.NoErr (W4.Partial _ v)) =
        C.Some (C.RegEntry tpr v)
    readField (FieldRepr (FkMaybe tpr)) (W4.Err _) =
        error $ "readField: W4.Err for type " ++ show tpr

    goMaybe ::
      Ty ->
      C.TypeRepr tp ->
      C.RegValue sym (C.MaybeType tp) ->
      C.OverrideSim p sym MIR rtp args ret String
    goMaybe ty tpr rvPart =
      case rvPart of
        W4.Unassigned -> return "<uninitialized>"
        W4.PE p rv'
          | Just True <- W4.asConstantPred p -> showRegEntry col ty $ C.RegEntry tpr rv'
          | otherwise ->return "<possibly uninitialized>"


data FoundVariant sym ctx tp where
    FoundVariant ::
        Ctx.Index ctx tp ->
        C.TypeRepr tp ->
        C.RegValue sym tp ->
        FoundVariant sym ctx tp

findVariant ::
    C.IsSymInterface sym =>
    C.CtxRepr ctx ->
    C.RegValue sym (C.VariantType ctx) ->
    Maybe (C.Some (FoundVariant sym ctx))
findVariant ctx vals = Ctx.forIndex (Ctx.size ctx)
    (\acc idx -> case vals Ctx.! idx of
        C.VB (W4.NoErr (W4.Partial p v)) | Just True <- W4.asConstantPred p ->
            Just $ C.Some $ FoundVariant idx (ctx Ctx.! idx) v
        _ -> acc) Nothing


-----------------------
