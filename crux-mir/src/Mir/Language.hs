
{-# LANGUAGE ConstraintKinds #-}
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


{-# OPTIONS_GHC -Wall #-}

module Mir.Language (
    main,
    mainWithExtraOverrides,
    mainWithOutputTo,
    mainWithOutputConfig,
    runTests,
    runTestsWithExtraOverrides,
    BindExtraOverridesFn,
    noExtraOverrides,
    orOverride,
    MIROptions(..),
    defaultMirOptions,
    MirLogging(..),
    mirLoggingToSayWhat,
    withMirLogging,
    HasMirState,
    mirState
) where

import qualified Data.Aeson as Aeson
import qualified Data.BitVector.Sized as BV
import qualified Data.Char       as Char
import           Data.Functor.Const (Const(..))
import           Control.Lens ((^.), (^?), (^..), ix, each,view,lens,Lens')
import           Control.Monad
import           Control.Monad.IO.Class
import qualified Data.List       as List
import           Data.Text (Text)
import qualified Data.Text       as Text
import           Data.Type.Equality ((:~:)(..),TestEquality(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Sequence   as Seq
import qualified Data.Vector     as Vector

import           GHC.Generics (Generic)

import System.Console.ANSI
import           System.IO (Handle)
import qualified SimpleGetOpt as GetOpt
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (exitSuccess, exitWith, ExitCode(..))
import           System.FilePath ((</>))

import           Prettyprinter (pretty)

--import           GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as Ctx

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
import qualified Crucibles.ExploreTypes as Explore
import Cruces.ExploreCrux


-- crux-mir
import           Mir.Mir
import           Mir.DefId
import           Mir.PP ()
import           Mir.Overrides
import           Mir.Intrinsics (MIR, mirExtImpl, mirIntrinsicTypes,
                    pattern RustEnumRepr, SomeRustEnumRepr(..),
                    pattern MirVectorRepr, MirVector(..))
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
    exitCode <- mainWithOutputConfig mkOutCfg CruxMir noExtraOverrides
    exitWith exitCode

mainWithExtraOverrides :: p -> BindExtraOverridesFn p -> IO ()
mainWithExtraOverrides s bindExtra = do
    mkOutCfg <- defaultOutputConfig
    exitCode <- mainWithOutputConfig mkOutCfg s bindExtra
    exitWith exitCode

mainWithOutputTo ::
  Handle -> p -> BindExtraOverridesFn p -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig $
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

mainWithOutputConfig :: (Maybe Crux.OutputOptions -> OutputConfig MirLogging)
                     -> p -> BindExtraOverridesFn p -> IO ExitCode
mainWithOutputConfig mkOutCfg customState bindExtra =
    withMirLogging $
    Crux.loadOptions mkOutCfg "crux-mir" Paths_crux_mir.version mirConfig
        $ runTestsWithExtraOverrides customState bindExtra

type HasMirState p s = (MirPersonality p, MirState p ~ s)

-- | Provides access to some custom state
class MirPersonality p where
  type MirState p
  mirStateField :: Lens' p (MirState p)

newtype CruxMir s = CruxMir { cruxMirState :: s }

cruxMirNoState :: CruxMir ()
cruxMirNoState = CruxMir ()

instance MirPersonality (CruxMir s) where
  type MirState (CruxMir s) = s 
  mirStateField = lens cruxMirState (const CruxMir)

-- | This is used when we execute with concurrency
instance MirPersonality p => MirPersonality (Explore.Exploration p alg ext ret sym) where
  type MirState (Explore.Exploration p alg ext ret sym) = MirState p
  mirStateField = Explore.personality . mirStateField

mirState :: HasMirState p s => Lens' (C.SimState p sym ext r f a) s
mirState = C.stateContext . C.cruciblePersonality . mirStateField



type BindExtraOverridesFn s = forall sym bak p t st fs args ret blocks rtp a r.
    (C.IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasMirState p s) =>
    Maybe (Crux.SomeOnlineSolver sym bak) ->
    CollectionState ->
    Text ->
    C.CFG MIR blocks args ret ->
    Maybe (C.OverrideSim p sym MIR rtp a r ())

noExtraOverrides :: BindExtraOverridesFn p
noExtraOverrides _ _ _ _ = Nothing

orOverride ::
    BindExtraOverridesFn p -> BindExtraOverridesFn p -> BindExtraOverridesFn p
orOverride f g symOnline colState name cfg =
    case f symOnline colState name cfg of
        Just x -> Just x
        Nothing -> g symOnline colState name cfg


-- | This closes over the Crucible 'personality' parameter, allowing us to select between
-- normal execution over Models and concurrent exeuctions that use an Exploration
-- personality.
data SomeTestOvr sym ctx (ty :: C.CrucibleType) =
  forall personality.
    SomeTestOvr { testOvr      :: Fun personality sym MIR ctx ty
                , testFeatures :: [C.ExecutionFeature personality sym MIR (C.RegEntry sym ty)]
                , testPersonality :: personality
                }


runTests ::
    Crux.Logs msgs =>
    Crux.SupportsCruxLogMessage msgs =>
    Log.SupportsMirLogMessage msgs =>
    (Crux.CruxOptions, MIROptions) -> IO ExitCode
runTests = runTestsWithExtraOverrides cruxMirNoState noExtraOverrides

runTestsWithExtraOverrides ::
    forall s msgs.
    Crux.Logs msgs =>
    Crux.SupportsCruxLogMessage msgs =>
    Log.SupportsMirLogMessage msgs =>
    s ->
    BindExtraOverridesFn s ->
    (Crux.CruxOptions, MIROptions) ->
    IO ExitCode
runTestsWithExtraOverrides customState bindExtra (cruxOpts, mirOpts) = do
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
    col <- generateMIR filename False

    when (onlyPP mirOpts) $ do
      -- TODO: make this exit more gracefully somehow
      print $ pretty col
      liftIO $ exitSuccess

    -- Translate to crucible
    halloc  <- C.newHandleAllocator
    mir     <- translateMIR col halloc

    C.AnyCFG staticInitCfg <- transStatics (mir^.rmCS) halloc
    let hi = C.cfgHandle staticInitCfg
    Refl <- failIfNotEqual (C.handleArgTypes hi) Ctx.Empty
           $ "BUG: static initializer should not require arguments"

    let cfgMap = mir^.rmCFGs

    -- Simulate each test case
    let linkOverrides :: (C.IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasMirState p s) =>
            Maybe (Crux.SomeOnlineSolver sym bak) -> C.OverrideSim p sym MIR rtp a r ()
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
    let testNames = List.sort $ filterTests $ col ^. roots

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
    let simTestBody :: forall sym bak p t st fs.
            ( C.IsSymBackend sym bak
            , sym ~ W4.ExprBuilder t st fs
            , HasMirState p s
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
                 Just fn -> return $ fn^.fsig.fsreturn_ty
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

    let simTest :: forall sym bak t st fs.
            ( C.IsSymBackend sym bak
            , sym ~ W4.ExprBuilder t st fs
            , Logs msgs
            , Log.SupportsCruxLogMessage msgs
            , Log.SupportsMirLogMessage msgs
            ) =>
            bak ->
            Maybe (Crux.SomeOnlineSolver sym bak) ->
            DefId ->
            SomeTestOvr sym Ctx.EmptyCtx C.UnitType
        simTest bak symOnline fnName
          | concurrency mirOpts = SomeTestOvr
            { testOvr = do printTest fnName
                           exploreOvr bak symOnline cruxOpts $ simTestBody bak symOnline fnName
            , testFeatures = [scheduleFeature mirExplorePrimitives []]
            , testPersonality = emptyExploration @DPOR (CruxMir customState)
            }
          | otherwise = SomeTestOvr
            { testOvr = do printTest fnName
                           simTestBody bak symOnline fnName
            , testFeatures = []
            , testPersonality = CruxMir customState
            }

    let simCallbacks fnName =
          Crux.SimulatorCallbacks $
            return $
              Crux.SimulatorHooks
                { Crux.setupHook =
                    \bak symOnline ->
                      case simTest bak symOnline fnName of
                        SomeTestOvr testFn features personality -> do
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
                    else Crux.outDir cruxOpts </> show fnName
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

        res <- Crux.runSimulator cruxOpts' $ simCallbacks fnName
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
    (TyStr, C.StringRepr W4.UnicodeRepr) -> return $ case W4.asString rv of
                     Just s -> show s
                     Nothing -> "Symbolic string"

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

    (TyTuple tys, C.StructRepr (ctxr :: C.CtxRepr ctx)) -> do
      let rv' :: Ctx.Assignment (C.RegValue' sym) ctx
          rv' = rv

      let
          go :: forall typ. Ctx.Index ctx typ -> C.RegValue' sym typ ->
                (C.OverrideSim p sym MIR rtp args ret (Const String typ))
          go idx (C.RV elt)
            | C.MaybeRepr tpr <- ctxr Ctx.! idx = case elt of
                W4.NoErr (W4.Partial p e) | Just True <- W4.asConstantPred p -> do
                    let i   = Ctx.indexVal idx
                    let mty0 = tys !! i
                    str <- showRegEntry col mty0 (C.RegEntry tpr e)
                    return (Const str)
                _ -> return $ Const $ "symbolic tuple element"
            | otherwise = error $ "expected MaybeRepr, but got " ++ show (ctxr Ctx.! idx)

      (cstrs :: Ctx.Assignment (Const String) ctx) <- Ctx.traverseWithIndex go rv'
      let strs = Ctx.toListFC (\(Const str) -> str) cstrs
      return $ "(" ++ List.intercalate ", " strs ++ ")"

    -- Tagged union type
    (TyAdt name _ _, _)
      | Just adt <- List.find (\(Adt n _ _ _ _ _ _) -> name == n) (col^.adts) -> do
        optParts <- case adt^.adtkind of
            Struct -> do
                let var = onlyVariant adt
                C.Some fctx <- return $ variantFields' col var
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
                SomeRustEnumRepr discrTp vctx <- return $ enumVariants col adt
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
                        C.Some fctx <- return $ variantFields' col var
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
                let varName = Text.unpack $ cleanVariantName (var^.vname)
                case var ^. vctorkind of
                    Just FnKind -> return $ varName ++ "(" ++ List.intercalate ", " strs ++ ")"
                    Just ConstKind -> return varName
                    Nothing ->
                        let strs' = zipWith (\fn v -> case parseFieldName fn of
                                Just x -> Text.unpack x ++ ": " ++ v
                                Nothing -> v) (var ^.. vfields . each . fName) strs
                        in return $ varName ++ " { " ++ List.intercalate ", " strs' ++ " }"

{-
            Enum -> do
                C.Some enumCtx <- return $ enumVariants adt args
                C.AnyValue anyTpr anyVal <- return rv
                Refl <- case testEquality anyTpr (RustEnumRepr enumCtx) of
                    Just refl -> return refl
                    Nothing -> fail $ "bad ANY unpack for " ++ show mty ++ ": expected " ++
                        show (RustEnumRepr enumCtx) ++ ", but got " ++ show anyTpr

        case W4.asUnsignedBV (C.unRV $ anyVal Ctx.! Ctx.i1of2) of
            Nothing -> return $ "Symbolic ADT: " ++ show name
            Just discr -> do
                let var = case adt ^? adtvariants . ix (fromIntegral discr) of
                        Just x -> x
                        Nothing -> error $ "variant index " ++ show discr ++ " out of range for " ++ show name
                return $ show name ++ ", variant " ++ show (var ^. vname)
-}


      {-
      let rv' :: Ctx.Assignment (C.RegValue' sym) (Ctx.EmptyCtx Ctx.::> C.NatType Ctx.::> C.AnyType)
          rv' = rv
      let kv = rv'  Ctx.! Ctx.i1of2
      case W4.asNat (C.unRV kv) of
        Just k  -> do
          let var = variants !! (fromInteger (toInteger k))
          case rv'  Ctx.! Ctx.i2of2 of
            (C.RV (C.AnyValue (C.StructRepr (ctxr :: C.CtxRepr ctx)) (av :: Ctx.Assignment (C.RegValue' sym) ctx))) -> do
              let goField :: forall typ. Ctx.Index ctx typ -> C.RegValue' sym typ
                          -> (C.OverrideSim p sym MIR rtp args ret (Const String typ))
                  goField idx (C.RV elt) = do
                    let (Field fName fty _fsubst) = (var^.vfields) !! (Ctx.indexVal idx)
                        cty0   = ctxr Ctx.! idx
                    str <- showRegEntry col fty (C.RegEntry cty0 elt)
                    case parseFieldName fName of
                      Just fn -> case Read.readMaybe (Text.unpack fn) of
                                        Just (_x :: Int) -> return $ (Const $ str)
                                        _  -> return $ (Const $ (Text.unpack fn) ++ ": " ++ str)
                      _       -> return $ (Const str)
              cstrs <- Ctx.traverseWithIndex goField av
              let strs = Ctx.toListFC (\(Const str) -> str) cstrs
              let body = List.intercalate ", " strs
              if Char.isDigit (head body) then
                return $ Text.unpack (cleanVariantName (var^.vname)) ++ "(" ++ body  ++ ")"
              else
                return $ Text.unpack (cleanVariantName (var^.vname)) ++ " { " ++ body ++ " }"
            _ -> fail "invalide representation of ADT"
        Nothing -> return $ "Symbolic ADT:" ++ show name
-}

    (TyRef ty Immut, _) -> showRegEntry col ty (C.RegEntry tp rv)

    (TyArray ty _sz, MirVectorRepr tyr) -> do
      values <- case rv of
        MirVector_Vector v -> forM (Vector.toList v) $ \val -> do
            showRegEntry col ty $ C.RegEntry tyr val
        MirVector_PartialVector pv -> forM (Vector.toList pv) $ \partVal -> case partVal of
            W4.Unassigned -> return "<uninitialized>"
            W4.PE p v | Just True <- W4.asConstantPred p ->
                showRegEntry col ty $ C.RegEntry tyr v
            W4.PE _ _ | otherwise -> return "<possibly uninitialized>"
        MirVector_Array _ -> return ["<symbolic array...>"]
      return $ "[" ++ List.intercalate ", " values ++ "]"

    (TyStr, C.VectorRepr tyr) -> do
      let entries = Vector.map (C.RegEntry tyr) rv
      values <- Vector.mapM (showRegEntry col TyChar) entries
      let strs = Vector.toList values
      return $ concat strs

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
