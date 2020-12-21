{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

module Mir.Language (main, mainWithOutputTo, mainWithOutputConfig, runTests,
                     MIROptions(..), defaultMirOptions) where

import qualified Data.Aeson as Aeson
import qualified Data.BitVector.Sized as BV
import qualified Data.Char       as Char
import           Data.Functor.Const (Const(..))
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
import           Control.Lens ((^.), (^?), (^..), ix, each)

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
import qualified Data.Parameterized.TraversableFC as Ctx

-- crucible
import qualified Lang.Crucible.Simulator               as C
import qualified Lang.Crucible.CFG.Core                as C
import qualified Lang.Crucible.FunctionHandle          as C
import qualified Lang.Crucible.Backend                 as C

-- what4
import qualified What4.Interface                       as W4
import qualified What4.Config                          as W4
import qualified What4.Partial                         as W4
import qualified What4.ProgramLoc                      as W4
import qualified What4.FunctionName                    as W4

-- crux
import qualified Crux as Crux
import qualified Crux.Model as Crux
import qualified Crux.UI.JS as Crux

import Crux.Goal (countProvedGoals, countDisprovedGoals, countTotalGoals)
import Crux.Types
import Crux.Log


-- crux-mir
import           Mir.Mir
import           Mir.DefId
import           Mir.PP ()
import           Mir.Overrides
import           Mir.Intrinsics (MIR, mirExtImpl, mirIntrinsicTypes,
                    pattern RustEnumRepr, pattern MirVectorRepr, MirVector(..))
import           Mir.Generator
import           Mir.Generate (generateMIR, translateMIR)
import           Mir.Trans (transStatics)
import           Mir.TransTy

main :: IO ()
main = mainWithOutputConfig defaultOutputConfig >>= exitWith

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig (OutputConfig False h h False)

mainWithOutputConfig :: OutputConfig -> IO ExitCode
mainWithOutputConfig outCfg =
    Crux.loadOptions outCfg "crux-mir" "0.1" mirConfig $ runTests

runTests :: (Crux.Logs) => (Crux.CruxOptions, MIROptions) -> IO ExitCode
runTests (cruxOpts, mirOpts) = do
    let ?debug              = Crux.simVerbose cruxOpts
    --let ?assertFalseOnError = assertFalse mirOpts
    let ?assertFalseOnError = True
    let ?printCrucible      = printCrucible mirOpts

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
    mir     <- translateMIR mempty col halloc

    C.AnyCFG staticInitCfg <- transStatics (mir^.rmCS) halloc
    let hi = C.cfgHandle staticInitCfg
    Refl <- failIfNotEqual (C.handleArgTypes hi) Ctx.Empty
           $ "BUG: static initializer should not require arguments"

    let cfgMap = mir^.rmCFGs

    -- Simulate each test case
    let linkOverrides :: C.IsSymInterface sym =>
            Maybe (Crux.SomeOnlineSolver sym) -> C.OverrideSim (Model sym) sym MIR rtp a r ()
        linkOverrides symOnline =
            forM_ (Map.toList cfgMap) $ \(fn, C.AnyCFG cfg) -> bindFn symOnline fn cfg
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

    let simTest :: forall sym. (C.IsSymInterface sym, Crux.Logs) =>
            Maybe (Crux.SomeOnlineSolver sym) -> DefId -> Fun Model sym MIR Ctx.EmptyCtx C.UnitType
        simTest symOnline fnName = do
            when (not $ printResultOnly mirOpts) $
                liftIO $ output $ "test " ++ show fnName ++ ": "

            linkOverrides symOnline
            _ <- C.callCFG staticInitCfg C.emptyRegMap

            -- Label the current path for later use
            sym <- C.getSymInterface
            liftIO $ C.addAssumption sym $ C.LabeledPred (W4.truePred sym) $
                C.ExploringAPath entry (Just $ testStartLoc fnName)

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

            when (printResultOnly mirOpts) $ do
                str <- showRegEntry @sym col resTy res
                liftIO $ outputLn str

            when (not (printResultOnly mirOpts) && resTy /= TyTuple []) $ do
                str <- showRegEntry @sym col resTy res
                liftIO $ output $ "returned " ++ str ++ ", "

    let simCallback fnName = Crux.SimulatorCallback $ \sym symOnline -> do
            let outH = view outputHandle ?outputConfig
            setSimulatorVerbosity (Crux.simVerbose cruxOpts) sym
            let simCtx = C.initSimContext sym mirIntrinsicTypes halloc outH
                    C.emptyHandleMap mirExtImpl Crux.emptyModel
            return (Crux.RunnableState $
                    C.InitialState simCtx C.emptyGlobals C.defaultAbortHandler C.UnitRepr $
                     C.runOverrideSim C.UnitRepr $ simTest symOnline fnName
                   , \_ _ -> return mempty
                   )

    let outputResult (CruxSimulationResult cmpl (fmap snd -> gls))
          | disproved > 0 = output "FAILED"
          | cmpl /= ProgramComplete = output "UNKNOWN"
          | proved == tot = output "ok"
          | otherwise = output "UNKNOWN"
          where
            tot = sum (fmap countTotalGoals gls)
            proved = sum (fmap countProvedGoals gls)
            disproved = sum (fmap countDisprovedGoals gls)

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

        res <- Crux.runSimulator cruxOpts' $ simCallback fnName
        when (not $ printResultOnly mirOpts) $ do
            clearFromCursorToLineEnd
            outputResult res
            outputLn ""
        return res

    -- Print counterexamples
    let isResultOK (CruxSimulationResult comp (fmap snd -> gls)) =
            comp == ProgramComplete &&
            sum (fmap countProvedGoals gls) == sum (fmap countTotalGoals gls)
    let anyFailed = any (not . isResultOK) results

    let printCounterexamples gs = case gs of
            AtLoc _ _ gs1 -> printCounterexamples gs1
            Branch g1 g2 -> printCounterexamples g1 >> printCounterexamples g2
            Goal _ (c, _) _ res ->
                let msg = show c
                in case res of
                    NotProved _ (Just m) -> do
                        outputLn ("Failure for " ++ msg)
                        when (showModel mirOpts) $ do
                           outputLn "Model:"
                           mjs <- Crux.modelJS m
                           outputLn (Crux.renderJS mjs)
                    _ -> return ()
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
        Crux.postprocessSimResult cruxOpts res
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
    , testFilter   :: Maybe Text
    , cargoTestFile :: Maybe FilePath
    }

defaultMirOptions :: MIROptions
defaultMirOptions = MIROptions
    { onlyPP = False
    , printCrucible = False
    , showModel = False
    , assertFalse = False
    , printResultOnly = False
    , testFilter = Nothing
    , cargoTestFile = Nothing
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
    (TyAdt name _ _, C.AnyRepr)
      | Just adt <- List.find (\(Adt n _ _ _ _) -> name == n) (col^.adts) -> do
        optParts <- case adt^.adtkind of
            Struct -> do
                let var = onlyVariant adt
                C.Some fctx <- return $ variantFields' var
                let ctx = fieldCtxType fctx
                let fields = unpackAnyValue rv (C.StructRepr ctx)
                return $ Right (var, readFields fctx fields)
            Enum -> do
                C.Some vctx <- return $ enumVariants adt
                let enumVal = unpackAnyValue rv (RustEnumRepr vctx)
                -- Note we don't look at the discriminant here, because mapping
                -- a discriminant value to a variant index is somewhat complex.
                -- Instead we just find the first PartExpr that's initialized.
                case findVariant vctx (C.unRV $ enumVal Ctx.! Ctx.i2of2) of
                    Just (C.Some (FoundVariant idx tpr fields)) -> do
                        let i = Ctx.indexVal idx
                        let var = fromMaybe (error "bad index from findVariant?") $
                                adt ^? adtvariants . ix i
                        C.Some fctx <- return $ variantFields' var
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
                    FnKind -> return $ varName ++ "(" ++ List.intercalate ", " strs ++ ")"
                    ConstKind -> return varName
                    FictiveKind ->
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
    unpackAnyValue :: C.AnyValue sym -> C.TypeRepr tp -> C.RegValue sym tp
    unpackAnyValue (C.AnyValue tpr val) tpr'
      | Just Refl <- testEquality tpr tpr' = val
      | otherwise = error $ "bad ANY unpack for " ++ show mty ++ ": expected" ++
        show tpr' ++ ", but got " ++ show tpr

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
