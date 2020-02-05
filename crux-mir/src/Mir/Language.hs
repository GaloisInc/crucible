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

{-# OPTIONS_GHC -Wall #-}

module Mir.Language (main,  mainWithOutputTo,
                     mirLanguage,
                     MIROptions(..),
                     defaultMirOptions) where

import qualified Data.Char       as Char
import qualified Data.Foldable as Fold
import           Data.Functor.Const (Const(..))
import           Control.Monad (forM_, when, unless, zipWithM)
import           Control.Monad.IO.Class
import qualified Data.List       as List
import qualified Data.Text       as Text
import           Data.Type.Equality ((:~:)(..),TestEquality(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Sequence   as Seq
import qualified Data.Vector     as Vector
import           Control.Lens ((^.), (^?), (^..), ix, each)

import           System.IO (Handle)
import qualified SimpleGetOpt as GetOpt
import           System.Exit (exitSuccess, exitWith, ExitCode)

import           Text.PrettyPrint.ANSI.Leijen (pretty)

import           Control.Lens (view)

--import           GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as Ctx

-- crucible
import qualified Lang.Crucible.Simulator               as C
import qualified Lang.Crucible.Simulator.PathSplitting as C
import qualified Lang.Crucible.CFG.Core                as C
import qualified Lang.Crucible.FunctionHandle          as C
import qualified Lang.Crucible.Backend                 as C

-- what4
import qualified What4.Interface                       as W4
import qualified What4.Config                          as W4
import qualified What4.Partial                         as W4

-- crux
import qualified Crux as Crux
import qualified Crux.Config.Common as Crux
import qualified Crux.Model as Crux

import Crux.Types
import Crux.Log


-- mir-verifier
import           Mir.Mir
import           Mir.PP ()
import           Mir.Overrides
import           Mir.Intrinsics (MIR, mirExtImpl, mirIntrinsicTypes,
                    pattern RustEnumRepr)
import           Mir.DefId (cleanVariantName, parseFieldName, idText)
import           Mir.Generator
import           Mir.Generate (generateMIR, translateMIR)
import           Mir.Trans (transStatics)
import           Mir.TransTy

main :: IO ()
main = Crux.main mirLanguage >>= exitWith

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = Crux.mainWithOutputConfig (OutputConfig False h h False) mirLanguage


mirLanguage :: Crux.Language MIROptions
mirLanguage = Crux.Language
    { Crux.name = "mir"
    , Crux.version = "0.1"
    , Crux.configuration = mirConfig
    , Crux.initialize = return
    , Crux.simulate = simulateMIR
    , Crux.makeCounterExamples = makeCounterExamplesMIR
    }


data MIROptions = MIROptions
    { onlyPP       :: Bool
    , printCrucible :: Bool
    , showModel    :: Bool
    , assertFalse  :: Bool
    }

defaultMirOptions :: MIROptions
defaultMirOptions = MIROptions
    { onlyPP = False
    , printCrucible = False
    , showModel = False
    , assertFalse = False
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

        , GetOpt.Option ['m']  ["show-model"]
            "show model on counter-example"
            (GetOpt.NoArg (\opts -> Right opts { showModel = True }))

        , GetOpt.Option [] ["assert-false-on-error"]
            "when translation fails, assert false in output and keep going"
            (GetOpt.NoArg (\opts -> Right opts { assertFalse = True }))
        ]
    }



-- | Main function for running the simulator,
-- This should only be called by crux's 'check' function. 
simulateMIR :: (?outputConfig :: OutputConfig) => Crux.SimulateCallback MIROptions
simulateMIR execFeatures (cruxOpts, mirOpts) (sym :: sym) initModel cont = do
  let ?debug              = Crux.simVerbose cruxOpts
  --let ?assertFalseOnError = assertFalse mirOpts
  let ?assertFalseOnError = True
  let ?printCrucible      = printCrucible mirOpts
  let filename            = case Crux.inputFiles cruxOpts of
        [x] -> x
        ifs -> error $ "expected exactly 1 input file, but got " ++ show (length ifs) ++ " files"

  col <- generateMIR filename False

  when (onlyPP mirOpts) $ do
    -- TODO: make this exit more gracefully somehow
    print $ pretty col
    liftIO $ exitSuccess

  halloc  <- C.newHandleAllocator
  mir     <- translateMIR mempty col halloc
                    
  C.AnyCFG init_cfg <- transStatics (mir^.rmCS) halloc
  let hi = C.cfgHandle init_cfg
  Refl <- failIfNotEqual (C.handleArgTypes hi)   (W4.knownRepr :: C.CtxRepr Ctx.EmptyCtx)
         $ "Checking input to initializer"

  let cfgmap = mir^.rmCFGs

  setSimulatorVerbosity (Crux.simVerbose cruxOpts) sym

  -- overrides
  let link :: C.OverrideSim (Model sym) sym MIR rtp a r ()
      link   = forM_ (Map.toList cfgmap) $
                 \(fn, C.AnyCFG cfg) -> bindFn fn cfg

  let
     osim :: Fun sym MIR Ctx.EmptyCtx C.UnitType
     osim   = do
        link
        _   <- C.callCFG init_cfg C.emptyRegMap
        forM_ @_ @_ @_ @() (col ^. roots) $ \fnName -> do
            (C.AnyCFG f_cfg) <- case (Map.lookup (idText fnName) cfgmap) of
                                  Just c -> return c
                                  _      -> fail $ "Could not find cfg: " ++ show fnName
            let hf = C.cfgHandle f_cfg
            Refl <- failIfNotEqual (C.handleArgTypes hf) (W4.knownRepr :: C.CtxRepr Ctx.EmptyCtx)
                   $ "Checking input to ARG"

            res <- C.callCFG f_cfg C.emptyRegMap
            res_ty <- case List.find (\fn -> fn^.fname == fnName) (col^.functions) of
                             Just fn -> return (fn^.fsig.fsreturn_ty)
                             Nothing  -> fail $ "cannot find " ++ show fnName
            if length (col^.roots) > 1 then do
                str <- if res_ty /= TyTuple [] then showRegEntry @sym col res_ty res else return "OK"
                liftIO $ outputLn $ show fnName ++ ": " ++ str
            else do
                -- This case is mainly for concrete evaluation tests, where the
                -- output get checked against the fmt::Debug rendering.
                str <- showRegEntry @sym col res_ty res
                liftIO $ outputLn $ str

  let outH = view outputHandle ?outputConfig
  let simctx = C.initSimContext sym mirIntrinsicTypes halloc outH C.emptyHandleMap mirExtImpl initModel

  let initSt = C.InitialState simctx C.emptyGlobals C.defaultAbortHandler C.UnitRepr $
           C.runOverrideSim C.UnitRepr osim

  case Crux.pathStrategy cruxOpts of
    Crux.AlwaysMergePaths ->
      do res <- C.executeCrucible (map C.genericToExecutionFeature execFeatures) initSt
         cont (Result res)
    Crux.SplitAndExploreDepthFirst ->
      do (i,ws) <- C.executeCrucibleDFSPaths (map C.genericToExecutionFeature execFeatures) initSt (cont . Result)
         say "Crux" ("Total paths explored: " ++ show i)
         unless (null ws) $
           sayWarn "Crux" (unwords [show (Seq.length ws), "paths remaining not explored: program might not be fully verified"])


makeCounterExamplesMIR :: (?outputConfig :: OutputConfig) => Crux.CounterExampleCallback MIROptions
makeCounterExamplesMIR (_cruxOpts, mirOpts) = mapM_ go . Fold.toList
  where
    go gs =
      case gs of
        AtLoc _ _ gs1 -> go gs1
        Branch g1 g2 -> go g1 >> go g2
        Goal _ (c, _) _ res ->
          let msg = show c
          in case res of
               NotProved (Just m) ->
                 do sayFail "Crux" ("Failure for " ++ msg)
                    when (showModel mirOpts) $ do
                       putStrLn "Model:"
                       putStrLn (Crux.ppModelJS "." m)
               _ -> return ()

-------------------------------------------------------
-- maybe add these to crux, as they are not specific to MIR?
failIfNotEqual :: forall f m a (b :: k).
                  (Monad m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise = fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2

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

    (TyChar, C.BVRepr _w) -> return $ case W4.asUnsignedBV rv of
                     Just i  -> show (Char.chr (fromInteger i))
                     Nothing -> "Symbolic char"
    (TyInt USize, C.NatRepr) -> return $ case W4.asNat rv of
                     Just n -> show n
                     Nothing -> "Symbolic nat"
    (TyUint USize, C.NatRepr) -> return $ case W4.asNat rv of
                     Just n -> show n
                     Nothing -> "Symbolic nat"
    (TyInt _sz, C.BVRepr _w) -> return $ case W4.asSignedBV rv of
                     Just i  -> show i
                     Nothing -> "Symbolic BV"
    (TyUint _sz, C.BVRepr _w) -> return $ case W4.asUnsignedBV rv of
                     Just i  -> show i
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
                C.Some fctx <- return $ variantFields' var mempty
                let ctx = fieldCtxType fctx
                let fields = unpackAnyValue rv (C.StructRepr ctx)
                return $ Right (var, readFields fctx fields)
            Enum -> do
                C.Some vctx <- return $ enumVariants adt mempty
                let enumVal = unpackAnyValue rv (RustEnumRepr vctx)
                -- Note we don't look at the discriminant here, because mapping
                -- a discriminant value to a variant index is somewhat complex.
                -- Instead we just find the first PartExpr that's initialized.
                case findVariant vctx (C.unRV $ enumVal Ctx.! Ctx.i2of2) of
                    Just (C.Some (FoundVariant idx tpr fields)) -> do
                        let i = Ctx.indexVal idx
                        let var = fromMaybe (error "bad index from findVariant?") $
                                adt ^? adtvariants . ix i
                        C.Some fctx <- return $ variantFields' var mempty
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

    (TyArray ty _sz, C.VectorRepr tyr) -> do
      -- rv is a Vector (RegValue tyr)
      let entries = Vector.map (C.RegEntry tyr) rv
      values <- Vector.mapM (showRegEntry col ty) entries
      let strs = Vector.toList values
      return $ "[" ++ List.intercalate ", " strs ++ "]"

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
