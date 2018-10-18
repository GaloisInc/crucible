{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}


module Main(main) where

import           Control.Monad (forM_, when)
import           Control.Monad.IO.Class
import qualified Data.Text       as Text
import           Data.Type.Equality ((:~:)(..),TestEquality(..))
import qualified Data.Map.Strict as Map

import           System.IO (stdout)
import           System.Directory (listDirectory, doesFileExist, removeFile)
import           System.Exit (ExitCode(..),exitWith)
import           System.FilePath ((<.>), (</>), takeBaseName, takeExtension, splitFileName,splitExtension)
import qualified System.Process as Proc

import           Text.PrettyPrint.ANSI.Leijen (pretty)

-- parameterized-utils
import qualified Data.Parameterized.Map     as MapF
import qualified Data.Parameterized.Context as Ctx

-- crucible
import qualified Lang.Crucible.Utils.MonadVerbosity    as C
import qualified Lang.Crucible.Simulator               as C
import qualified Lang.Crucible.CFG.Core                as C
import qualified Lang.Crucible.Analysis.Postdom        as C
import qualified Lang.Crucible.FunctionHandle          as C

-- what4
import qualified What4.Interface                       as W4
import qualified What4.Config                          as W4

-- crux
import qualified Crux.Language as Crux
import qualified Crux.CruxMain as Crux
import qualified Crux.Error    as Crux
import qualified Crux.Options  as Crux

import Crux.Types
import Crux.Model
import Crux.Log

-- mir-verifier
import           Mir.Mir
import           Mir.Intrinsics(MIR,mirExtImpl)
import           Mir.SAWInterface (loadMIR,RustModule(..))



-- | Main defers to crux to begin
main :: IO ()
main = Crux.main [Crux.LangConf (Crux.defaultOptions @CruxMIR)]

data CruxMIR
instance Crux.Language CruxMIR where
  name = "mir"
  validExtensions = [".rs", ".rslib" ]

  type LangError CruxMIR = ()
  formatError  _ = ""

  data LangOptions CruxMIR = MIROptions
     {
     }

  defaultOptions = MIROptions
    {
    }

  envOptions = []

  simulate = simulateMIR

  makeCounterExamples = makeCounterExamplesMIR


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

printRegEntry :: forall sym tp. (W4.IsExpr (W4.SymExpr sym)) => C.RegEntry sym tp -> IO ()
printRegEntry (C.RegEntry tp rv) =
  case tp of 
    C.BoolRepr  ->
      putStrLn $ show (W4.printSymExpr rv)
    C.StringRepr  ->
      putStrLn $ show (W4.printSymExpr rv)
    C.NatRepr  ->
      putStrLn $ show (W4.printSymExpr rv)
    (C.BVRepr _w) ->
      case W4.asSignedBV rv of
        Just i -> putStrLn $ show i
        _      -> error "showBV, not an int-like type"
    C.RealValRepr  ->
      putStrLn $ show (W4.printSymExpr rv)

    _ -> say "Crux" "I don't know how to print result"
  
-----------------------  

simulateMIR :: forall sym. Crux.Simulate sym CruxMIR
simulateMIR  executeCrucible (cruxOpts, _mirOpts) sym p = do
  
  setSimulatorVerbosity (Crux.simVerbose cruxOpts) sym

  let filename      = Crux.inputFile cruxOpts
  let (dir,nameExt) = splitFileName filename
  let (name,_ext)   = splitExtension nameExt

  when (Crux.simVerbose cruxOpts > 2) $
    say "Crux" $ "Generating " ++ dir </> name <.> "mir"
    
  exitCode <- generateMIR dir name
  case exitCode of
    ExitFailure _ -> do
        say "Crux" "Mir generation failed"
        exitWith exitCode
    ExitSuccess   -> return ()

  mir <- loadMIR (dir </> name <.> "mir")

  let mname = "main"

  let cfgmap = rmCFGs mir
      _link  = forM_ cfgmap (\(C.AnyCFG cfg) -> C.bindFnHandle (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg))

  
  (C.AnyCFG f_cfg) <- case (Map.lookup (Text.pack "f") cfgmap) of
                        Just c -> return c
                        _      -> fail $ "Could not find cfg: " ++ mname
  (C.AnyCFG a_cfg) <- case (Map.lookup (Text.pack "ARG") cfgmap) of
                        Just c -> return c
                        _      -> fail $ "Could not find cfg: " ++ mname

  when (Crux.simVerbose cruxOpts > 2) $ do
    say "Crux" "f CFG"
    print $ C.ppCFG True f_cfg
    say "Crux" "ARG CFG"
    print $ C.ppCFG True a_cfg

  let hf = C.cfgHandle f_cfg
  let ha = C.cfgHandle a_cfg
  
  Refl <- failIfNotEqual (C.handleArgTypes ha)   (W4.knownRepr :: C.CtxRepr Ctx.EmptyCtx)
         $ "Checking input to ARG" 
  Refl <- failIfNotEqual (C.handleArgTypes hf) (Ctx.empty `Ctx.extend` C.handleReturnType ha)
         $ "Checking agreement between f and ARG" 

  let
     osim :: Fun sym MIR Ctx.EmptyCtx C.UnitType
     osim   = do
        arg  <- C.callCFG a_cfg C.emptyRegMap
        res <- C.callCFG f_cfg (C.RegMap (Ctx.empty `Ctx.extend` arg))
        liftIO $ printRegEntry @sym res
        return ()
  
  halloc <- C.newHandleAllocator
  let simctx = C.initSimContext sym MapF.empty halloc stdout C.emptyHandleMap mirExtImpl p
      simst  = C.initSimState simctx C.emptyGlobals C.defaultAbortHandler

  res <- executeCrucible simst $ C.runOverrideSim (W4.knownRepr :: C.TypeRepr C.UnitType) osim
  return $ Result res


makeCounterExamplesMIR :: Crux.Options CruxMIR -> Maybe ProvedGoals -> IO ()
makeCounterExamplesMIR _ _ = return ()
  

-- | Run mir-json on the input
generateMIR :: FilePath -> String -> IO ExitCode
generateMIR dir name = do
  let rustFile = dir </> name <.> "rs" 
  doesFileExist rustFile >>= \case
    True -> return ()
    False -> say "Crux" $ "Cannot find input file " ++ rustFile

  (ec, _, _) <- Proc.readProcessWithExitCode "mir-json"
    [rustFile, "--crate-type", "lib"] ""
  let rlibFile = ("lib" ++ name) <.> "rlib"
  doesFileExist rlibFile >>= \case
    True  -> removeFile rlibFile
    False -> return ()

  return ec


