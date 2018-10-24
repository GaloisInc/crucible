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

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}


module Main(main) where

import           Control.Monad (forM_, when)
import           Control.Monad.IO.Class
import qualified Data.List       as List
import qualified Data.Text       as Text
import           Data.Type.Equality ((:~:)(..),TestEquality(..))
import qualified Data.Map.Strict as Map
import qualified Data.String     as String

import           System.IO (stdout)
import           System.Directory (listDirectory, doesFileExist, removeFile)
import           System.Exit (ExitCode(..),exitWith)
import           System.FilePath ((<.>), (</>), takeBaseName, takeExtension, splitFileName,splitExtension)
import qualified System.Process as Proc

import qualified Data.Aeson as J
import qualified Data.ByteString.Lazy as B
import           Text.PrettyPrint.ANSI.Leijen (pretty)

import           Control.Lens((^.))

import           GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Map     as MapF
import qualified Data.Parameterized.Context as Ctx

-- crucible
import qualified Lang.Crucible.Utils.MonadVerbosity    as C
import qualified Lang.Crucible.Simulator               as C
import qualified Lang.Crucible.CFG.Core                as C
import qualified Lang.Crucible.Analysis.Postdom        as C
import qualified Lang.Crucible.FunctionHandle          as C
import qualified Lang.Crucible.Backend                 as C

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
import           Mir.PP()
import           Mir.Intrinsics(MIR,mirExtImpl)
import           Mir.SAWInterface (translateMIR,generateMIR,RustModule(..))



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


showRegEntry :: forall sym arg p rtp args ret
   . C.IsSymInterface sym 
  => Ty
  -> C.RegEntry sym arg
  -> C.OverrideSim p sym MIR rtp args ret String
showRegEntry _mty (C.RegEntry tp rv) =
  case tp of 
    C.BoolRepr  -> return $ case W4.asConstantPred rv of
                     Just b -> show b
                     Nothing -> "Symbolic bool"
    C.StringRepr  -> return $ case W4.asString rv of
                     Just s -> show s
                     Nothing -> "Symbolic string"
    C.NatRepr  -> return $ case W4.asNat rv of
                     Just n -> show n
                     Nothing -> "Symbolic nat"
    (C.BVRepr _w) -> return $ case W4.asSignedBV rv of
                     Just i  -> show i
                     Nothing -> "Symbolic BV"
    C.RealValRepr  -> return $ case W4.asRational rv of
                     Just f -> show f
                     Nothing -> "Symbolic real"
                     
    C.StructRepr _ctx -> undefined

    _ -> return $ "I don't know how to print result"
  

-----------------------  

simulateMIR :: forall sym. Crux.Simulate sym CruxMIR
simulateMIR  executeCrucible (cruxOpts, _mirOpts) sym p = do
  
  setSimulatorVerbosity (Crux.simVerbose cruxOpts) sym

  let filename      = Crux.inputFile cruxOpts
  let (dir,nameExt) = splitFileName filename
  let (name,_ext)   = splitExtension nameExt

  when (Crux.simVerbose cruxOpts > 2) $
    say "Crux" $ "Generating " ++ dir </> name <.> "mir"
    
  col <- generateMIR dir name 

  when (Crux.simVerbose cruxOpts > 2) $ do
    say "Crux" $ "MIR collection" 
    putStrLn $ show (pretty col)

  res_ty <- case List.find (\fn -> fn^.fname == "::f[0]") (col^.functions) of
                   Just fn -> return (fn^.freturn_ty)
                   Nothing  -> fail "cannot find f"

  let mir = translateMIR col

  let cfgmap = rmCFGs mir

  let link :: C.OverrideSim p sym MIR rtp a r ()
      link   = forM_ cfgmap (\(C.AnyCFG cfg) -> C.bindFnHandle (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg))

  
  (C.AnyCFG f_cfg) <- case (Map.lookup (Text.pack "::f[0]") cfgmap) of
                        Just c -> return c
                        _      -> fail $ "Could not find cfg: " ++ "f"
  (C.AnyCFG a_cfg) <- case (Map.lookup (Text.pack "::ARG[0]") cfgmap) of
                        Just c -> return c
                        _      -> fail $ "Could not find cfg: " ++ "g"

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
        link
        arg <- C.callCFG a_cfg C.emptyRegMap
        res <- C.callCFG f_cfg (C.RegMap (Ctx.empty `Ctx.extend` arg))
        str <- showRegEntry @sym res_ty res
        liftIO $ putStrLn $ str
        return ()
  
  halloc <- C.newHandleAllocator
  let simctx = C.initSimContext sym MapF.empty halloc stdout C.emptyHandleMap mirExtImpl p
      simst  = C.initSimState simctx C.emptyGlobals C.defaultAbortHandler

  res <- executeCrucible simst $ C.runOverrideSim (W4.knownRepr :: C.TypeRepr C.UnitType) osim
  return $ Result res


makeCounterExamplesMIR :: Crux.Options CruxMIR -> Maybe ProvedGoals -> IO ()
makeCounterExamplesMIR _ _ = return ()
  



