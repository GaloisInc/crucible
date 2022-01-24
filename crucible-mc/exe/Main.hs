{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module           : Main
-- Description      : Run the Crucible model-checker backend
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Main
  ( main,
  )
where

import Control.Exception (Exception (..), throwIO)
import Control.Lens ((^.))
import Crux.LLVM.Overrides (ArchOk)
import qualified Data.LLVM.BitCode as BC
import Data.Parameterized.Nonce (withIONonceGenerator)
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.FunctionHandle
import Lang.Crucible.LLVM.MemModel (mkMemVar, withPtrWidth)
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.ModelChecker.CrucibleMC (runCrucibleMC)
import System.Console.GetOpt (ArgOrder (..), getOpt)
import System.Environment (getArgs)
import qualified Text.LLVM as LLVM
import What4.ProblemFeatures (noFeatures)
import Lang.Crucible.Types(TypeRepr(..))
import Lang.Crucible.Backend.Online
          ( Z3OnlineBackend, withZ3OnlineBackend, UnsatFeatures(..)
          , Flags, FloatIEEE, FloatModeRepr(..)
          )
import Lang.Crucible.Backend(IsSymInterface)
import Lang.Crucible.CFG.Core(AnyCFG(..),cfgArgTypes,cfgReturnType)
import Lang.Crucible.Simulator
import What4.ProblemFeatures ( noFeatures )

import Lang.Crucible.LLVM.MemModel(defaultMemOptions)
import Lang.Crucible.LLVM.Run

import Crux.LLVM.Simulate( registerFunctions )
import Crux.Model

import Print

test_file :: FilePath
test_file = "crucible-mc/test/example.bc"

test_fun :: String
test_fun = "f"

main :: IO ()
main =
  parseLLVM test_file                       >>= \llvm_mod ->
  withZ3                                    $ \sym ->
  runCruxLLVM llvm_mod defaultMemOptions False False $
  CruxLLVM                                  $ \mt ->
  withPtrWidthOf mt                         $
  case findCFG mt test_fun of
    Nothing -> throwIO (UnknownFunction test_fun)
    Just (AnyCFG cfg) ->
      case (cfgArgTypes cfg, cfgReturnType cfg) of
        (Empty, UnitRepr) ->
          let ?recordLLVMAnnotation = \_ _ _ -> pure () in
               pure Setup
                 { cruxOutput = stdout
                 , cruxBackend = sym
                 , cruxInitCodeReturns = UnitRepr
                 , cruxInitCode = do registerFunctions llvm_mod mt
                                     _ <- callCFG cfg emptyRegMap
                                     pure ()
                 , cruxUserState = emptyModel
                 , cruxGo  = runFrom
                 }

        _ -> throwIO (UnsupportedFunType test_fun)

runFrom :: (IsSymInterface sym, HasPtrWidth (ArchWidth arch)) =>
            ExecState p sym (LLVM arch) rtp ->  IO ()
runFrom st =
  do print (ppExecState st)
     _ <- getLine
     st1 <- singleStepCrucible 5 st
     runFrom st1

withPtrWidthOf :: ModuleTranslation arch -> (ArchOk arch => b) -> b
withPtrWidthOf trans k =
  llvmPtrWidth (trans ^. transContext) (\ptrW -> withPtrWidth ptrW k)

-- | Create a Z3 backend for the simulator.
withZ3 ::
  (forall s. Online.Z3OnlineBackend s (Online.Flags Online.FloatIEEE) -> IO a) ->
  IO a
withZ3 k =
  withIONonceGenerator $ \nonceGen ->
    Online.withZ3OnlineBackend Online.FloatIEEERepr nonceGen Online.ProduceUnsatCores noFeatures k

-- | This exception is thrown when we fail to parse a bit-code file.
data Err
  = BitcodeError BC.Error
  | UnknownFunction String
  | UnsupportedFunType String
  deriving (Show)

instance Exception Err

-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO LLVM.Module
parseLLVM file =
  do
    ok <- BC.parseBitCodeFromFile file
    case ok of
      Left err -> throwIO (BitcodeError err)
      Right m -> pure m

main :: IO ()
main =
  do
    args <- getArgs
    let (_, nonOpts, _) = getOpt Permute [] args
    case nonOpts of
      [bitcodeFile, functionToSimulate] ->
        do
          llvmModule <- parseLLVM bitcodeFile
          withZ3 $ \sym ->
            do
              hAlloc <- newHandleAllocator
              let ?laxArith = False
              let ?optLoopMerge = False
              memVar <- mkMemVar "crucible-mc" hAlloc
              Core.Some trans <- translateModule hAlloc memVar llvmModule
              withPtrWidthOf
                trans
                do
                  let ?recordLLVMAnnotation = \_ _ -> pure ()
                  runCrucibleMC sym llvmModule hAlloc trans functionToSimulate
      _ -> error "Usage: crucible-mc inputBitcodeFile.bc functionToSimulate"
