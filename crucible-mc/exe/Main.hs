{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

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
import qualified Data.LLVM.BitCode as BC
import Data.Parameterized.Nonce (withIONonceGenerator)
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.FunctionHandle
import Lang.Crucible.LLVM.Run
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.ModelChecker.CrucibleMC (runCrucibleMC)
import System.Console.GetOpt (ArgOrder (..), getOpt)
import System.Environment (getArgs)

-- | Create a Z3 backend for the simulator.
withZ3 ::
  (forall s. Online.Z3OnlineBackend s (Online.Flags Online.FloatIEEE) -> IO a) ->
  IO a
withZ3 k =
  withIONonceGenerator $ \nonceGen ->
    Online.withZ3OnlineBackend Online.FloatIEEERepr nonceGen Online.ProduceUnsatCores k

-- | This exception is thrown when we fail to parse a bit-code file.
data Err
  = BitcodeError BC.Error
  | UnknownFunction String
  | UnsupportedFunType String
  deriving (Show)

instance Exception Err

-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
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
          withZ3 $ \sym -> do
            hAlloc <- newHandleAllocator
            let ?laxArith = False
            Core.Some trans <- translateModule hAlloc llvmModule
            withPtrWidthOf trans (runCrucibleMC sym llvmModule hAlloc trans functionToSimulate)
      _ -> error "Usage: crucible-mc inputBitcodeFile.bc functionToSimulate"
