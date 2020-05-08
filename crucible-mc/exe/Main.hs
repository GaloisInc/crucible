{-# Language RankNTypes, TypeApplications, TypeFamilies #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language PatternSynonyms #-}
module Main(main) where

import System.IO(stdout)
import Control.Exception(throwIO,Exception(..))

import Data.IORef (newIORef)
import qualified Data.Map as Map
import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Context (pattern Empty)

import qualified Data.LLVM.BitCode as BC

import What4.InterpretedFloatingPoint (FloatIEEE, FloatModeRepr(..))

import Lang.Crucible.Types(TypeRepr(..))
import Lang.Crucible.Backend.Online
          ( Z3OnlineBackend, withZ3OnlineBackend, UnsatFeatures(..) )
import Lang.Crucible.Backend(IsSymInterface, CrucibleFloatMode)
import Lang.Crucible.CFG.Core(AnyCFG(..),cfgArgTypes,cfgReturnType)
import Lang.Crucible.Simulator

import Lang.Crucible.LLVM.MemModel(defaultMemOptions, LLVMAnnMap)
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
  runCruxLLVM llvm_mod defaultMemOptions False $
  CruxLLVM                                  $ \mt ->
  withPtrWidthOf mt                         $
  case findCFG mt test_fun of
    Nothing -> throwIO (UnknownFunction test_fun)
    Just (AnyCFG cfg) ->
      case (cfgArgTypes cfg, cfgReturnType cfg) of
        (Empty, UnitRepr) ->
          do bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
             let ?badBehaviorMap = bbMapRef in
               pure Setup
                 { cruxOutput = stdout
                 , cruxBackend = sym
                 , cruxInitCodeReturns = UnitRepr
                 , cruxInitCode = do registerFunctions llvm_mod mt
                                     _ <- callCFG cfg emptyRegMap
                                     pure ()
                 , cruxUserState = emptyModel
                 , cruxGo  = runFrom FloatIEEERepr
                 }

        _ -> throwIO (UnsupportedFunType test_fun)

runFrom ::
  (IsSymInterface sym, HasPtrWidth (ArchWidth arch)) =>
  FloatModeRepr (CrucibleFloatMode sym) ->
  ExecState p sym (LLVM arch) rtp ->  IO ()
runFrom fm st =
  do print (ppExecState st)
     _ <- getLine
     st1 <- singleStepCrucible 5 fm st
     runFrom fm st1 


-- | Create a Z3 backend for the simulator.
withZ3 :: (forall s. Z3OnlineBackend s FloatIEEE -> IO a) -> IO a
withZ3 k =
  withIONonceGenerator $ \nonceGen ->
  withZ3OnlineBackend nonceGen FloatIEEERepr ProduceUnsatCores k


-- | This exception is thrown when we fail to parse a bit-code file.
data Err = BitcodeError BC.Error
         | UnknownFunction String
         | UnsupportedFunType String
            deriving Show

instance Exception Err

-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do ok <- BC.parseBitCodeFromFile file
     case ok of
       Left err -> throwIO (BitcodeError err)
       Right m  -> pure m


