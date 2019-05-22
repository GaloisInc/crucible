
{-# Language RankNTypes, TypeApplications, TypeFamilies #-}
{-# Language FlexibleContexts #-}
module Main(main) where

import System.IO(stdout)
import Control.Exception(throwIO,Exception(..))

import Data.Parameterized.Nonce(withIONonceGenerator)

import qualified Data.LLVM.BitCode as BC

import Lang.Crucible.Types(TypeRepr(..))
import Lang.Crucible.Backend.Online
          ( Z3OnlineBackend, withZ3OnlineBackend, UnsatFeatures(..)
          , Flags, FloatIEEE
          )
import Lang.Crucible.LLVM.Run
import Lang.Crucible.Backend(IsSymInterface)
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.EvalStmt(singleStepCrucible)

import Print


main :: IO ()
main =
  parseLLVM "crucible-mc/test/example.bc" >>= \llvm_mod ->
  withZ3                                    $ \sym ->
  runCruxLLVM llvm_mod                      $
  CruxLLVM                                  $ \mt ->
  withPtrWidthOf mt                         $
  Setup
    { cruxOutput = stdout
    , cruxBackend = sym
    , cruxInitCodeReturns = UnitRepr
    , cruxInitCode = return ()
    , cruxUserState = ()
    , cruxGo  = runFrom
    }

runFrom :: (IsSymInterface sym, HasPtrWidth (ArchWidth arch)) =>
            ExecState p sym (LLVM arch) rtp ->  IO ()
runFrom st =
  do print (ppExecState st)
     _ <- getLine
     st1 <- singleStepCrucible 0 st
     runFrom st1


-- | Create a Z3 backend for the simulator.
withZ3 :: (forall s. Z3OnlineBackend s (Flags FloatIEEE) -> IO a) -> IO a
withZ3 k =
  withIONonceGenerator $ \nonceGen ->
  withZ3OnlineBackend @(Flags FloatIEEE) nonceGen ProduceUnsatCores k


-- | This exception is thrown when we fail to parse a bit-code file.
data Err = BitcodeError BC.Error
            deriving Show

instance Exception Err

-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do ok <- BC.parseBitCodeFromFile file
     case ok of
       Left err -> throwIO (BitcodeError err)
       Right m  -> pure m


