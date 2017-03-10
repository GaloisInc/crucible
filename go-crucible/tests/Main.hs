{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main ( main ) where

import Control.Lens ( (^.) )
import Control.Monad.ST ( runST )
import Data.IORef
import qualified Data.List.NonEmpty as NL
import System.FilePath.Glob ( namesMatching )
import System.IO ( stderr )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Nonce as Ctx
import qualified Data.Parameterized.Map as MapF

import qualified Lang.Crucible.Config as C
import qualified Lang.Crucible.Core as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Simulator.CallFns as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.MSSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Solver.Interface as C hiding (mkStruct)
import qualified Lang.Crucible.Solver.SimpleBuilder as C
import qualified Lang.Crucible.Solver.SimpleBackend as C
import qualified Lang.Crucible.Utils.Arithmetic as C
-- import qualified Lang.Crucible.Solver.SAWCoreBackend as C
import qualified Verifier.SAW.SharedTerm as SC

import qualified Language.Go.Parser as Go
import qualified Language.Go.AST as Go
import Lang.Crucible.Go.Translation ( translateFunction )

main :: IO ()
main = return ()

testGoFile :: FilePath -> T.Assertion
testGoFile fp = do
  efile <- Go.parseFile fp
  case efile of
    Left err -> T.assertFailure (show err)
    Right f@(Go.File a _ pname _ _ ) -> do
      let (fid, params, returns, body) = findFirstFunction f
          cfg = runST $ translateFunction fid params returns body
      withSimulatedResult cfg $ \sr ->
        T.assertEqual undefined 0 0

findFirstFunction = undefined

type Sym t = C.SimpleBuilder t C.SimpleBackendState

withSimulatedResult :: C.AnyCFG -> (SimpleResult -> IO r) -> IO r
withSimulatedResult (C.AnyCFG cfg) k = do
  Ctx.withIONonceGenerator $ \ngen ->
    C.withHandleAllocator $ \halloc -> do
      sym <- C.newSimpleBackend ngen
      simConfig <- C.initialConfig 0 []
      let bindings = C.fnBindingsFromList []
      let simCtx = C.initSimContext sym MapF.empty simConfig halloc stderr bindings
      let h   = C.cfgHandle cfg
      args <- setupArguments sym cfg
      res  <- C.run simCtx C.emptyGlobals errorHandler (C.handleReturnType h)
                 (C.regValue <$> (C.callCFG cfg args))
      case res of
        C.FinishedExecution st pr -> do
            gp <- case pr of
                    C.TotalRes gp -> return gp
                    C.PartialRes _ gp _ -> do
                      putStrLn "Symbolic simulation failed along some paths!"
                      return gp
            k (toSimpleResult (gp ^. C.gpValue))
        C.AbortedResult _ ar -> fail "Symbolic execution failed"

toSimpleResult :: forall t tp . C.RegEntry (Sym t) tp -> SimpleResult
toSimpleResult re =
  case C.asBaseType (C.regType re) of
    C.NotBaseType -> error "Not a base type"
    C.AsBaseType btr ->
      case btr of
        C.BaseBVRepr w ->
          case C.regValue re of
            C.BVElt _ i _ -> RInt i

data SimpleResult = RInt Integer
  deriving (Eq, Ord, Read, Show)

setupArguments :: forall t blocks init ret . Sym t -> C.CFG blocks init ret -> IO (C.RegMap (Sym t) init)
setupArguments sym cfg = C.RegMap <$> Ctx.traverseWithIndex setupArg (C.cfgArgTypes cfg)
  where
    hdl = C.cfgHandle cfg
    loc = C.mkProgramLoc (C.handleName hdl) C.InternalPos
    setupArg :: forall s ctx . Ctx.Index ctx s -> C.TypeRepr s -> IO (C.RegEntry (Sym t) s)
    setupArg ix tr = do
      case tr of
        C.BVRepr w -> return C.RegEntry { C.regType = tr
                                        , C.regValue = C.BVElt w (fromIntegral (Ctx.indexVal ix)) loc
                                        }

-- | Abort the current execution.
abortTree :: C.SimError
          -> C.MSS_State  sym rtp f args
          -> IO (C.SimResult  sym rtp)
abortTree e s = do
  -- Switch to new frame.
  C.isSolverProof (s^.C.stateContext) $ do
    C.abortExec e s


errorHandler :: C.ErrorHandler C.SimContext sym rtp
errorHandler = C.EH abortTree
