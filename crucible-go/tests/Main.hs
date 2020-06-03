{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
module Main ( main ) where

import Control.Lens ( (^.) )
import Control.Monad.ST ( runST )
import System.FilePath ( dropExtension )
import System.FilePath.Glob ( namesMatching )
import System.IO ( stderr )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Data.Parameterized.Context as Ctx
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
import qualified Lang.Crucible.Solver.SimpleBuilder as C
import qualified Lang.Crucible.Solver.SimpleBackend as C

import qualified Language.Go.Parser as Go
import qualified Language.Go.AST as Go
import Lang.Crucible.Go.Translation ( translateFunction )

main :: IO ()
main = do
  expectedFiles <- namesMatching "tests/programs/*.go.expected"
  T.defaultMain $ T.testGroup "GoSimulatorTests" (map testGoFile expectedFiles)

testGoFile :: FilePath -> T.TestTree
testGoFile fp = T.testCase goFileName $ do
  efile <- Go.parseFile goFileName
  case efile of
    Left err -> T.assertFailure ("Error while parsing " ++ goFileName ++ ": " ++ show err)
    Right f -> do
      let (fid, params, returns, body) = findFirstFunction f
          cfg = let ?machineWordWidth = 32 in runST $ translateFunction fid params returns body
      withSimulatedResult cfg $ \sr -> do
        expectedResult <- read <$> readFile fp
        T.assertEqual "Expected result" expectedResult sr
  where
    goFileName = dropExtension fp

findFirstFunction :: Go.File Go.SourceRange
                  -> (Go.Id Go.SourceRange,
                      Go.ParameterList Go.SourceRange,
                      Go.ReturnList Go.SourceRange,
                      [Go.Statement Go.SourceRange])
findFirstFunction (Go.File _ _ _ _ tls) = go tls
  where
    go (Go.FunctionDecl _ fid pl rl (Just body) : _) = (fid, pl, rl, body)
    go (_:rest) = go rest
    go [] = error "No functions defined in file"

-- | Specialize the symbolic simulator to the SimpleBuilder backend
type Sym t = C.SimpleBuilder t C.SimpleBackendState

-- | Given a CFG, run the symbolic simulator on it and then call a
-- callback on the result.
--
-- Note that we only populate integer arguments.
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
                 (C.regValue <$> C.callCFG cfg args)
      case res of
        C.FinishedExecution _st pr -> do
            gp <- case pr of
                    C.TotalRes gp -> return gp
                    C.PartialRes _ gp _ -> do
                      putStrLn "Symbolic simulation failed along some paths!"
                      return gp
            k (toSimpleResult (gp ^. C.gpValue))
        C.AbortedResult _ _ar -> fail "Symbolic execution failed"

-- | Convert a value returned by the symbolic simulator into a simple
-- result that we can inspect.
--
-- Currently, we only support returning a single int32, int64, or
-- float (which is wrapped in a single-element struct by our
-- crucible-go translation).  Floats are translated to rationals,
-- unfortunately.
toSimpleResult :: forall t tp . C.RegEntry (Sym t) tp -> SimpleResult
toSimpleResult re =
  case C.regType re of
    C.StructRepr ctx
      | Just C.Refl <- C.testEquality ctx (Ctx.empty Ctx.%> C.BVRepr (C.knownNat :: C.NatRepr 32)) ->
        case C.unRV (C.regValue re Ctx.! Ctx.base) of
          C.BVElt _ i _ -> RInt i
          _ -> error "Impossible"
      | Just C.Refl <- C.testEquality ctx (Ctx.empty Ctx.%> C.BVRepr (C.knownNat :: C.NatRepr 64)) ->
        case C.unRV (C.regValue re Ctx.! Ctx.base) of
          C.BVElt _ i _ -> RInt i
          _ -> error "Impossible"
      | Just C.Refl <- C.testEquality ctx (Ctx.empty Ctx.%> C.RealValRepr) ->
        case C.unRV (C.regValue re Ctx.! Ctx.base) of
          C.RatElt r _ -> RRational r
          _ -> error "Impossible"
    _ -> InvalidResult (show (C.regType re))

data SimpleResult = RInt Integer
                  | RRational Rational
                  | InvalidResult String
  deriving (Eq, Ord, Read, Show)

setupArguments :: forall t blocks init ret . Sym t -> C.CFG blocks init ret -> IO (C.RegMap (Sym t) init)
setupArguments _sym cfg = C.RegMap <$> Ctx.traverseWithIndex setupArg (C.cfgArgTypes cfg)
  where
    hdl = C.cfgHandle cfg
    loc = C.mkProgramLoc (C.handleName hdl) C.InternalPos
    setupArg :: forall s ctx . Ctx.Index ctx s -> C.TypeRepr s -> IO (C.RegEntry (Sym t) s)
    setupArg ix tr = do
      case tr of
        C.BVRepr w -> return C.RegEntry { C.regType = tr
                                        , C.regValue = C.BVElt w (fromIntegral (Ctx.indexVal ix)) loc
                                        }
        _ -> error "Unsupported argument type"

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
