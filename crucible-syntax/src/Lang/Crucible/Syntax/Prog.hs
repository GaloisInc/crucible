{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Syntax.Prog where

import Control.Monad.ST
import Control.Monad

import Data.List (find)
import Data.Text (Text)
import Data.String (IsString(..))
--import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.Exit
import Text.Megaparsec as MP

import Data.Parameterized.Nonce
import Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.CFG.Core as C
import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.ExprParse (printSyntaxError)
import Lang.Crucible.Syntax.Atoms

import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.Backend
import Lang.Crucible.Backend.ProofGoals
import Lang.Crucible.Backend.Simple
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator

import What4.Expr.Builder (Flags, FloatIEEE)


-- | The main loop body, useful for both the program and for testing.
doParseCheck
   :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Bool     -- ^ Whether to pretty-print the input data as well
   -> Handle   -- ^ A handle that will receive the output
   -> IO ()
doParseCheck fn theInput pprint outh =
  do ha <- newHandleAllocator
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
       Left err ->
         do putStrLn $ parseErrorPretty' theInput err
            exitFailure
       Right v ->
         do when pprint $
              forM_ v $
                \e -> T.hPutStrLn outh (printExpr e) >> hPutStrLn outh ""
            cs <- stToIO $ top ha $ cfgs v
            case cs of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right ok ->
                forM_ ok $
                 \(ACFG _ _ theCfg) ->
                   do let ssa = toSSA theCfg
                      hPutStrLn outh $ show $ cfgHandle theCfg
                      hPutStrLn outh $ show ssa

simulateProgram
   :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Handle   -- ^ A handle that will receive the output
   -> IO ()
simulateProgram fn theInput outh =
  do ha <- newHandleAllocator
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
       Left err ->
         do putStrLn $ parseErrorPretty' theInput err
            exitFailure
       Right v ->
         do cs <- stToIO $ top ha $ cfgs v
            case cs of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right ok -> runProgram outh ha ok

runProgram ::
  Handle ->
  HandleAllocator RealWorld ->
  [ACFG] ->
  IO ()
runProgram outh ha cs =
  case find isMain cs of
    Just (ACFG Ctx.Empty retType mn) ->
      withIONonceGenerator $ \nonceGen ->
      do sym <- newSimpleBackend @_ @(Flags FloatIEEE) nonceGen

         let mainHdl = cfgHandle mn
         let fnBindings = fnBindingsFromList
                           [ case toSSA g of
                               C.SomeCFG ssa ->
                                 FnBinding (cfgHandle g) (UseCFG ssa (postdomInfo ssa))
                           | ACFG _ _ g <- cs
                           ]
         let simCtx = initSimContext sym emptyIntrinsicTypes ha outh fnBindings emptyExtensionImpl ()
         let simSt  = initSimState simCtx emptyGlobals defaultAbortHandler

         hPutStrLn outh "==== Begin Simulation ===="

         _res <- executeCrucible simSt $ runOverrideSim retType (regValue <$> callFnVal (HandleFnVal mainHdl) emptyRegMap)

         hPutStrLn outh "\n==== Finish Simulation ===="

         getProofObligations sym >>= \case
           Nothing -> hPutStrLn outh "==== No proof obligations ===="
           Just gs ->
             do hPutStrLn outh "==== Proof obligations ===="
                mapM_ (hPrint outh . ppProofObligation sym) (goalsToList gs)

    _ -> hPutStrLn outh "No suitable main function found"

  where
  isMain (ACFG _ _ g) = handleName (cfgHandle g) == fromString "main"
