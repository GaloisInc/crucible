{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Mir.Run (mirToCFG, extractFromCFGPure)
    where
import System.IO
import qualified Mir.Trans as T
import qualified Data.Map.Strict as Map
import qualified Mir.Mir as M
import Control.Monad
import Control.Lens
import Data.Foldable
import qualified Data.Text as Text
import Control.Monad.ST
import Data.Parameterized.Nonce
import System.IO
import Data.IORef
import qualified Data.Parameterized.Map as MapF
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedAST as SC
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.Config as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Solver.Interface as C hiding (mkStruct)
import qualified Lang.Crucible.Solver.SAWCoreBackend as C
import qualified Lang.Crucible.Solver.SimpleBuilder as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Lang.Crucible.CFG.Reg as Reg
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Vector as V
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Mir.Pass as Pass

import qualified Control.Monad.Trans.State.Strict as SState

type Sym = C.SAWCoreBackend GlobalNonceGenerator

type SimContext = C.SimContext C.SAWCruciblePersonality Sym
type SimGlobalState = C.SymGlobalState Sym

type SymOverride arg_ctx ret = C.OverrideSim C.SAWCruciblePersonality Sym (C.RegEntry Sym ret) arg_ctx ret ()

unfoldAssign ::
     C.CtxRepr ctx
    -> Ctx.Assignment f ctx
    -> (forall ctx' tp. C.TypeRepr tp -> f tp  -> C.CtxRepr ctx' -> Ctx.Assignment f ctx' -> a)
    -> a
unfoldAssign ctx0 asgn k =
  case Ctx.view ctx0 of
    Ctx.AssignEmpty -> error "packType: ran out of actual arguments!"
    Ctx.AssignExtend ctx' ctp' ->
          let asgn' = Ctx.init asgn
              idx   = Ctx.nextIndex (Ctx.size asgn')
           in k ctp' (asgn Ctx.! idx) 
                ctx'
                asgn'

show_val :: C.TypeRepr tp -> C.RegValue Sym tp -> String
show_val tp reg_val =
    case tp of
      C.BVRepr w -> show reg_val
      C.BoolRepr -> show reg_val
      C.StructRepr reprasgn -> show_regval_assgn reprasgn reg_val
      _ -> "Cannot show type: " ++ (show tp)

show_regval_assgn :: C.CtxRepr ctx -> Ctx.Assignment (C.RegValue' Sym) ctx -> String
show_regval_assgn ctxrepr asgn = "[" ++ go ctxrepr asgn (Ctx.sizeInt (Ctx.size ctxrepr)) ++ "]"
    where go :: forall ctx sym. C.CtxRepr ctx -> Ctx.Assignment (C.RegValue' Sym) ctx -> Int -> String
          go _ _ 0 = ""
          go cr as i = unfoldAssign cr as $ \repr val cr' as' ->
              go cr' as' (i-1) ++ ", " ++ show_val repr (C.unRV val) 


asgnCtxToListM :: (Monad m) => C.CtxRepr ctx -> Int -> Ctx.Assignment f ctx -> (forall tp. C.TypeRepr tp -> f tp -> m a) -> m [a]
asgnCtxToListM _ 0 _ _ = return []
asgnCtxToListM cr i as f = unfoldAssign cr as $ \repr val cr' as' -> do
    e <- f repr val
    rest <- asgnCtxToListM cr' (i-1) as' f 
    return (rest ++ [e])


show_regentry :: C.RegEntry Sym ret -> String 
show_regentry (C.RegEntry tp reg_val) = show_val tp reg_val

print_cfg :: C.AnyCFG -> IO ()
print_cfg cfg = case cfg of
                     C.AnyCFG c -> print $ C.ppCFG False c



extractFromCFGPure :: SymOverride Ctx.EmptyCtx ret -> SC.SharedContext -> C.CFG blocks argctx ret -> IO SC.Term -- no global variables
extractFromCFGPure setup sc cfg = do
    let h = C.cfgHandle cfg
    config <- C.initialConfig 0 C.sawOptions
    sym <- C.newSAWCoreBackend sc globalNonceGenerator config
    halloc <- C.newHandleAllocator
    (ecs, args) <- setupArgs sc sym h
    let simctx = C.initSimContext sym MapF.empty config halloc stdout C.emptyHandleMap C.SAWCruciblePersonality
        simst = C.initSimState simctx C.emptyGlobals C.defaultErrorHandler
        osim = do
            setup
            C.regValue <$> C.callCFG cfg args
    res <- C.runOverrideSim simst (C.handleReturnType h) osim
    case res of
      C.FinishedExecution _ pr -> do
          gp <- case pr of
                  C.TotalRes gp -> return gp
                  C.PartialRes _ gp _ -> do
                      putStrLn "Symbolic simulation failed along some paths"
                      return gp
          t <- toSawCore sc sym (gp^.C.gpValue)
          t' <- SC.scAbstractExts sc (toList ecs) t
          return t'
      C.AbortedResult a ar -> do
          fail $ "aborted failure: " ++ handleAbortedResult ar


handleAbortedResult :: C.AbortedResult sym -> String
handleAbortedResult (C.AbortedExec simerror _) = C.simErrorReasonMsg $ C.simErrorReason simerror
handleAbortedResult _ = "unknown"

mirToCFG :: [M.Fn] -> Maybe ([M.Fn] -> [M.Fn]) -> Map.Map Text.Text C.AnyCFG
mirToCFG fns Nothing = mirToCFG fns (Just Pass.passId)
mirToCFG fns (Just pass) = 
    runST $ C.withHandleAllocator (T.transCollection $ pass fns)

toSawCore :: SC.SharedContext -> Sym -> (C.RegEntry Sym tp) -> IO SC.Term
toSawCore sc sym (C.RegEntry tp v) = 
    case tp of
        C.NatRepr -> C.toSC sym v
        C.IntegerRepr -> C.toSC sym v
        C.RealValRepr -> C.toSC sym v
        C.ComplexRealRepr -> C.toSC sym v
        C.BoolRepr -> C.toSC sym v
        C.BVRepr w -> C.toSC sym v
        C.StructRepr ctx -> -- ctx is of type CtxRepr; v is of type Ctx.Assignment (RegValue' sym) ctx
            go_struct ctx v 
        C.VectorRepr t -> go_vector t v
        _ -> fail $ unwords ["unknown type: ", show tp]

   where go_struct :: C.CtxRepr ctx -> Ctx.Assignment (C.RegValue' Sym) ctx -> IO SC.Term
         go_struct cr as = do
             terms <- asgnCtxToListM cr (Ctx.sizeInt (Ctx.size cr)) as $ \repr val -> toSawCore sc sym (C.RegEntry repr (C.unRV val))
             SC.scTuple sc terms
             
         go_vector :: C.TypeRepr t -> V.Vector (C.RegValue Sym t) -> IO SC.Term -- This should actually be a sawcore list; this requires one to also have a function from typereprs to terms
         go_vector tp v = 
             case C.asBaseType tp of
               C.AsBaseType btp -> do
                   sc_tp <- C.baseSCType sc btp
                   let l = V.toList v
                   rs <- mapM (\e -> toSawCore sc sym (C.RegEntry tp e)) l
                   SC.scVector sc sc_tp rs
               _ -> fail $ "Cannot return vectors of non-base type"
             

             


-- one could perhaps do more about ADTs below by giving the below access to the MIR types

setupArg :: SC.SharedContext
         -> Sym
         -> IORef (Seq (SC.ExtCns SC.Term))
         -> C.TypeRepr tp
         -> IO (C.RegEntry Sym tp)
setupArg sc sym ecRef tp =
  case C.asBaseType tp of
    C.AsBaseType btp -> do
       sc_tp <- C.baseSCType sc btp
       i     <- SC.scFreshGlobalVar sc
       ecs   <- readIORef ecRef
       let len = Seq.length ecs
       let ec = SC.EC i ("arg_"++show len) sc_tp
       writeIORef ecRef (ecs Seq.|> ec)
       t     <- SC.scFlatTermF sc (SC.ExtCns ec)
       elt   <- C.bindSAWTerm sym btp t
       return (C.RegEntry tp elt)

    C.NotBaseType ->
        case tp of
          C.StructRepr ctr -> do
              sargs_ <- Ctx.traverseFC (setupArg sc sym ecRef) ctr -- sargs : Ctx.Assignment (C.RegEntry Sym) ctx
              sargs <- Ctx.traverseWithIndex (\_ e -> return $ C.RV $ C.regValue e) sargs_
              return (C.RegEntry tp sargs)
          C.AnyRepr -> fail $ "AnyRepr cannot be made symbolic. This is probably due to attempting to extract an ADT or closure."
          _ -> fail $ unwords ["unimp",  show tp]

setupArgs :: SC.SharedContext
          -> Sym
          -> C.FnHandle init ret
          -> IO (Seq (SC.ExtCns SC.Term), C.RegMap Sym init)
setupArgs sc sym fn = do
  ecRef  <- newIORef Seq.empty
  regmap <- C.RegMap <$> Ctx.traverseFC (setupArg sc sym ecRef) (C.handleArgTypes fn)
  ecs    <- readIORef ecRef
  return (ecs, regmap)
