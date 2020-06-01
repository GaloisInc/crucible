-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.ExtractSAWCore
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Some experimental, and currently bitrotted code for extracting
-- recursive functional representations from Crucible programs.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}


module Lang.Crucible.Solver.ExtractSAWCore where

import Control.Monad.ST
import qualified Data.Text as Text
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.IO.Class
import Control.Lens
import Control.Monad
import qualified Data.Vector as V
import Control.Monad.Writer
import Data.IORef

import Text.PrettyPrint.ANSI.Leijen ( text, Doc )

import qualified Lang.MATLAB.MultiDimArray as MDA
import qualified Text.LLVM.AST as L

import Data.Parameterized.TraversableFC
import qualified Data.Parameterized.Context as Ctx

import Lang.Crucible.Analysis.DFS
import Lang.Crucible.Analysis.Shape
import Lang.Crucible.Analysis.ForwardDataflow
import Lang.Crucible.Core
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.MSSim
import Lang.Crucible.Solver.PartExpr
import Lang.Crucible.Solver.Interface
import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.FunctionName( functionNameFromText )
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.CallFns

import qualified Lang.Crucible.Solver.SAWCoreBackend as SAW
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Rewriter as SC
import qualified Verifier.SAW.TypedAST as SC
import qualified Verifier.SAW.ExternalFormat as SC
--import qualified Verifier.SAW.Prelude.Constants as SC
import Lang.Crucible.LLVM.Translation


data RedirectInfo s (ret :: CrucibleType) (init :: Ctx CrucibleType)
  = NoRedirectInfo
  | RedirectInfo
      String
      (Lang.Crucible.FunctionHandle.FnHandle init ret)
      (SC.ExtCns (SC.SharedTerm s))
      (Override (SAW.SAWCoreBackend s) init ret)
      (Ctx.Assignment ShapeDom init)

findSymbolicBackEdges
  :: ModuleTranslation
  -> String
  -> (forall blocks init ret
          . CFG blocks init ret
         -> Ctx.Assignment (KildallPair (Ctx.Assignment ShapeDom) SymDom) blocks
         -> Set.Set (Some (BlockID blocks))
         -> a)
  -> a
findSymbolicBackEdges mt nm k =
 -- FIXME, this is all pretty bogus...
 let f :: TypeRepr tp -> ShapeDom tp
     f (BVRepr _) = SymbolicShape
     f (BoolRepr) = LitShape True
     f (StructRepr ctx) = StructShape $ Ctx.generate (Ctx.size ctx) $ \i -> f (ctx Ctx.! i)
     f _ = ConcreteShape

  in case Map.lookup (L.Symbol nm) (cfgMap mt) of
       Nothing -> error $ unwords ["symbol", nm, "not found"]
       Just (AnyCFG (cfg :: CFG blocks init ret)) ->
          let begin = Ctx.generate (Ctx.size (cfgArgTypes cfg)) (\i -> f (cfgArgTypes cfg Ctx.! i))
              (asgn, _r, _rc) = kildall_forward shapeAnalysis cfg (begin, Concrete)
              bkset = dfs_backedge_targets cfg

              isSymbolicBlock :: Some (BlockID blocks) -> Bool
              isSymbolicBlock (Some (BlockID bid)) =
                  case asgn Ctx.! bid of
                    KP _ Symbolic -> True
                    _ -> False

           in k cfg asgn $ Set.filter isSymbolicBlock bkset


-------------------------------------

{-
llvmShapeResults
   :: ModuleTranslation
   -> String
llvmShapeResults mt =
  let nm = "factorial" -- "main" --
      f :: TypeRepr tp -> ShapeDom tp
      f (BVRepr _) = SymbolicShape
      f (BoolRepr) = LitShape True
      f (StructRepr ctx) = StructShape $ ctxReprGenerate ctx $ \_i tp -> f tp
      f _ = ConcreteShape

  in case Map.lookup (L.Symbol nm) (cfgMap mt) of
       Nothing -> error $ unwords ["symbol", nm, "not found"]
       Just (AnyCFG cfg) ->
          shapeResults (ctxReprGenerate (cfgArgTypes cfg) (\_ tp -> f tp)) cfg
-}


doExtractSAWCore
  :: HandleAllocator RealWorld
  -> SAW.SAWCoreBackend s
  -> (MSSim (SAW.SAWCoreBackend s) () (OverrideLang EmptyCtx UnitType) EmptyCtx () -> IO (SimResult (SAW.SAWCoreBackend s) ()))
  -> ModuleTranslation
  -> String
  -> IO ()
doExtractSAWCore halloc sym runOverride mt fnname = do
  -- we use this IORef to "leak" some additional information from the following "run" call,
  -- which has a constrained type that makes it difficult to pass this information out otherwise
  defRef <- newIORef Nothing

  rr <- runOverride $ do
       -- Build a crucible CFG for the given LLVM function.  Compute
       -- the shape analysis for the given function and find which
       -- control-flow edges in the graph are back-edges under the
       -- influence of a symbolic branch.
       findSymbolicBackEdges mt fnname $ \(cfg :: CFG blocks init ret) shapes bk -> do

       -- Allocate new Crucible handles and SAW external constants to stand in for the
       -- symbolic back-edge targets.  Also build a crucible override function that
       -- constructs a SAWCore term corresponding to a recursive call.  Save all the
       -- relevant information in a RedirectInfo.
       redirInfo <- Ctx.generateM (Ctx.size (cfgBlockMap cfg)) (\i -> do
              if Set.member (Some (BlockID i)) bk
                 then do let nm = fnname ++ "_" ++ show (Ctx.indexVal i)
                         h <- liftIO $ stToIO $ mkHandle' halloc (functionNameFromText $ Text.pack nm)
                                                      (blockInputs (cfgBlockMap cfg Ctx.! i))
                                                      (cfgReturnType cfg)
                         let (KP shape _) = shapes Ctx.! i
                         (ec, ovr) <- liftIO $ buildSAWInterface sym nm
                                          (blockInputs (cfgBlockMap cfg Ctx.! i))
                                          (cfgReturnType cfg)
                                          shape
                         return $ RedirectInfo nm h ec ovr shape
                 else return NoRedirectInfo)

       -- Build a new block map where those basic blocks that are the target of symbolic
       -- back edges are replaced by tail calls to the new functions we just allocated
       let blockMap' = Ctx.generate (Ctx.size (cfgBlockMap cfg)) (\i ->
                let block = (cfgBlockMap cfg) Ctx.! i in
                case redirInfo Ctx.! i of
                  NoRedirectInfo -> block
                  RedirectInfo nm h _ _ _ ->
                     Block (BlockID i)
                          (blockInputs block)
                          (ConsStmt (mkProgramLoc (functionNameFromText $ Text.pack nm) InternalPos)
                            (SetReg (handleType h) (App (HandleLit h)))
                          (TermStmt (mkProgramLoc (functionNameFromText $ Text.pack nm) InternalPos)
                                    (TailCall (Reg (Ctx.nextIndex (Ctx.size (blockInputs block))))
                                              (blockInputs block)
                                              (Ctx.generate (Ctx.size (blockInputs block))
                                                     (\idx -> Reg (Ctx.skip idx)))
                                          )))
                          Ctx.noDiff
                          Nothing)

       -- populate the simulator's handleMap with our custom overrides
       sequence_ [
              do let RedirectInfo _nm h _ex ovr _shape = redirInfo Ctx.! i
                 stateContext . functionBindings %= insertHandleMap h (UseOverride ovr)
              | Some (BlockID i) <- Set.toList bk
              ]

       -- For each branch of the reclet we want to build, symbolically simulate from
       -- the the beginning of related basic block with symbolic arguments.
       (branches :: [(SC.ExtCns (SC.SharedTerm s), SC.SharedTerm s)]) <- sequence [
              do let block = (cfgBlockMap cfg) Ctx.! i
                 let RedirectInfo _nm h ex _ovr shape = redirInfo Ctx.! i
                 let freshId = BlockID $ Ctx.nextIndex (Ctx.size blockMap')
                 let block' = Block freshId
                                    (blockInputs block)
                                    (blockStmts block)
                                    (Ctx.extendRight Ctx.noDiff)
                                    Nothing
                 let bm' = Ctx.extend (extendBlockMap blockMap') block'
                 let branch_cfg = fillPostdomFields $ CFG h bm' freshId

                 (args,sawECs) <- liftIO $ buildBranchArgs sym (blockInputs block) shape

                 out <- callCFG branch_cfg args
                 v <- liftIO $ sawMarshalValue sym (cfgReturnType cfg) out
                 def <- liftIO $ SC.scAbstractExts (SAW.saw_ctx sym) sawECs v
                 return (ex, def)

              | Some (BlockID i) <- Set.toList bk
              ]

       -- Simulate from the original function entry point to build the body of the reclet.
       let (KP mainshape _) = shapes Ctx.! (blockIDIndex (cfgEntryBlockID cfg))
       (mainArgs,mainSawECs) <- liftIO $ buildBranchArgs sym (cfgArgTypes cfg) mainshape
       let maincfg = fillPostdomFields $ cfg{ cfgBlockMap = blockMap' }
       out <- callCFG maincfg mainArgs

       -- Now stitch the pieces togeter to get the final SAWCore definition.
       liftIO $ do
            body  <- sawMarshalValue sym (cfgReturnType cfg) out
            def   <- scReclet (SAW.saw_ctx sym) branches body
            def'  <- simplifySAW (SAW.saw_ctx sym) def
            def'' <- SC.scAbstractExts (SAW.saw_ctx sym) mainSawECs def'
            writeIORef defRef (Just def'')

       -- We are done inside the simulator
       return ()

  putStrLn ""
  case rr of
     FinishedExecution _ (TotalRes _) -> do
        Just v <- readIORef defRef
        -- putStrLn $ SC.scPrettyTerm v
        putStrLn $ SC.scWriteExternal v

     _ -> putStrLn "Execution failed!"

simplifySAW
  :: SC.SharedContext s
  -> SC.SharedTerm s
  -> IO (SC.SharedTerm s)
simplifySAW s t = do
   rs <- tupleRules s
   let simpset = SC.addRules rs SC.emptySimpset
   -- putStrLn $ show simpset
   SC.rewriteSharedTerm s simpset t

tupleRules
  :: SC.SharedContext s
  -> IO [SC.RewriteRule (SC.SharedTerm s)]
tupleRules _sc = return []
{-
tupleRules sc = do
{-
  r <- SC.scEqRewriteRule sc (SC.mkIdent SC.preludeModuleName "tuple2_eta")
  return [r]
-}
  srt <- SC.scSort sc (SC.mkSort 0)
  ty1 <- SC.scLocalVar sc 1
  ty2 <- SC.scLocalVar sc 0
  tty <- SC.scTupleType sc [ty1, ty2]
  x   <- SC.scLocalVar sc 0
  x0  <- SC.scTupleSelector sc x 1
  x1  <- SC.scTupleSelector sc x 2
  x'  <- SC.scTuple sc [x0,x1]
  let ctx = [srt, srt, tty]
  let r2  = SC.mkRewriteRule ctx x' x
  return [r2]
-}

scReclet
  :: SC.SharedContext s
  -> [(SC.ExtCns (SC.SharedTerm s), SC.SharedTerm s)]
  -> SC.SharedTerm s
  -> IO (SC.SharedTerm s)
scReclet _sc [] body = return body
scReclet sc [(ec,def)] body =
  do def' <- SC.scAbstractExts sc [ec] def
     fx <- SC.scGlobalApply sc "Cryptol.fix" [SC.ecType ec, def']
     SC.scInstantiateExt sc (Map.singleton (SC.ecVarIndex ec) fx) body
scReclet _sc _xs _body = error "FIXME mutual reclet..."


newtype MoF m f a = MoF { unMoF :: m (f a) }

buildBranchArgs :: forall s args
   . SAW.SAWCoreBackend s
  -> CtxRepr args
  -> Ctx.Assignment ShapeDom args
  -> IO (RegMap (SAW.SAWCoreBackend s) args, [SC.ExtCns (SC.SharedTerm s)])
buildBranchArgs sym args shape = do
  let mp :: Ctx.Assignment (MoF (WriterT [SC.ExtCns (SC.SharedTerm s)] IO) (RegEntry (SAW.SAWCoreBackend s))) args
      mp = Ctx.generate (Ctx.size args) (\i -> MoF $ do
             let tp = args Ctx.! i
             cty <- liftIO $ crucibleToSawType sym tp (shape Ctx.! i)
             var <- liftIO $ SC.scFreshGlobalVar (SAW.saw_ctx sym)
             let ec = SC.EC var ("arg_"++(show $ Ctx.indexVal i)) cty
             tell [ec]
             v <- liftIO (sawUnmarshalValue sym tp =<< SC.scFlatTermF (SAW.saw_ctx sym) (SC.ExtCns ec))
             return (RegEntry tp v))

  (mp',ecs) <- runWriterT $ traverseFC unMoF mp
  return (RegMap mp', ecs)

buildSAWInterface
  :: SAW.SAWCoreBackend s
  -> String
  -> CtxRepr args
  -> TypeRepr ret
  -> Ctx.Assignment ShapeDom args
  -> IO (SC.ExtCns (SC.SharedTerm s), Override (SAW.SAWCoreBackend s) args ret)
buildSAWInterface sym nm args ret shape = do
  sawGlobal <- SC.scFreshGlobalVar (SAW.saw_ctx sym)
  sc_ty <- crucibleSigToSawType sym args ret shape
  let ec = SC.EC sawGlobal nm sc_ty
  return (ec
         , Override
              (functionNameFromText $ Text.pack nm)
              (sawInterfaceOverrideHandler sym args ret shape ec)
         )


sawInterfaceOverrideHandler :: forall s args ret rtp
   . SAW.SAWCoreBackend s
  -> CtxRepr args
  -> TypeRepr ret
  -> Ctx.Assignment ShapeDom args
  -> SC.ExtCns (SC.SharedTerm s)
  -> MSS_State (SAW.SAWCoreBackend s) rtp (OverrideLang args ret) EmptyCtx
  -> IO (SimResult (SAW.SAWCoreBackend s) rtp)
sawInterfaceOverrideHandler sym args ret _shape ex mss_state = do
  base <- SC.scFlatTermF (SAW.saw_ctx sym) $ SC.ExtCns ex
  tm <- go args base
  v <- sawUnmarshalValue sym ret tm
  returnValue mss_state v

 where go :: CtxRepr args
          -> SC.SharedTerm s
          -> IO (SC.SharedTerm s)
       go ctx base = foldlFC fld (return base) $ Ctx.generate (Ctx.size ctx) (\i -> mkArg i (ctx Ctx.! i))

       fld :: IO (SC.SharedTerm s)
           -> Ignore (IO (SC.SharedTerm s)) tp
           -> IO (SC.SharedTerm s)
       fld base (Ignore x) = join $ pure (SC.scApply (SAW.saw_ctx sym)) <*> base <*> x

       mkArg :: Ctx.Index args tp
             -> TypeRepr tp
             -> Ignore (IO (SC.SharedTerm s)) tp
       mkArg i tp = Ignore $ do
            let mp = overrideRegMap $ mss_state ^. stateOverrideFrame
            let arg = regVal mp (Reg i)
            sawMarshalValue sym tp arg

sawUnmarshalValue
  :: SAW.SAWCoreBackend s
  -> TypeRepr tp
  -> SC.SharedTerm s
  -> IO (RegValue (SAW.SAWCoreBackend s) tp)
sawUnmarshalValue sym tpr tm =
  case tpr of
    BVRepr w | Just LeqProof <- isPosNat w -> return $ SAW.SC (BaseBVRepr w) tm
    NatRepr   -> return $ SAW.SC baseTypeRepr tm
    BoolRepr  -> return $ SAW.SC baseTypeRepr tm
    -- NB: structures with exactly one element are treated as a special case
    StructRepr ctx
      | Ctx.AssignExtend ctx' tp <- Ctx.view ctx
      , Ctx.AssignEmpty <- Ctx.view ctx' -> do
          x <- sawUnmarshalValue sym tp tm
          return $ Ctx.extend Ctx.empty $ RV $ x
    StructRepr ctx ->
      Ctx.generateM (Ctx.size ctx) $ \idx -> do
        let tp = ctx Ctx.! idx
        -- NB: SAWCore tuple selectors are 1-based!
        tm' <- SC.scTupleSelector (SAW.saw_ctx sym) tm (Ctx.indexVal idx + 1)
        RV <$> sawUnmarshalValue sym tp tm'
    _ -> fail $ unwords ["Crucible type cannot be mapped onto a SAW type:", show tpr]

sawMarshalValue
  :: SAW.SAWCoreBackend s
  -> TypeRepr tp
  -> RegValue (SAW.SAWCoreBackend s) tp
  -> IO (SC.SharedTerm s)
sawMarshalValue sym tpr expr =
  case tpr of
    BVRepr _w -> SAW.toSC sym expr
    NatRepr   -> SAW.toSC sym expr
    BoolRepr  -> SAW.toSC sym expr
    -- NB: structures with exactly one element are treated as a special case
    StructRepr ctx
      | Ctx.AssignExtend ctx' tp <- Ctx.view ctx
      , Ctx.AssignEmpty <- Ctx.view ctx' ->
         sawMarshalValue sym tp (unRV $ expr Ctx.! Ctx.base)
    StructRepr ctx -> do
       xs <- toListFC ignoreOut <$>
               Ctx.zipWithM (\tp ex -> Ignore <$> sawMarshalValue sym tp (unRV ex)) ctx expr
       SC.scTuple (SAW.saw_ctx sym) xs
    _ -> fail $ unwords ["Crucible type cannot be mapped onto a SAW type:", show tpr]


crucibleSigToSawType
  :: forall s args tp
   . SAW.SAWCoreBackend s
  -> CtxRepr args
  -> TypeRepr tp
  -> Ctx.Assignment ShapeDom args
  -> IO (SC.SharedTerm s)
crucibleSigToSawType sym args ret shape = do
   xs <- Ctx.generateM (Ctx.size args) (\i ->
             Ignore <$> crucibleToSawType sym (args Ctx.! i) (shape Ctx.! i))
   ret' <- crucibleToSawType sym ret SymbolicShape
   foldrFC (\(Ignore t) m -> m >>= SC.scFun (SAW.saw_ctx sym) t) (return ret') xs

{-
crucibleSigToSawType sym args ret shape = go args =<< crucibleToSawType sym ret
 where go :: CtxRepr tps -> SC.SharedTerm s -> IO (SC.SharedTerm s)
       go EmptyCtxRepr tp = return tp
       go (ConsCtxRepr ctx x) shs tp = do
               x' <- crucibleToSawType sym x
               tp' <- SC.scFun (SAW.saw_ctx sym) x' tp
               go ctx tp'
-}

crucibleToSawType :: forall s tp
   . SAW.SAWCoreBackend s
  -> TypeRepr tp
  -> ShapeDom tp
  -> IO (SC.SharedTerm s)
crucibleToSawType sym tp sh =
  let sc = SAW.saw_ctx sym in
  case tp of
    BVRepr w -> SC.scBitvector sc (fromIntegral (widthVal w))
    NatRepr  -> SC.scNatType sc
    BoolRepr -> SC.scBoolType sc
    StructRepr ctx -> do
       xs <- Ctx.generateM (Ctx.size ctx) (\i -> do
                let tp' = ctx Ctx.! i
                let sh' = case sh of
                             StructShape ss -> ss Ctx.! i
                             ConcreteShape  -> ConcreteShape
                             _              -> SymbolicShape
                Ignore <$> crucibleToSawType sym tp' sh')
       let xs' = toListFC ignoreOut xs
       case xs' of
         -- NB: structures with exactly one element are treated as a special case
         [x] -> return x
         _   -> SC.scTupleType sc xs'

{-
    StructRepr ctx -> go ctx []
       where go :: CtxRepr ctx -> [SC.SharedTerm s] -> IO (SC.SharedTerm s)
             go EmptyCtxRepr []  = SC.scTupleType sc []
             -- NB: structures with exactly one element are treated as a special case
             go EmptyCtxRepr [x] = return x
             go EmptyCtxRepr xs  = SC.scTupleType sc xs
             go (ConsCtxRepr c t) xs = do
                       t' <- crucibleToSawType sym t (error "FIXME")
                       go c (t':xs)
-}

    _ -> fail $ unwords ["Crucible type cannot be mapped ont a SAW type:", show tp]


printSAWValues
   :: forall s
    . SAW.SAWCoreBackend s
   -> V.Vector (PartExpr (Pred (SAW.SAWCoreBackend s)) (Value (SAW.SAWCoreBackend s)))
   -> IO ()
printSAWValues sc = V.ifoldl' (\m i x -> m >> printPart i x) (return ())
 where printPart i Unassigned = putStrLn $ unlines [ "Result "++show i, "  UNASSIGNED",""]
       printPart i (PE _ v)   = printVal i v >>= print

       printVal :: Int -> Value (SAW.SAWCoreBackend s) -> IO Doc
       printVal i (UIntArray (SomeBVArray _ a)) = do
           a' <- traverse (ppSAWCore sc) a
           return $ MDA.ppVector ("Result "++ show i) id a'

       printVal _ (RealArray _)  = return $ text "No printing for real arrays"
       printVal _ (IntArray _)   = return $ text "No printing for int arrays"
       printVal _ (CharArray _)  = return $ text "No printing for char arrays"
       printVal _ (LogicArray _) = return $ text "No printing for bool arrays"
       printVal _ (CellArray _)  = return $ text "No printing for cell arrays"
       printVal _ (MatlabStructArray _) = return $ text "No printing for struct arrays"
       printVal _ (FunctionHandle _) = return $ text "No printing for function handles"
       printVal _ (SymLogicArray _) = return $ text "No printing for symbolic logical arrays"

ppSAWCore :: forall s tp. SAW.SAWCoreBackend s -> SymExpr (SAW.SAWCoreBackend s) tp -> IO String
ppSAWCore sc t = SC.scPrettyTerm <$> SAW.toSC sc t
