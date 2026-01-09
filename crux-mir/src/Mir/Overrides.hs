{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language PatternSynonyms #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language ViewPatterns #-}
{-# Language TypeApplications #-}
{-# Language PartialTypeSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language AllowAmbiguousTypes #-}

module Mir.Overrides (bindFn, getString) where

import Control.Lens ((^?), (.=), use, ix, _Wrapped)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.IntMap as IntMap
import Data.List.Extra (unsnoc)
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text

import System.IO (hPutStrLn)

import qualified Prettyprinter as PP

import Data.Parameterized.Context (pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.NatRepr

import What4.Config( getOpt, setOpt, getOptionSetting )
import What4.Expr.GroundEval (GroundEvalFn(..), groundToSym)
import What4.FunctionName (functionNameFromText)
import What4.Interface
import What4.Partial (PartExpr, pattern PE, pattern Unassigned)
import What4.Protocol.Online ( checkWithAssumptionsAndModel )
import What4.SatResult (SatResult(..))

import Lang.Crucible.Backend
    ( CrucibleAssumption(..), IsSymBackend, addAssumption
    , assert, getPathCondition, addFailedAssertion, IsSymInterface
    , backendGetSym, throwUnsupported, LabeledPred(..), addProofObligation )
import Lang.Crucible.Backend.Online
import Lang.Crucible.CFG.Core
    ( CFG, GlobalVar(..), cfgArgTypes, cfgHandle, cfgReturnType )
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Panic
import Lang.Crucible.Pretty
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Types
import Lang.Crucible.Utils.MuxTree


import Crux (SomeOnlineSolver(..))
import Crux.Log
import qualified Crux.Overrides as Crux

import Mir.DefId
import Mir.FancyMuxTree
import Mir.Generator (CollectionState, collection, handleMap, MirHandle(..))
import Mir.Intrinsics
import qualified Mir.Mir as M


getString :: forall sym rtp args ret p. (IsSymInterface sym) =>
    RegValue sym MirSlice ->
    OverrideSim p sym MIR rtp args ret (Maybe Text)
getString (Empty :> RV mirPtr :> RV lenExpr) = runMaybeT $ do
    let w = knownNat @8
    sym <- lift getSymInterface
    len <- readBV lenExpr
    bytes <- forM [0 .. len - 1] $ \i -> do
        iExpr <- liftIO $ bvLit sym knownNat (BV.mkBV knownNat i)
        elemPtr <- lift $ mirRef_offsetWrapSim mirPtr iExpr
        bExpr <- lift $ readMirRefSim (BVRepr w) elemPtr
        b <- readBV bExpr
        return $ fromIntegral b
    return $ Text.decodeUtf8 $ BS.pack bytes

  where
    readBV e = MaybeT (return (BV.asUnsigned <$> asBV e))

makeSymbolicVar ::
    IsSymInterface sym =>
    BaseTypeRepr btp ->
    TypedOverride (p sym) sym MIR (EmptyCtx ::> MirSlice) (BaseToType btp)
makeSymbolicVar btpr =
  Crux.baseFreshOverride btpr strrepr $ \(RV strSlice) -> do
    mstr <- getString strSlice
    case mstr of
      Nothing -> fail "symbolic variable name must be a concrete string"
      Just name ->
        case userSymbol (Text.unpack name) of
          Left err -> fail $ "invalid symbolic variable name " ++ show name ++ ": " ++ show err
          Right x -> return x
  where
    strrepr :: TypeRepr MirSlice
    strrepr = knownRepr

array_symbolic ::
  forall sym btp p .
  (IsSymInterface sym) =>
  BaseTypeRepr btp ->
  TypedOverride (p sym) sym MIR (EmptyCtx ::> MirSlice) (UsizeArrayType btp)
array_symbolic btpr = makeSymbolicVar (BaseArrayRepr (Empty :> BaseUsizeRepr) btpr)

concretize ::
  forall sym bak rtp tp p .
  (IsSymInterface sym) =>
  Maybe (SomeOnlineSolver sym bak) ->
  OverrideSim p sym MIR rtp (EmptyCtx ::> tp) tp (RegValue sym tp)
concretize (Just (SomeOnlineSolver bak)) = do
    let sym = backendGetSym bak

    -- remember if online solving was enabled
    enabledOpt <- liftIO $ getOptionSetting enableOnlineBackend (getConfiguration sym)
    wasEnabled <- liftIO $ getOpt enabledOpt

    -- enable online solving to concretize
    _ <- liftIO $ setOpt enabledOpt True

    -- If the current path condition is satisfiable, retrieve the underlying
    -- model to use for concretizing symbolic values.
    let onlineDisabled = panic "concretize" ["requires online solving to be enabled"]
    mbGroundEval <- liftIO $ withSolverProcess bak onlineDisabled $ \sp -> do
        cond <- getPathCondition bak
        result <- checkWithAssumptionsAndModel sp "concretize" [cond]
        case result of
            Sat f -> pure $ Just f
            _ -> pure Nothing

    RegMap (Empty :> RegEntry tpr val) <- getOverrideArgs

    res <-
      case mbGroundEval of
        -- If the current path condition is satisfiable, concretize the
        -- argument and return it.
        Just (GroundEvalFn evalGround) -> do
          let evalBase :: forall bt . BaseTypeRepr bt -> SymExpr sym bt -> IO (SymExpr sym bt)
              evalBase btr v = evalGround v >>= groundToSym sym btr

          regEval bak (\btpr expr -> liftIO $ evalBase btpr expr) tpr val

        -- If the current path condition is not satisfiable, then return the
        -- original argument unchanged. This is fine to do since the path will
        -- be deemed unreachable anyway.
        --
        -- To be on the safe side, we also emit a failing proof goal. Note that
        -- we don't want to simply abort here, since doing so might cause the
        -- current assumption frame to become unbalanced (#1526). Instead, we
        -- do everything that 'addFailedAssertion' does /besides/ aborting.
        Nothing -> do
          loc <- liftIO $ getCurrentProgramLoc sym
          let err = SimError loc "path is already unreachable"
          liftIO $ addProofObligation bak (LabeledPred (falsePred sym) err)
          pure val

    -- restore the previous setting of the online backend
    _ <- liftIO $ setOpt enabledOpt wasEnabled

    pure res

concretize Nothing = fail "`concretize` requires an online solver backend"

regEval ::
    forall sym bak tp rtp args ret p .
    (IsSymBackend sym bak) =>
    bak ->
    (forall bt. BaseTypeRepr bt -> SymExpr sym bt ->
        OverrideSim p sym MIR rtp args ret (SymExpr sym bt)) ->
    TypeRepr tp ->
    RegValue sym tp ->
    OverrideSim p sym MIR rtp args ret (RegValue sym tp)
regEval bak baseEval = go
  where
    sym = backendGetSym bak

    go :: forall tp' . TypeRepr tp' -> RegValue sym tp' ->
        OverrideSim p sym MIR rtp args ret (RegValue sym tp')
    go (SymbolicArrayRepr {}) _ =
        liftIO $ addFailedAssertion bak $ GenericSimError "can't evaluate a symbolic array"

    go tpr v | AsBaseType btr <- asBaseType tpr = baseEval btr v

    go MirSliceRepr (Empty :> RV ptr :> RV len) = do
        ptr' <- go MirReferenceRepr ptr
        len' <- go UsizeRepr len
        pure $ Empty :> RV ptr' :> RV len'
    go (FloatRepr _fi) v = pure v
    go AnyRepr (AnyValue tpr v) = AnyValue tpr <$> go tpr v
    go CharRepr c = pure c
    go (FunctionHandleRepr args ret) v = goFnVal args ret v
    go (MaybeRepr tpr) pe = goPartExpr tpr pe
    go (VectorRepr tpr) vec = traverse (go tpr) vec
    go (StructRepr ctx) v = Ctx.zipWithM go' ctx v
    go (VariantRepr ctx) v = Ctx.zipWithM goVariantBranch ctx v
    go tpr@(ReferenceRepr _tpr) v = do
        -- Can't use `collapseMuxTree` here since it's in the IO monad, not
        -- OverrideSim.
        rc <- goMuxTreeEntries tpr (viewMuxTree v)
        rc' <- goRefCell rc
        return $ toMuxTree sym rc'
    -- TODO: WordMapRepr
    -- TODO: RecursiveRepr
    go MirReferenceRepr (MirReferenceMux mux) = do
        ref <- goMuxTreeEntries MirReferenceRepr (viewFancyMuxTree mux)
        ref' <- case ref of
            MirReference tpr root path ->
                MirReference tpr <$> goMirReferenceRoot root <*> goMirReferencePath path
            MirReference_Integer i ->
                MirReference_Integer <$> go UsizeRepr i
        return $ MirReferenceMux $ toFancyMuxTree sym ref'
    go MirAggregateRepr (MirAggregate sz m) =
        MirAggregate sz <$> mapM goMirAggregateEntry m
    -- TODO: StringMapRepr
    go tpr _v = throwUnsupported sym $
          "evaluation of " ++ show tpr ++ " is not yet implemented"

    go' :: forall tp' . TypeRepr tp' -> RegValue' sym tp' ->
        OverrideSim p sym MIR rtp args ret (RegValue' sym tp')
    go' tpr (RV v) = RV <$> go tpr v

    goFnVal :: forall args' ret' .
        CtxRepr args' -> TypeRepr ret' -> FnVal sym args' ret' ->
        OverrideSim p sym MIR rtp args ret (FnVal sym args' ret')
    goFnVal args ret (ClosureFnVal fv tpr v) =
        ClosureFnVal <$> goFnVal (args :> tpr) ret fv <*> pure tpr <*> go tpr v
    goFnVal _ _ (HandleFnVal fh) = pure $ HandleFnVal fh
    goFnVal _ _ (VarargsFnVal fh addlArgs) = pure $ VarargsFnVal fh addlArgs

    goPartExpr :: forall tp' . TypeRepr tp' ->
        PartExpr (Pred sym) (RegValue sym tp') ->
        OverrideSim p sym MIR rtp args ret (PartExpr (Pred sym) (RegValue sym tp'))
    goPartExpr _tpr Unassigned = pure Unassigned
    goPartExpr tpr (PE p v) = PE <$> baseEval BaseBoolRepr p <*> go tpr v

    goVariantBranch :: forall tp' . TypeRepr tp' ->
        VariantBranch sym tp' ->
        OverrideSim p sym MIR rtp args ret (VariantBranch sym tp')
    goVariantBranch tpr (VB pe) = VB <$> goPartExpr tpr pe

    goMuxTreeEntries :: forall tp' a . TypeRepr tp' ->
        [(a, Pred sym)] ->
        OverrideSim p sym MIR rtp args ret a
    goMuxTreeEntries _tpr [] = liftIO $ addFailedAssertion bak $ GenericSimError $
        "empty or incomplete mux tree?"
    goMuxTreeEntries tpr ((x, p) : xs) = do
        p' <- baseEval BaseBoolRepr p
        case asConstantPred p' of
            Just True -> return x
            Just False -> goMuxTreeEntries tpr xs
            Nothing -> liftIO $ addFailedAssertion bak $ GenericSimError $
                "baseEval returned a non-constant predicate?"

    goRefCell :: forall tp' .
        RefCell tp' ->
        OverrideSim p sym MIR rtp args ret (RefCell tp')
    goRefCell rc = do
        let tpr = refType rc
        -- Generate a new refcell to store the evaluated copy.  We don't want
        -- to mutate anything in-place, since `concretize` is meant to be
        -- side-effect-free.
        -- TODO: deduplicate refcells, so structures with sharing don't become
        -- exponentially large
        halloc <- simHandleAllocator <$> use stateContext
        rc' <- liftIO $ freshRefCell halloc tpr

        -- Retrieve the current global state, use it to look up the pointee
        -- value (if it exists), and concretize the pointee value.
        globalState0 <- use $ stateTree.actFrame.gpGlobals
        let pe = lookupRef rc globalState0
        pe' <- goPartExpr tpr pe

        -- Retrieve the current global state again. We must do this in case the
        -- call to goPartExpr above changed the global state further (e.g., in
        -- case we have a reference to another reference).
        globalState1 <- use $ stateTree.actFrame.gpGlobals

        -- Update the global state with the new refcell pointing to the
        -- concretized pointee value.
        let globalState2 = updateRef rc' pe' globalState1
        stateTree.actFrame.gpGlobals .= globalState2

        return rc'

    -- Why does this produce a `RefCell` and not a `GlobalVar`? Producing a
    -- `GlobalVar` makes it challenging to run this conditionally, since we
    -- might end up merging a branch where a `GlobalVar` was created with one
    -- where it wasn't, which causes a panic. Producing a `RefCell` avoids this
    -- problem, because we support merging branches with divergent `RefCell`s.
    goGlobalVar :: forall tp'.
        GlobalVar tp' ->
        OverrideSim p sym MIR rtp args ret (RefCell tp')
    goGlobalVar gv = do
        let nm = globalName gv
        let tpr = globalType gv
        -- Generate a new refcell to store the evaluated copy. We don't
        -- want to mutate anything in-place, since `concretize` is meant to be
        -- side-effect-free.
        -- TODO: deduplicate refcells, so structures with sharing don't
        -- become exponentially large
        halloc <- simHandleAllocator <$> use stateContext
        rc <- liftIO $ freshRefCell halloc tpr

        -- Retrieve the current global state, use it to look up the pointee
        -- value (if it exists), and concretize the pointee value.
        globalState0 <- use $ stateTree.actFrame.gpGlobals
        e <-
          case lookupGlobal gv globalState0 of
            Just e -> pure e
            Nothing ->
              panic
                "regEval"
                [ "GlobalVar with no SymGlobalState entry"
                , Text.unpack nm
                ]
        e' <- go tpr e

        -- Retrieve the current global state again. We must do this in case the
        -- call to `go` above changed the global state further (e.g., in case
        -- we have a reference to another reference).
        globalState1 <- use $ stateTree.actFrame.gpGlobals

        -- Update the global state with the new refcell pointing to the
        -- concretized pointee value.
        let globalState2 = insertRef sym rc e' globalState1
        stateTree.actFrame.gpGlobals .= globalState2

        return rc

    goMirReferenceRoot :: forall tp' .
        MirReferenceRoot sym tp' ->
        OverrideSim p sym MIR rtp args ret (MirReferenceRoot sym tp')
    goMirReferenceRoot (RefCell_RefRoot rc) = RefCell_RefRoot <$> goRefCell rc
    goMirReferenceRoot (GlobalVar_RefRoot gv) =
        -- See `goGlobalVar` for why this returns a `RefCell_RefRoot` instead of
        -- a `GlobalVar_RefRoot`.
        RefCell_RefRoot <$> goGlobalVar gv
    goMirReferenceRoot (Const_RefRoot tpr v) = Const_RefRoot tpr <$> go tpr v

    goMirReferencePath :: forall tp_base tp' .
        MirReferencePath sym tp_base tp' ->
        OverrideSim p sym MIR rtp args ret (MirReferencePath sym tp_base tp')
    goMirReferencePath Empty_RefPath =
        pure Empty_RefPath
    goMirReferencePath (Field_RefPath ctx p idx) =
        Field_RefPath ctx <$> goMirReferencePath p <*> pure idx
    goMirReferencePath (Variant_RefPath discrTp ctx p idx) =
        Variant_RefPath discrTp ctx <$> goMirReferencePath p <*> pure idx
    goMirReferencePath (Just_RefPath tpr p) =
        Just_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (VectorIndex_RefPath tpr p idx) =
        VectorIndex_RefPath tpr <$> goMirReferencePath p <*> go UsizeRepr idx
    goMirReferencePath (ArrayIndex_RefPath btpr p idx) =
        ArrayIndex_RefPath btpr <$> goMirReferencePath p <*> go UsizeRepr idx
    goMirReferencePath (AgElem_RefPath off sz tpr p) =
        AgElem_RefPath <$> go UsizeRepr off <*> pure sz <*> pure tpr <*> goMirReferencePath p

    goMirAggregateEntry ::
        MirAggregateEntry sym ->
        OverrideSim p sym MIR rtp args ret (MirAggregateEntry sym)
    goMirAggregateEntry (MirAggregateEntry sz tpr' rvPart) = do
        rvPart' <- goPartExpr tpr' rvPart
        return $ MirAggregateEntry sz tpr' rvPart'


-- | Override one Rust function with another.
overrideRust ::
  (IsSymInterface sym) =>
  CollectionState ->
  Text ->
  OverrideSim (p sym) sym MIR rtp args ret ()
overrideRust cs name = do
  let tyArgs = cs ^? collection . M.intrinsics . ix (textId name) .
        M.intrInst . M.inSubsts . _Wrapped
  (fDefId, gDefId) <- case tyArgs of
    Just [M.TyFnDef f, M.TyFnDef g] -> return (f, g)
    _ -> error $ "expected two TyFnDef arguments, but got " ++ show tyArgs
  MirHandle _ _ fhF <- case cs ^? handleMap . ix fDefId of
    Just fh -> return fh
    _ -> error $ "failed to get function definition for " ++ show fDefId
  MirHandle _ _ fhG <- case cs ^? handleMap . ix gDefId of
    Just fh -> return fh
    _ -> error $ "failed to get function definition for " ++ show gDefId
  Refl <- case testEquality (handleArgTypes fhF) (handleArgTypes fhG) of
    Just x -> return x
    Nothing -> fail $ "type mismatch: original and override argument lists don't match: " ++
      show (handleArgTypes fhF, handleArgTypes fhG)
  Refl <- case testEquality (handleReturnType fhF) (handleReturnType fhG) of
    Just x -> return x
    Nothing -> fail $ "type mismatch: original and override return types don't match: " ++
      show (handleReturnType fhF, handleReturnType fhG)

  bindFnHandle fhF $ UseOverride $ mkOverride' (handleName fhF) (handleReturnType fhF) $ do
    args <- getOverrideArgs
    regValue <$> callFnVal (HandleFnVal fhG) args


bindFn ::
  forall p msgs args ret blocks sym bak rtp a r.
  (IsSymInterface sym, Logs msgs) =>
  Maybe (SomeOnlineSolver sym bak) ->
  CollectionState ->
  Text ->
  CFG MIR blocks args ret ->
  OverrideSim (p sym) sym MIR rtp a r ()
bindFn symOnline cs name cfg
  | hasInstPrefix ["crucible", "array", "symbolic"] explodedName
  , Empty :> MirSliceRepr <- cfgArgTypes cfg
  , UsizeArrayRepr btpr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    runTypedOverride "array::symbolic" (array_symbolic btpr)

  | hasInstPrefix ["crucible", "concretize"] explodedName
  , Empty :> tpr <- cfgArgTypes cfg
  , Just Refl <- testEquality tpr (cfgReturnType cfg)
  = bindFnHandle (cfgHandle cfg) $ UseOverride $ mkOverride' "concretize" tpr $ concretize symOnline

  | hasInstPrefix ["crucible", "override_"] explodedName
  , Empty :> MirAggregateRepr :> MirAggregateRepr <- cfgArgTypes cfg
  , MirAggregateRepr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "crucible_override_" MirAggregateRepr $ do
        overrideRust cs name
        mirAggregate_zstSim

  | ["crucible", "print_str"] == explodedName
  , Empty :> MirSliceRepr <- cfgArgTypes cfg
  , MirAggregateRepr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "print_str" MirAggregateRepr $ do
        RegMap (Empty :> RegEntry _ strRef) <- getOverrideArgs
        str <- getString strRef >>= \x -> case x of
            Just str -> return str
            Nothing -> fail "print_str: desc string must be concrete"
        liftIO $ outputLn $ Text.unpack str
        mirAggregate_zstSim

  | hasInstPrefix ["crucible", "dump_what4"] explodedName
  , Empty :> MirSliceRepr :> (asBaseType -> AsBaseType _btpr) <- cfgArgTypes cfg
  , MirAggregateRepr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "dump_what4" MirAggregateRepr $ do
        RegMap (Empty :> RegEntry _ strRef :> RegEntry _ expr) <- getOverrideArgs
        str <- getString strRef >>= \x -> case x of
            Just str -> return str
            Nothing -> fail $ "dump_what4: desc string must be concrete"
        liftIO $ outputLn $ Text.unpack str ++ " = " ++ show (printSymExpr expr)
        mirAggregate_zstSim

  | hasInstPrefix ["crucible", "dump_rv"] explodedName
  , Empty :> MirSliceRepr :> tpr <- cfgArgTypes cfg
  , MirAggregateRepr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "dump_rv" MirAggregateRepr $ do
        RegMap (Empty :> RegEntry _ strRef :> RegEntry _ expr) <- getOverrideArgs
        str <- getString strRef >>= \x -> case x of
            Just str -> return str
            Nothing -> fail "dump_rv: desc string must be concrete"
        liftIO $ outputLn $ Text.unpack str ++ " = " ++ showRV @sym tpr expr
        mirAggregate_zstSim

  where
    explodedName = textIdKey name

    -- | Check if @edid@ has the same path as @pfxInit@, plus a final path
    -- component that begins with the name @_inst@.
    hasInstPrefix :: [Text] -> ExplodedDefId -> Bool
    hasInstPrefix pfxInit edid =
      case unsnoc edid of
        Nothing -> False
        Just (edidInit, edidLast) ->
          pfxInit == edidInit &&
          "_inst" `Text.isPrefixOf` edidLast

bindFn _symOnline _cs fn cfg =
  ovrWithBackend $ \bak ->
  case Map.lookup (textIdKey fn) (overrides bak) of
    Nothing -> bindCFG cfg
    Just (SomeTypedOverride o@(TypedOverride _f argTys retTy)) ->
      case (,) <$> testEquality (cfgReturnType cfg) retTy <*> testEquality (cfgArgTypes cfg) argTys of
        Nothing -> error $ "Mismatching override type for " ++ Text.unpack fn ++
                           ".\n\tExpected (" ++ show (cfgArgTypes cfg) ++ ") → " ++ show (cfgReturnType cfg) ++
                           "\n\tbut got (" ++ show argTys ++ ") → (" ++ show retTy ++ ")."
        Just (Refl, Refl) ->
          bindFnHandle (cfgHandle cfg) $ UseOverride (runTypedOverride (functionNameFromText fn) o)

  where
    override ::
      forall args' ret' .
      ExplodedDefId -> CtxRepr args' -> TypeRepr ret' ->
      (forall rtp' args'' ret''.
        Ctx.Assignment (RegValue' sym) args' ->
        OverrideSim (p sym) sym MIR rtp' args'' ret'' (RegValue sym ret')) ->
      (ExplodedDefId, SomeTypedOverride (p sym) sym MIR)
    override edid args ret act =
        ( edid
        , SomeTypedOverride (TypedOverride act args ret)
        )

    u32repr :: TypeRepr (BaseToType (BaseBVType 32))
    u32repr = knownRepr

    strrepr :: TypeRepr MirSlice
    strrepr = knownRepr

    symb_bv :: forall n . (1 <= n)
            => ExplodedDefId -> NatRepr n
            -> (ExplodedDefId, SomeTypedOverride (p sym) sym MIR)
    symb_bv edid n = (edid, SomeTypedOverride $ makeSymbolicVar (BaseBVRepr n))

    overrides :: IsSymBackend sym bak'
              => bak'
              -> Map ExplodedDefId (SomeTypedOverride (p sym) sym MIR)
    overrides bak =
      let sym = backendGetSym bak in
      fromList [ override ["crucible", "one"] Empty (BVRepr (knownNat @8)) $ \_args ->
                 do h <- printHandle <$> getContext
                    liftIO (hPutStrLn h "Hello, I'm an override")
                    v <- liftIO $ bvLit sym knownNat (BV.mkBV knownNat 1)
                    return v
               , (["crucible", "symbolic", "symbolic_bool"], SomeTypedOverride (makeSymbolicVar BaseBoolRepr))
               , symb_bv ["crucible", "symbolic", "symbolic_u8"]  (knownNat @8)
               , symb_bv ["crucible", "symbolic", "symbolic_u16"] (knownNat @16)
               , symb_bv ["crucible", "symbolic", "symbolic_u32"] (knownNat @32)
               , symb_bv ["crucible", "symbolic", "symbolic_u64"] (knownNat @64)
               , symb_bv ["crucible", "symbolic", "symbolic_u128"] (knownNat @128)
               , symb_bv ["int512", "symbolic"] (knownNat @512)
               , symb_bv ["crucible", "bitvector", "make_symbolic_128"] (knownNat @128)
               , symb_bv ["crucible", "bitvector", "make_symbolic_256"] (knownNat @256)
               , symb_bv ["crucible", "bitvector", "make_symbolic_512"] (knownNat @512)

               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override ["crucible", "crucible_assert_impl"] argTys MirAggregateRepr $
                    \(Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) -> do
                       src <- maybe (fail "not a constant src string")
                                (pure . Text.unpack)
                                =<< getString (unRV srcArg)
                       file <- maybe (fail "not a constant filename string") pure =<< getString (unRV fileArg)
                       line <- maybe (fail "not a constant line number") pure
                               (BV.asUnsigned <$> asBV (unRV lineArg))
                       col <- maybe (fail "not a constant column number") pure $
                              (BV.asUnsigned <$> asBV (unRV colArg))
                       let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                       let reason = AssertFailureSimError ("MIR assertion at " <> locStr <> ":\n\t" <> src) ""
                       liftIO $ assert bak (unRV c) reason
                       mirAggregate_zstSim
               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override ["crucible", "crucible_assume_impl"] argTys MirAggregateRepr $
                    \(Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) -> do
                       loc <- liftIO $ getCurrentProgramLoc sym
                       src <- maybe (fail "not a constant src string")
                                (pure . Text.unpack)
                                =<< getString (unRV srcArg)
                       file <- maybe (fail "not a constant filename string") pure =<< getString (unRV fileArg)
                       line <- maybe (fail "not a constant line number") pure
                               (BV.asUnsigned <$> asBV (unRV lineArg))
                       col <- maybe (fail "not a constant column number") pure
                              (BV.asUnsigned <$> asBV (unRV colArg))
                       let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                       let reason = GenericAssumption loc ("Assumption \n\t" <> src <> "\nfrom " <> locStr) (unRV c)
                       liftIO $ addAssumption bak reason
                       mirAggregate_zstSim
               ]


mirReferencePrettyFn :: forall sym. IsSymInterface sym =>
  IntrinsicPrettyFn sym MirReferenceSymbol
-- mirReferencePrettyFn = IntrinsicPrettyFn $ \Ctx.Empty ref -> PP.viaShow ref
mirReferencePrettyFn = IntrinsicPrettyFn $ \tyCtx ref ->
  case tyCtx of
    Ctx.Empty ->
      PP.viaShow ref
    _ Ctx.:> _ ->
      panic "mirReferencePrettyFn" ["Unexpected type context", show tyCtx]

mirAggregatePrettyFn :: forall sym. IsSymInterface sym =>
  IntrinsicPrettyFn sym MirAggregateSymbol
mirAggregatePrettyFn = IntrinsicPrettyFn $ \tyCtx ag ->
  case (tyCtx, ag) of
    (Ctx.Empty, MirAggregate totalSize m) ->
      let kvs = [PP.viaShow off <> ".." <> PP.viaShow (off + sz) PP.<+> "->" PP.<+> ppMaybeRV @sym tpr rv
            | (fromIntegral -> off, MirAggregateEntry sz tpr rv) <- IntMap.toAscList m]
      in
      PP.encloseSep "{" "}" ", " $ kvs ++ ["size" PP.<+> PP.viaShow totalSize]
    (_ Ctx.:> _, _) ->
      panic "mirAggregatePrettyFn" ["Unexpected type context", show tyCtx]

ppMaybeRV ::
  forall sym tpr ann.
  IsSymInterface sym =>
  TypeRepr tpr ->
  RegValue sym (MaybeType tpr) ->
  PP.Doc ann
ppMaybeRV _tpr Unassigned = "<uninit>"
ppMaybeRV tpr (PE p rv)
  | Just True <- asConstantPred p = ppRV @sym tpr rv
  | otherwise = ppRV @sym tpr rv PP.<+> PP.parens ("if" PP.<+> ppRV @sym BoolRepr p)

intrinsicPrinters :: forall sym. IsSymInterface sym => IntrinsicPrinters sym
intrinsicPrinters = IntrinsicPrinters $
  MapF.insert knownRepr mirReferencePrettyFn $
  MapF.insert knownRepr mirAggregatePrettyFn $
  MapF.empty

ppRV :: forall sym tp ann. IsSymInterface sym =>
  TypeRepr tp -> RegValue sym tp -> PP.Doc ann
ppRV tpr rv = ppRegVal intrinsicPrinters tpr (RV @sym rv)

showRV :: forall sym tp. IsSymInterface sym =>
  TypeRepr tp -> RegValue sym tp -> String
showRV tpr rv = show $ ppRV @sym tpr rv
