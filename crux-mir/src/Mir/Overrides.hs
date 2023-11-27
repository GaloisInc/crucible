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

module Mir.Overrides (bindFn, getString) where

import Control.Lens ((^?), (.=), use, ix, _Wrapped)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State (get)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import Data.List.Extra (unsnoc)
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Vector as V

import System.IO (hPutStrLn)

import Data.Parameterized.Context (pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr

import What4.Config( getOpt, setOpt, getOptionSetting )
import What4.Expr.GroundEval (GroundValue, GroundEvalFn(..), GroundArray(..))
import What4.FunctionName (FunctionName, functionNameFromText)
import What4.Interface
import What4.Partial (PartExpr, pattern PE, pattern Unassigned)
import What4.Protocol.Online ( checkWithAssumptionsAndModel )
import What4.SatResult (SatResult(..))

import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.Backend
    ( CrucibleAssumption(..), IsSymBackend, addAssumption
    , assert, getPathCondition, addFailedAssertion, IsSymInterface
    , singleEvent, addAssumptions, CrucibleEvent(..), backendGetSym
    , throwUnsupported )
import Lang.Crucible.Backend.Online
import Lang.Crucible.CFG.Core (CFG, cfgArgTypes, cfgHandle, cfgReturnType)
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Panic
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Types
import Lang.Crucible.Utils.MuxTree


import Crux (SomeOnlineSolver(..))
import qualified Crux.Overrides as Crux

import Mir.DefId
import Mir.FancyMuxTree
import Mir.Generator (CollectionState, collection, handleMap, MirHandle(..))
import Mir.Intrinsics
import qualified Mir.Mir as M


getString :: forall sym rtp args ret p. (IsSymInterface sym) =>
    RegValue sym (MirSlice (BVType 8)) ->
    OverrideSim p sym MIR rtp args ret (Maybe Text)
getString (Empty :> RV mirPtr :> RV lenExpr) = runMaybeT $ do
    sym <- lift getSymInterface
    state <- get
    len <- readBV lenExpr
    bytes <- forM [0 .. len - 1] $ \i -> do
        iExpr <- liftIO $ bvLit sym knownRepr (BV.mkBV knownRepr i)
        elemPtr <- lift $ mirRef_offsetWrapSim knownRepr mirPtr iExpr
        bExpr <- lift $ readMirRefSim knownRepr elemPtr
        b <- readBV bExpr
        return $ fromIntegral b
    return $ Text.decodeUtf8 $ BS.pack bytes

  where
    readBV e = MaybeT (return (BV.asUnsigned <$> asBV e))

makeSymbolicVar ::
    IsSymInterface sym =>
    BaseTypeRepr btp ->
    TypedOverride (p sym) sym MIR (EmptyCtx ::> MirSlice (BVType 8)) (BaseToType btp)
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
    strrepr :: TypeRepr (MirSlice (BVType 8))
    strrepr = knownRepr

array_symbolic ::
  forall sym rtp btp p .
  (IsSymInterface sym) =>
  BaseTypeRepr btp ->
  TypedOverride (p sym) sym MIR (EmptyCtx ::> MirSlice (BVType 8)) (UsizeArrayType btp)
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

    let onlineDisabled = panic "concretize" ["requires online solving to be enabled"]
    GroundEvalFn evalGround <- liftIO $ withSolverProcess bak onlineDisabled $ \sp -> do
        cond <- getPathCondition bak
        result <- checkWithAssumptionsAndModel sp "concretize" [cond]
        case result of
            Sat f -> return f
            _ -> addFailedAssertion bak $
                   GenericSimError "path is already unreachable"
    let evalBase :: forall bt . BaseTypeRepr bt -> SymExpr sym bt -> IO (SymExpr sym bt)
        evalBase btr v = evalGround v >>= groundExpr sym btr

    RegMap (Empty :> RegEntry tpr val) <- getOverrideArgs
    x <- regEval bak (\btpr exp -> liftIO $ evalBase btpr exp) tpr val

    -- restore the previous setting of the online backend
    _ <- liftIO $ setOpt enabledOpt wasEnabled

    return x

concretize Nothing = fail "`concretize` requires an online solver backend"

groundExpr ::
    IsExprBuilder sym =>
    sym ->
    BaseTypeRepr tp ->
    GroundValue tp ->
    IO (SymExpr sym tp)
groundExpr sym tpr v = case tpr of
    BaseBoolRepr -> return $ if v then truePred sym else falsePred sym
    BaseIntegerRepr -> intLit sym v
    BaseRealRepr -> realLit sym v
    BaseBVRepr w -> bvLit sym w v
    BaseComplexRepr -> mkComplexLit sym v
    BaseStringRepr _ -> stringLit sym v
    -- TODO: this case is implemented, but always hits the `ArrayMapping` case,
    -- which fails.  It seems like z3 always returns a function for array
    -- instances.  Fixing this would require Crucible changes to recognize
    -- the if/else tree used for array instances and produce `ArrayConcrete`
    -- instead of `ArrayMapping` in that case.
    BaseArrayRepr idxTprs tpr' -> case v of
        ArrayMapping _ -> fail "groundExpr: can't convert array backed by function"
        ArrayConcrete dfl vals -> do
            dfl' <- groundExpr sym tpr' dfl
            vals' <- mapM (\(idxs, val) -> do
                idxs' <- Ctx.zipWithM (indexExpr sym) idxTprs idxs
                val' <- groundExpr sym tpr' val
                return (idxs', val')) $ Map.toList vals
            arr0 <- constantArray sym idxTprs dfl'
            foldM (\arr (idxs, val) -> arrayUpdate sym arr idxs val) arr0 vals'
    _ -> throwUnsupported sym $
              "groundExpr: conversion of " ++ show tpr ++ " is not yet implemented"

indexExpr :: IsExprBuilder sym =>
    sym ->
    BaseTypeRepr tp ->
    IndexLit tp ->
    IO (SymExpr sym tp)
indexExpr sym tpr l = case l of
    IntIndexLit n  -> intLit sym n
    BVIndexLit w i -> bvLit sym w i


regEval ::
    forall sym bak tp rtp args ret p .
    (IsSymBackend sym bak) =>
    bak ->
    (forall bt. BaseTypeRepr bt -> SymExpr sym bt ->
        OverrideSim p sym MIR rtp args ret (SymExpr sym bt)) ->
    TypeRepr tp ->
    RegValue sym tp ->
    OverrideSim p sym MIR rtp args ret (RegValue sym tp)
regEval bak baseEval tpr v = go tpr v
  where
    sym = backendGetSym bak

    go :: forall tp' . TypeRepr tp' -> RegValue sym tp' ->
        OverrideSim p sym MIR rtp args ret (RegValue sym tp')
    go tpr v | AsBaseType btr <- asBaseType tpr = baseEval btr v

    -- Special case for slices.  The issue here is that we can't evaluate
    -- SymbolicArrayType, but we can evaluate slices of SymbolicArrayType by
    -- evaluating lookups at every index inside the slice bounds.
    go (MirSliceRepr tpr') (Empty :> RV ptr :> RV len) = do
        state <- get

        len' <- go UsizeRepr len
        let lenBV = BV.asUnsigned $
                    fromMaybe (error "regEval produced non-concrete BV") $
                    asBV len'

        vals <- forM [0 .. lenBV - 1] $ \i -> do
            i' <- liftIO $ bvLit sym knownRepr (BV.mkBV knownRepr i)
            ptr' <- mirRef_offsetSim tpr' ptr i'
            val <- readMirRefSim tpr' ptr'
            go tpr' val

        let vec = MirVector_Vector $ V.fromList vals
        let vecRef = newConstMirRef sym (MirVectorRepr tpr') vec
        ptr <- subindexMirRefSim tpr' vecRef =<< liftIO (bvLit sym knownRepr (BV.zero knownRepr))
        return $ Empty :> RV ptr :> RV len'

    go (FloatRepr fi) v = pure v
    go AnyRepr (AnyValue tpr v) = AnyValue tpr <$> go tpr v
    go UnitRepr () = pure ()
    go CharRepr c = pure c
    go (FunctionHandleRepr args ret) v = goFnVal args ret v
    go (MaybeRepr tpr) pe = goPartExpr tpr pe
    go (VectorRepr tpr) vec = traverse (go tpr) vec
    go (StructRepr ctx) v = Ctx.zipWithM go' ctx v
    go (VariantRepr ctx) v = Ctx.zipWithM goVariantBranch ctx v
    go (ReferenceRepr _tpr) v = do
        -- Can't use `collapseMuxTree` here since it's in the IO monad, not
        -- OverrideSim.
        rc <- goMuxTreeEntries tpr (viewMuxTree v)
        rc' <- goRefCell rc
        return $ toMuxTree sym rc'
    -- TODO: WordMapRepr
    -- TODO: RecursiveRepr
    go (MirReferenceRepr tpr') (MirReferenceMux mux) = do
        ref <- goMuxTreeEntries tpr (viewFancyMuxTree mux)
        ref' <- case ref of
            MirReference root path ->
                MirReference <$> goMirReferenceRoot root <*> goMirReferencePath path
            (MirReference_Integer _tpr i) ->
                MirReference_Integer tpr' <$> go UsizeRepr i
        return $ MirReferenceMux $ toFancyMuxTree sym ref'
    go (MirVectorRepr tpr') vec = case vec of
        MirVector_Vector v -> MirVector_Vector <$> go (VectorRepr tpr') v
        MirVector_Array a
          | AsBaseType btpr' <- asBaseType tpr' ->
            MirVector_Array <$> go (UsizeArrayRepr btpr') a
          | otherwise -> error "unreachable: MirVector_Array elem type is always a base type"
    -- TODO: StringMapRepr
    go tpr v = throwUnsupported sym $
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

    goPartExpr :: forall tp' . TypeRepr tp' ->
        PartExpr (Pred sym) (RegValue sym tp') ->
        OverrideSim p sym MIR rtp args ret (PartExpr (Pred sym) (RegValue sym tp'))
    goPartExpr tpr Unassigned = pure Unassigned
    goPartExpr tpr (PE p v) = PE <$> baseEval BaseBoolRepr p <*> go tpr v

    goVariantBranch :: forall tp' . TypeRepr tp' ->
        VariantBranch sym tp' ->
        OverrideSim p sym MIR rtp args ret (VariantBranch sym tp')
    goVariantBranch tpr (VB pe) = VB <$> goPartExpr tpr pe

    goMuxTreeEntries :: forall tp' a . TypeRepr tp' ->
        [(a, Pred sym)] ->
        OverrideSim p sym MIR rtp args ret a
    goMuxTreeEntries tpr [] = liftIO $ addFailedAssertion bak $ GenericSimError $
        "empty or incomplete mux tree?"
    goMuxTreeEntries tpr ((x, pred) : xs) = do
        pred' <- baseEval BaseBoolRepr pred
        case asConstantPred pred' of
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

        globalState <- use $ stateTree.actFrame.gpGlobals
        let pe = lookupRef rc globalState
        pe' <- goPartExpr tpr pe
        let globalState' = updateRef rc' pe' globalState
        stateTree.actFrame.gpGlobals .= globalState'

        return rc'

    goMirReferenceRoot :: forall tp' .
        MirReferenceRoot sym tp' ->
        OverrideSim p sym MIR rtp args ret (MirReferenceRoot sym tp')
    goMirReferenceRoot (RefCell_RefRoot rc) = RefCell_RefRoot <$> goRefCell rc
    goMirReferenceRoot (GlobalVar_RefRoot gv) =
        throwUnsupported sym $
          "evaluation of GlobalVar_RefRoot is not yet implemented"
    goMirReferenceRoot (Const_RefRoot tpr v) = Const_RefRoot tpr <$> go tpr v

    goMirReferencePath :: forall tp_base tp' .
        MirReferencePath sym tp_base tp' ->
        OverrideSim p sym MIR rtp args ret (MirReferencePath sym tp_base tp')
    goMirReferencePath Empty_RefPath =
        pure Empty_RefPath
    goMirReferencePath (Any_RefPath tpr p) =
        Any_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (Field_RefPath ctx p idx) =
        Field_RefPath ctx <$> goMirReferencePath p <*> pure idx
    goMirReferencePath (Variant_RefPath discrTp ctx p idx) =
        Variant_RefPath discrTp ctx <$> goMirReferencePath p <*> pure idx
    goMirReferencePath (Index_RefPath tpr p idx) =
        Index_RefPath tpr <$> goMirReferencePath p <*> go UsizeRepr idx
    goMirReferencePath (Just_RefPath tpr p) =
        Just_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (VectorAsMirVector_RefPath tpr p) =
        VectorAsMirVector_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (ArrayAsMirVector_RefPath tpr p) =
        ArrayAsMirVector_RefPath tpr <$> goMirReferencePath p


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
  forall p ng args ret blocks sym bak rtp a r.
  (IsSymInterface sym) =>
  Maybe (SomeOnlineSolver sym bak) ->
  CollectionState ->
  Text ->
  CFG MIR blocks args ret ->
  OverrideSim (p sym) sym MIR rtp a r ()
bindFn symOnline cs name cfg
  | hasInstPrefix ["crucible", "array", "symbolic"] explodedName
  , Empty :> MirSliceRepr (BVRepr w) <- cfgArgTypes cfg
  , UsizeArrayRepr btpr <- cfgReturnType cfg
  , Just Refl <- testEquality w (knownNat @8)
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    runTypedOverride "array::symbolic" (array_symbolic btpr)

  | hasInstPrefix ["crucible", "concretize"] explodedName
  , Empty :> tpr <- cfgArgTypes cfg
  , Just Refl <- testEquality tpr (cfgReturnType cfg)
  = bindFnHandle (cfgHandle cfg) $ UseOverride $ mkOverride' "concretize" tpr $ concretize symOnline

  | hasInstPrefix ["crucible", "override_"] explodedName
  , Empty :> UnitRepr :> UnitRepr <- cfgArgTypes cfg
  , UnitRepr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "crucible_override_" UnitRepr $ overrideRust cs name

  | hasInstPrefix ["crucible", "dump_what4"] explodedName
  , Empty :> MirSliceRepr (BVRepr w) :> (asBaseType -> AsBaseType btpr) <- cfgArgTypes cfg
  , Just Refl <- testEquality w (knownNat @8)
  , UnitRepr <- cfgReturnType cfg
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "crucible_override_" UnitRepr $ do
        RegMap (Empty :> RegEntry _ strRef :> RegEntry _ expr) <- getOverrideArgs
        str <- getString strRef >>= \x -> case x of
            Just x -> return x
            Nothing -> fail $ "dump_what4: desc string must be concrete"
        liftIO $ putStrLn $ Text.unpack str ++ " = " ++ show (printSymExpr expr)
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
  let s = backendGetSym bak in
  case Map.lookup (textIdKey fn) (overrides bak) of
    Nothing ->
      bindFnHandle (cfgHandle cfg) $ UseCFG cfg (postdomInfo cfg)
    Just (SomeTypedOverride o@(TypedOverride f argTys retTy)) ->
      case (,) <$> testEquality (cfgReturnType cfg) retTy <*> testEquality (cfgArgTypes cfg) argTys of
        Nothing -> error $ "Mismatching override type for " ++ Text.unpack fn ++
                           ".\n\tExpected (" ++ show (cfgArgTypes cfg) ++ ") → " ++ show (cfgReturnType cfg) ++
                           "\n\tbut got (" ++ show argTys ++ ") → (" ++ show retTy ++ ")."
        Just (Refl, Refl) ->
          bindFnHandle (cfgHandle cfg) $ UseOverride (runTypedOverride (functionNameFromText fn) o)

  where
    override ::
      forall args ret .
      ExplodedDefId -> CtxRepr args -> TypeRepr ret ->
      (forall rtp args' ret'.
        Ctx.Assignment (RegValue' sym) args ->
        OverrideSim (p sym) sym MIR rtp args' ret' (RegValue sym ret)) ->
      (ExplodedDefId, SomeTypedOverride (p sym) sym MIR)
    override edid args ret act =
        ( edid
        , SomeTypedOverride (TypedOverride act args ret)
        )

    u8repr :: TypeRepr (BaseToType (BaseBVType 8))
    u8repr = knownRepr

    u32repr :: TypeRepr (BaseToType (BaseBVType 32))
    u32repr = knownRepr

    strrepr :: TypeRepr (MirSlice (BVType 8))
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
                 in override ["crucible", "crucible_assert_impl"] argTys UnitRepr $
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
                       return ()
               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override ["crucible", "crucible_assume_impl"] argTys UnitRepr $
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
                       return ()
               ]
