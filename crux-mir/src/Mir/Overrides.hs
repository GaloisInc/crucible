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

module Mir.Overrides (bindFn) where

import Control.Lens ((^.), (%=), (.=), use)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State (get)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))

import qualified Data.ByteString as BS
import qualified Data.Char as Char
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, catMaybes)
import Data.Semigroup
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word

import System.IO (hPutStrLn)

import Data.Parameterized.Context (pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.NatRepr
import Data.Parameterized.Nonce(withIONonceGenerator, NonceGenerator)
import Data.Parameterized.Some
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC

import qualified What4.Expr.ArrayUpdateMap as AUM
import What4.Expr.GroundEval (GroundValue, GroundEvalFn(..), GroundArray(..))
import What4.FunctionName (FunctionName, functionNameFromText)
import What4.Interface
import What4.LabeledPred (LabeledPred(..))
import What4.Partial (PartExpr, pattern PE, pattern Unassigned, justPartExpr)
import What4.Protocol.Online
    ( OnlineSolver, inNewFrame, solverEvalFuns , solverConn, check
    , getUnsatCore , checkWithAssumptionsAndModel )
import What4.Protocol.SMTWriter
    ( mkFormula, assumeFormulaWithFreshName , assumeFormula
    , smtExprGroundEvalFn )
import What4.SatResult (SatResult(..))

import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.Backend
    ( AssumptionReason(..), IsBoolSolver, LabeledPred(..), addAssumption
    , assert, getPathCondition, Assumption(..), addFailedAssertion, IsSymInterface )
import Lang.Crucible.Backend.Online
import Lang.Crucible.CFG.Core (CFG, cfgArgTypes, cfgHandle, cfgReturnType, lastReg)
import Lang.Crucible.FunctionHandle (RefCell, freshRefCell, refType)
import Lang.Crucible.Simulator (SimErrorReason(..))
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Types
import Lang.Crucible.Utils.MuxTree

import Crux (SomeOnlineSolver(..))
import Crux.Model (addVar, evalModel)
import Crux.Types (Model(..), Vars(..), Vals(..), Entry(..))

import Mir.DefId
import Mir.FancyMuxTree
import Mir.Intrinsics


getString :: forall sym rtp args ret. (IsSymInterface sym) =>
    RegValue sym (MirSlice (BVType 8)) ->
    OverrideSim (Model sym) sym MIR rtp args ret (Maybe Text)
getString (Empty :> RV mirPtr :> RV lenExpr) = runMaybeT $ do
    sym <- lift getSymInterface
    state <- get
    len <- readBV lenExpr
    bytes <- forM [0 .. len - 1] $ \i -> do
        iExpr <- liftIO $ bvLit sym knownRepr i
        elemPtr <- lift $ mirRef_offsetWrapSim knownRepr mirPtr iExpr
        bExpr <- lift $ readMirRefSim knownRepr elemPtr
        b <- readBV bExpr
        return $ fromIntegral b
    return $ Text.decodeUtf8 $ BS.pack bytes

  where
    readBV = MaybeT . return . asUnsignedBV

data SomeOverride p sym where
  SomeOverride :: CtxRepr args -> TypeRepr ret -> Override p sym MIR args ret -> SomeOverride p sym

makeSymbolicVar ::
    (IsSymInterface sym) =>
    RegEntry sym (MirSlice (BVType 8)) ->
    BaseTypeRepr btp ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym (BaseToType btp))
makeSymbolicVar nameReg btpr = do
    sym <- getSymInterface
    nameOpt <- getString $ regValue nameReg
    name <- case nameOpt of
        Just x -> return $ Text.unpack x
        Nothing -> fail "symbolic variable name must be a concrete string"
    nameSymbol <- case userSymbol name of
        Left err -> fail $ "invalid symbolic variable name " ++ show name ++ ": " ++ show err
        Right x -> return x
    v <- liftIO $ freshConstant sym nameSymbol btpr
    loc <- liftIO $ getCurrentProgramLoc sym
    stateContext.cruciblePersonality %= addVar loc name btpr v
    return v

array_symbolic ::
  forall sym rtp btp .
  (IsSymInterface sym) =>
  BaseTypeRepr btp ->
  OverrideSim (Model sym) sym MIR rtp
    (EmptyCtx ::> MirSlice (BVType 8)) (UsizeArrayType btp)
    (RegValue sym (UsizeArrayType btp))
array_symbolic btpr = do
    RegMap (Empty :> nameReg) <- getOverrideArgs
    makeSymbolicVar nameReg $ BaseArrayRepr (Empty :> BaseUsizeRepr) btpr

concretize ::
  forall sym rtp tp .
  (IsSymInterface sym) =>
  Maybe (SomeOnlineSolver sym) ->
  OverrideSim (Model sym) sym MIR rtp (EmptyCtx ::> tp) tp (RegValue sym tp)
concretize (Just SomeOnlineSolver) = do
    (sym :: sym) <- getSymInterface

    GroundEvalFn evalGround <- liftIO $ withSolverProcess sym $ \sp -> do
        cond <- getPathCondition sym
        result <- checkWithAssumptionsAndModel sp "concretize" [cond]
        case result of
            Sat f -> return f
            _ -> addFailedAssertion sym $
                GenericSimError "path is already unreachable"
    let evalBase :: forall bt . BaseTypeRepr bt -> SymExpr sym bt -> IO (SymExpr sym bt)
        evalBase btr v = evalGround v >>= groundExpr sym btr

    RegMap (Empty :> RegEntry tpr val) <- getOverrideArgs
    regEval sym (\btpr exp -> liftIO $ evalBase btpr exp) tpr val
concretize Nothing = fail "`concretize` requires an online solver backend"

groundExpr :: (IsExprBuilder sym, IsBoolSolver sym) => sym ->
    BaseTypeRepr tp -> GroundValue tp -> IO (SymExpr sym tp)
groundExpr sym tpr v = case tpr of
    BaseBoolRepr -> return $ if v then truePred sym else falsePred sym
    BaseNatRepr -> natLit sym v
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
    _ -> addFailedAssertion sym $ GenericSimError $
        "groundExpr: conversion of " ++ show tpr ++ " is not yet implemented"

indexExpr :: (IsExprBuilder sym, IsBoolSolver sym) =>
    sym -> BaseTypeRepr tp -> IndexLit tp -> IO (SymExpr sym tp)
indexExpr sym tpr l = case l of
    NatIndexLit n -> natLit sym n
    BVIndexLit w i -> bvLit sym w i


regEval ::
    forall sym tp rtp args ret .
    (IsSymInterface sym) =>
    sym ->
    (forall bt. BaseTypeRepr bt -> SymExpr sym bt ->
        OverrideSim (Model sym) sym MIR rtp args ret (SymExpr sym bt)) ->
    TypeRepr tp ->
    RegValue sym tp ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp)
regEval sym baseEval tpr v = go tpr v
  where
    go :: forall tp' . TypeRepr tp' -> RegValue sym tp' ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym tp')
    go tpr v | AsBaseType btr <- asBaseType tpr = baseEval btr v

    -- Special case for slices.  The issue here is that we can't evaluate
    -- SymbolicArrayType, but we can evaluate slices of SymbolicArrayType by
    -- evaluating lookups at every index inside the slice bounds.
    go (MirSliceRepr tpr') (Empty :> RV ptr :> RV len) = do
        state <- get

        len' <- go UsizeRepr len
        let lenBV = fromMaybe (error "regEval produced non-concrete BV") $
                asUnsignedBV len'

        vals <- forM [0 .. lenBV - 1] $ \i -> do
            i' <- liftIO $ bvLit sym knownRepr i
            ptr' <- mirRef_offsetSim tpr' ptr i'
            val <- readMirRefSim tpr' ptr'
            go tpr' val

        let vec = MirVector_Vector $ V.fromList vals
        let vecRef = newConstMirRef sym (MirVectorRepr tpr') vec
        ptr <- subindexMirRefSim tpr' vecRef =<< liftIO (bvLit sym knownRepr 0)
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
    go tpr v = liftIO $ addFailedAssertion sym $ GenericSimError $
        "evaluation of " ++ show tpr ++ " is not yet implemented"

    go' :: forall tp' . TypeRepr tp' -> RegValue' sym tp' ->
        OverrideSim (Model sym) sym MIR rtp args ret (RegValue' sym tp')
    go' tpr (RV v) = RV <$> go tpr v

    goFnVal :: forall args' ret' .
        CtxRepr args' -> TypeRepr ret' -> FnVal sym args' ret' ->
        OverrideSim (Model sym) sym MIR rtp args ret (FnVal sym args' ret')
    goFnVal args ret (ClosureFnVal fv tpr v) =
        ClosureFnVal <$> goFnVal (args :> tpr) ret fv <*> pure tpr <*> go tpr v
    goFnVal _ _ (HandleFnVal fh) = pure $ HandleFnVal fh

    goPartExpr :: forall tp' . TypeRepr tp' ->
        PartExpr (Pred sym) (RegValue sym tp') ->
        OverrideSim (Model sym) sym MIR rtp args ret (PartExpr (Pred sym) (RegValue sym tp'))
    goPartExpr tpr Unassigned = pure Unassigned
    goPartExpr tpr (PE p v) = PE <$> baseEval BaseBoolRepr p <*> go tpr v

    goVariantBranch :: forall tp' . TypeRepr tp' ->
        VariantBranch sym tp' ->
        OverrideSim (Model sym) sym MIR rtp args ret (VariantBranch sym tp')
    goVariantBranch tpr (VB pe) = VB <$> goPartExpr tpr pe

    goMuxTreeEntries :: forall tp' a . TypeRepr tp' ->
        [(a, Pred sym)] ->
        OverrideSim (Model sym) sym MIR rtp args ret a
    goMuxTreeEntries tpr [] = liftIO $ addFailedAssertion sym $ GenericSimError $
        "empty or incomplete mux tree?"
    goMuxTreeEntries tpr ((x, pred) : xs) = do
        pred' <- baseEval BaseBoolRepr pred
        case asConstantPred pred' of
            Just True -> return x
            Just False -> goMuxTreeEntries tpr xs
            Nothing -> liftIO $ addFailedAssertion sym $ GenericSimError $
                "baseEval returned a non-constant predicate?"

    goRefCell :: forall tp' .
        RefCell tp' ->
        OverrideSim (Model sym) sym MIR rtp args ret (RefCell tp')
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
        OverrideSim (Model sym) sym MIR rtp args ret (MirReferenceRoot sym tp')
    goMirReferenceRoot (RefCell_RefRoot rc) = RefCell_RefRoot <$> goRefCell rc
    goMirReferenceRoot (GlobalVar_RefRoot gv) =
        liftIO $ addFailedAssertion sym $ GenericSimError $
            "evaluation of GlobalVar_RefRoot is not yet implemented"
    goMirReferenceRoot (Const_RefRoot tpr v) = Const_RefRoot tpr <$> go tpr v

    goMirReferencePath :: forall tp_base tp' .
        MirReferencePath sym tp_base tp' ->
        OverrideSim (Model sym) sym MIR rtp args ret (MirReferencePath sym tp_base tp')
    goMirReferencePath Empty_RefPath =
        pure Empty_RefPath
    goMirReferencePath (Any_RefPath tpr p) =
        Any_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (Field_RefPath ctx p idx) =
        Field_RefPath ctx <$> goMirReferencePath p <*> pure idx
    goMirReferencePath (Variant_RefPath ctx p idx) =
        Variant_RefPath ctx <$> goMirReferencePath p <*> pure idx
    goMirReferencePath (Index_RefPath tpr p idx) =
        Index_RefPath tpr <$> goMirReferencePath p <*> go UsizeRepr idx
    goMirReferencePath (Just_RefPath tpr p) =
        Just_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (VectorAsMirVector_RefPath tpr p) =
        VectorAsMirVector_RefPath tpr <$> goMirReferencePath p
    goMirReferencePath (ArrayAsMirVector_RefPath tpr p) =
        ArrayAsMirVector_RefPath tpr <$> goMirReferencePath p


bindFn ::
  forall args ret blocks sym rtp a r .
  (IsSymInterface sym) =>
  Maybe (SomeOnlineSolver sym) -> Text -> CFG MIR blocks args ret ->
  OverrideSim (Model sym) sym MIR rtp a r ()
bindFn symOnline name cfg
  | (normDefId "crucible::array::symbolic" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> MirSliceRepr (BVRepr w) <- cfgArgTypes cfg
  , UsizeArrayRepr btpr <- cfgReturnType cfg
  , Just Refl <- testEquality w (knownNat @8)
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "array::symbolic" (UsizeArrayRepr btpr) (array_symbolic btpr)
  | (normDefId "crucible::concretize" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> tpr <- cfgArgTypes cfg
  , Just Refl <- testEquality tpr (cfgReturnType cfg)
  = bindFnHandle (cfgHandle cfg) $ UseOverride $ mkOverride' "concretize" tpr $ concretize symOnline
bindFn _symOnline fn cfg =
  getSymInterface >>= \s ->
  case Map.lookup fn (overrides s) of
    Nothing ->
      bindFnHandle (cfgHandle cfg) $ UseCFG cfg (postdomInfo cfg)
    Just (($ functionNameFromText fn) -> SomeOverride argTys retTy f) ->
      case (,) <$> testEquality (cfgReturnType cfg) retTy <*> testEquality (cfgArgTypes cfg) argTys of
        Nothing -> error $ "Mismatching override type for " ++ Text.unpack fn ++
                           ".\n\tExpected (" ++ show (cfgArgTypes cfg) ++ ") → " ++ show (cfgReturnType cfg) ++
                           "\n\tbut got (" ++ show argTys ++ ") → (" ++ show retTy ++ ")."
        Just (Refl, Refl) ->
          bindFnHandle (cfgHandle cfg) $ UseOverride f

  where
    override ::
      forall args ret .
      Text -> CtxRepr args -> TypeRepr ret ->
      (forall rtp . OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym ret)) ->
      (Text, FunctionName -> SomeOverride (Model sym) sym)
    override n args ret act =
        -- Round-trip through `DefId` to normalize the path.  In particular,
        -- this adds the current `defaultDisambiguator` and any missing `[0]`s.
        ( normDefId n
        , \funName -> SomeOverride args ret (mkOverride' funName ret act)
        )

    u8repr :: TypeRepr (BaseToType (BaseBVType 8))
    u8repr = knownRepr

    u32repr :: TypeRepr (BaseToType (BaseBVType 32))
    u32repr = knownRepr

    strrepr :: TypeRepr (MirSlice (BVType 8))
    strrepr = knownRepr

    symb_bv :: forall n . (1 <= n) => Text -> NatRepr n -> (Text, FunctionName -> SomeOverride (Model sym) sym)
    symb_bv name n =
      override name (Empty :> strrepr) (BVRepr n) $
      do RegMap (Empty :> str) <- getOverrideArgs
         makeSymbolicVar str $ BaseBVRepr n

    overrides :: sym -> Map Text (FunctionName -> SomeOverride (Model sym) sym)
    overrides s =
      fromList [ override "crucible::one" Empty (BVRepr (knownNat @ 8)) $
                 do h <- printHandle <$> getContext
                    liftIO (hPutStrLn h "Hello, I'm an override")
                    v <- liftIO $ bvLit (s :: sym) knownNat 1
                    return v
               , symb_bv "crucible::symbolic::symbolic_u8"  (knownNat @ 8)
               , symb_bv "crucible::symbolic::symbolic_u16" (knownNat @ 16)
               , symb_bv "crucible::symbolic::symbolic_u32" (knownNat @ 32)
               , symb_bv "crucible::symbolic::symbolic_u64" (knownNat @ 64)
               , symb_bv "crucible::symbolic::symbolic_u128" (knownNat @ 128)
               , symb_bv "int512::symbolic" (knownNat @ 512)
               , symb_bv "crucible::bitvector::make_symbolic_128" (knownNat @ 128)
               , symb_bv "crucible::bitvector::make_symbolic_256" (knownNat @ 256)
               , symb_bv "crucible::bitvector::make_symbolic_512" (knownNat @ 512)
               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override "crucible::crucible_assert_impl" argTys UnitRepr $
                    do RegMap (Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) <- getOverrideArgs
                       s <- getSymInterface
                       src <- maybe (fail "not a constant src string")
                                (pure . Text.unpack)
                                =<< getString (regValue srcArg)
                       file <- maybe (fail "not a constant filename string") pure =<< getString (regValue fileArg)
                       line <- maybe (fail "not a constant line number") pure (asUnsignedBV (regValue lineArg))
                       col <- maybe (fail "not a constant column number") pure (asUnsignedBV (regValue colArg))
                       let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                       let reason = AssertFailureSimError ("MIR assertion at " <> locStr <> ":\n\t" <> src) ""
                       liftIO $ assert s (regValue c) reason
                       return ()
               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override "crucible::crucible_assume_impl" argTys UnitRepr $
                    do RegMap (Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) <- getOverrideArgs
                       s <- getSymInterface
                       loc <- liftIO $ getCurrentProgramLoc s
                       src <- maybe (fail "not a constant src string")
                                (pure . Text.unpack)
                                =<< getString (regValue srcArg)
                       file <- maybe (fail "not a constant filename string") pure =<< getString (regValue fileArg)
                       line <- maybe (fail "not a constant line number") pure (asUnsignedBV (regValue lineArg))
                       col <- maybe (fail "not a constant column number") pure (asUnsignedBV (regValue colArg))
                       let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                       let reason = AssumptionReason loc $ "Assumption \n\t" <> src <> "\nfrom " <> locStr
                       liftIO $ addAssumption s (LabeledPred (regValue c) reason)
                       return ()
               ]
