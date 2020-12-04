{-# Language GADTs #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}
{-# Language DataKinds #-}
{-# Language TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Mir.ExtractSpec where

import Control.Lens
    (makeLenses, (^.), (^..), (^?), (%=), (.=), (&), (.~), (%~), use, at, ix,
        each, to, folded, _Wrapped)
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import Data.Foldable
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Context (Ctx(..), pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce
import Data.Parameterized.Some
import Data.Reflection
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Vector as V
import Data.Void

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified What4.Expr.Builder as W4
import What4.FunctionName
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.Partial as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Types

import qualified Lang.Crucible.Backend.SAWCore as SAW
import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.Recognizer as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Simulator.Value as SAW
import qualified Verifier.SAW.Simulator.What4 as SAW
import qualified Verifier.SAW.Term.Functor as SAW
import qualified Verifier.SAW.Term.Pretty as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as MS

import qualified Crux.Model as Crux
import Crux.Types (Model)

import Mir.DefId
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M
import Mir.TransTy


-- Declared early for TH

data ArgMatchResult sym = ArgMatchResult
    { _amrEqualities :: [(Some (W4.SymExpr sym), SAW.Term)]
    }

makeLenses ''ArgMatchResult


data Void2

instance PP.Pretty Void2 where
    pretty _ = undefined

type instance MS.HasSetupNull MIR = 'False
type instance MS.HasSetupGlobal MIR = 'False
type instance MS.HasSetupStruct MIR = 'True
type instance MS.HasSetupArray MIR = 'True
type instance MS.HasSetupElem MIR = 'True
type instance MS.HasSetupField MIR = 'True
type instance MS.HasSetupGlobalInitializer MIR = 'False

type instance MS.HasGhostState MIR = 'False

type instance MS.TypeName MIR = Text
type instance MS.ExtType MIR = M.Ty

type instance MS.MethodId MIR = DefId
type instance MS.AllocSpec MIR = Void2
type instance MS.PointsTo MIR = Void2

type instance MS.Codebase MIR = CollectionState

type instance MS.CrucibleContext MIR = ()



builderNew ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    CollectionState ->
    -- | `DefId` of the `builder_new` monomorphization.  Its `Instance` should
    -- have one type argument, which is the `TyFnDef` of the function that the
    -- spec applies to.
    DefId ->
    OverrideSim (Model sym) sym MIR rtp
        EmptyCtx MethodSpecBuilderType (MethodSpecBuilder sym)
builderNew cs defId = do
    sym <- getSymInterface
    snapFrame <- liftIO $ pushAssumptionFrame sym

    let tyArg = cs ^? collection . M.intrinsics . ix defId .
            M.intrInst . M.inSubsts . _Wrapped . ix 0
    fnDefId <- case tyArg of
        Just (M.TyFnDef did) -> return did
        _ -> error $ "expected TyFnDef argument, but got " ++ show tyArg
    let sig = case cs ^? collection . M.functions . ix fnDefId . M.fsig of
            Just x -> x
            _ -> error $ "failed to look up sig of " ++ show fnDefId

    let loc = mkProgramLoc (functionNameFromText $ idText defId) InternalPos
    let ms :: MIRMethodSpec = MS.makeCrucibleMethodSpecIR fnDefId
            (sig ^. M.fsarg_tys) (Just $ sig ^. M.fsreturn_ty) loc cs

    Some retTpr <- return $ tyToRepr $ sig ^. M.fsreturn_ty

    return $ initMethodSpecBuilder ms snapFrame

builderAddArg ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType ::> MirReferenceType tp)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderAddArg = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr builder :> RegEntry (MirReferenceRepr tpr) argRef) <-
        getOverrideArgs

    arg <- readMirRefSim tpr argRef

    return $ builder & msbArgs %~ (Seq.|> Some (MethodSpecValue tpr arg))

builderSetReturn ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType ::> MirReferenceType tp)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderSetReturn = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr builder :> RegEntry (MirReferenceRepr tpr) argRef) <-
        getOverrideArgs

    arg <- readMirRefSim tpr argRef

    return $ builder & msbResult .~ Just (Some (MethodSpecValue tpr arg))

builderGatherAssumes ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderGatherAssumes = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr builder) <- getOverrideArgs

    -- Find all vars that are mentioned in the arguments.
    vars <- liftIO $ gatherVars sym (toList $ builder ^. msbArgs)

    liftIO $ putStrLn $ "found " ++ show (Set.size vars) ++ " relevant variables"
    liftIO $ print vars

    -- Find all assumptions that mention a relevant variable.
    assumes <- liftIO $ collectAssumptions sym
    optAssumes' <- liftIO $ relevantPreds sym vars $
        map (\a -> (a ^. W4.labeledPred, a ^. W4.labeledPredMsg)) $ toList assumes
    let assumes' = case optAssumes' of
            Left (pred, msg, Some v) ->
                error $ "assumption `" ++ show pred ++ "` (" ++ show msg ++
                    ") references variable " ++ show v ++ " (" ++ show (W4.bvarName v) ++ " at " ++
                    show (W4.bvarLoc v) ++ "), which does not appear in the function args"
            Right x -> Seq.fromList $ map fst x

    liftIO $ putStrLn $ "found " ++ show (Seq.length assumes') ++ " relevant assumes, " ++
        show (Seq.length assumes) ++ " total"

    return $ builder & msbPre .~ assumes'

builderGatherAsserts ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderGatherAsserts = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr builder) <- getOverrideArgs

    -- Find all vars that are mentioned in the arguments or return value.
    let args = toList $ builder ^. msbArgs
    let trueValue = MethodSpecValue BoolRepr $ W4.truePred sym
    let result = maybe (Some trueValue) id $ builder ^. msbResult
    vars <- liftIO $ gatherVars sym (result : args)

    liftIO $ putStrLn $ "found " ++ show (Set.size vars) ++ " relevant variables"
    liftIO $ print vars

    -- Find all assertions that mention a relevant variable.
    goals <- liftIO $ proofGoalsToList <$> getProofObligations sym
    let asserts = map proofGoal goals
    optAsserts' <- liftIO $ relevantPreds sym vars $
        map (\a -> (a ^. W4.labeledPred, a ^. W4.labeledPredMsg)) asserts
    let asserts' = case optAsserts' of
            Left (pred, msg, Some v) ->
                error $ "assertion `" ++ show pred ++ "` (" ++ show msg ++
                    ") references variable " ++ show v ++ " (" ++ show (W4.bvarName v) ++ " at " ++
                    show (W4.bvarLoc v) ++ "), which does not appear in the function args"
            Right x -> Seq.fromList $ map fst x

    liftIO $ putStrLn $ "found " ++ show (Seq.length asserts') ++ " relevant asserts, " ++
        show (length asserts) ++ " total"

    return $ builder & msbPost .~ asserts'

-- | Collect all the symbolic variables that appear in `vals`.
gatherVars ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    [Some (MethodSpecValue sym)] ->
    IO (Set (Some (W4.ExprBoundVar t)))
gatherVars sym vals = do
    varsRef <- newIORef Set.empty
    cache <- W4.newIdxCache
    forM_ vals $ \(Some (MethodSpecValue tpr arg)) ->
        visitRegValueExprs sym tpr arg $ \expr ->
            visitExprVars cache expr $ \v ->
                modifyIORef' varsRef $ Set.insert (Some v)
    readIORef varsRef

-- | Collect all the symbolic variables that appear in `preds`.
gatherPredVars ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    [W4.Pred sym] ->
    IO (Set (Some (W4.ExprBoundVar t)))
gatherPredVars sym preds = do
    varsRef <- newIORef Set.empty
    cache <- W4.newIdxCache
    forM_ preds $ \pred ->
        visitExprVars cache pred $ \v ->
            modifyIORef' varsRef $ Set.insert (Some v)
    readIORef varsRef

-- | Collect all the predicates from `preds` that mention at least one variable
-- in `vars`.  Return `Left (pred, info, badVar)` if it finds a predicate
-- `pred` that mentions at least one variable in `vars` along with some
-- `badVar` not in `vars`.
relevantPreds :: forall sym t st fs a.
    (IsSymInterface sym, IsBoolSolver sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    Set (Some (W4.ExprBoundVar t)) ->
    [(W4.Pred sym, a)] ->
    IO (Either (W4.Pred sym, a, Some (W4.ExprBoundVar t)) [(W4.Pred sym, a)])
relevantPreds _sym vars preds = runExceptT $ filterM check preds
  where
    check (pred, info) = do
        sawRel <- lift $ newIORef False
        sawIrrel <- lift $ newIORef Nothing

        cache <- W4.newIdxCache
        lift $ visitExprVars cache pred $ \v ->
            if Set.member (Some v) vars then
                writeIORef sawRel True
            else
                writeIORef sawIrrel (Just $ Some v)
        sawRel' <- lift $ readIORef sawRel
        sawIrrel' <- lift $ readIORef sawIrrel

        case (sawRel', sawIrrel') of
            (True, Just badVar) -> throwError (pred, info, badVar)
            (True, Nothing) -> return True
            (False, _) -> return False


builderFinish :: forall sym t st fs rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType) MethodSpecType MIRMethodSpecWithNonce
builderFinish = do
    RegMap (Empty :> RegEntry _tpr builder) <- getOverrideArgs

    sym <- getSymInterface

    -- TODO: also undo any changes to Crucible global variables / refcells
    liftIO $ popAssumptionFrameAndObligations sym (builder ^. msbSnapshotFrame)

    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    let ng = W4.exprCounter sym
    sawSym <- liftIO $ SAW.newSAWCoreBackend W4.FloatUninterpretedRepr sc ng

    cache <- W4.newIdxCache
    let eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = SAW.evaluateExpr sawSym sc cache x

    preVars <- liftIO $ gatherPredVars sym (toList $ builder ^. msbPre)
    postVars <- liftIO $ gatherPredVars sym (toList $ builder ^. msbPost)
    let postOnlyVars = postVars `Set.difference` preVars

    preVars' <- liftIO $ mapM (\(Some x) -> evalVar eval sc x) $ toList preVars
    postVars' <- liftIO $ mapM (\(Some x) -> evalVar eval sc x) $ toList postOnlyVars

    prePreds' <- liftIO $ mapM (evalTyped eval sc BaseBoolRepr) (builder ^. msbPre)
    postPreds' <- liftIO $ mapM (evalTyped eval sc BaseBoolRepr) (builder ^. msbPost)

    argTts <- liftIO $ mapM (evalSomeRegToSetup sym eval sc) (toList $ builder ^. msbArgs)
    retTt <- liftIO $ mapM (evalSomeRegToSetup sym eval sc) (builder ^. msbResult)
    let argBindings = Map.fromList $ zip [0..] $ zip (builder ^. msbSpec ^. MS.csArgs) argTts

    liftIO $ print $ "finish: " ++ show (Seq.length $ builder ^. msbArgs) ++ " args"
    let loc = builder ^. msbSpec . MS.csLoc
    let ms = builder ^. msbSpec
            & MS.csPreState . MS.csFreshVars .~ preVars'
            & MS.csPreState . MS.csConditions .~ map (MS.SetupCond_Pred loc) (toList prePreds')
            & MS.csPostState . MS.csFreshVars .~ postVars'
            & MS.csPostState . MS.csConditions .~ map (MS.SetupCond_Pred loc) (toList postPreds')
            & MS.csArgBindings .~ argBindings
            & MS.csRetValue .~ retTt
    nonce <- liftIO $ freshNonce ng
    return $ MSN ms (indexValue nonce)

  where
    evalTyped :: forall tp.
        (W4.Expr t tp -> IO SAW.Term) -> SAW.SharedContext ->
        BaseTypeRepr tp -> W4.Expr t tp -> IO SAW.TypedTerm
    evalTyped eval sc _tpr expr = SAW.mkTypedTerm sc =<< eval expr

    evalVar :: forall tp.
        (W4.Expr t tp -> IO SAW.Term) -> SAW.SharedContext ->
        W4.ExprBoundVar t tp -> IO SAW.TypedExtCns
    evalVar eval sc var = do
        tt <- evalTyped eval sc (W4.bvarType var) (W4.BoundVarExpr var)
        case SAW.asTypedExtCns tt of
            Just x -> return x
            Nothing -> error $ "BoundVarExpr translated to non-ExtCns term? " ++ show tt

    evalSomeRegToSetup ::
        sym ->
        (forall tp. W4.Expr t tp -> IO SAW.Term) -> SAW.SharedContext ->
        Some (MethodSpecValue sym) -> IO (MS.SetupValue MIR)
    evalSomeRegToSetup sym eval sc (Some (MethodSpecValue tpr rv)) =
        regToSetup sym (evalTyped eval sc) tpr rv


specPrettyPrint ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecType) (MirSlice (BVType 8)) (RegValue sym (MirSlice (BVType 8)))
specPrettyPrint = do
    RegMap (Empty :> RegEntry _tpr (MSN ms _)) <- getOverrideArgs
    let str = show $ MS.ppMethodSpec ms
    let bytes = Text.encodeUtf8 $ Text.pack str

    sym <- getSymInterface
    len <- liftIO $ W4.bvLit sym knownRepr (BV.mkBV knownRepr $ fromIntegral $ BS.length bytes)

    byteVals <- forM (BS.unpack bytes) $ \b -> do
        liftIO $ W4.bvLit sym (knownNat @8) (BV.mkBV knownRepr $ fromIntegral b)

    let vec = MirVector_Vector $ V.fromList byteVals
    let vecRef = newConstMirRef sym knownRepr vec
    ptr <- subindexMirRefSim knownRepr vecRef =<<
        liftIO (W4.bvLit sym knownRepr (BV.zero knownRepr))
    return $ Empty :> RV ptr :> RV len

specEnable ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    CollectionState ->
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecType) UnitType ()
specEnable cs = do
    RegMap (Empty :> RegEntry _tpr (MSN ms _)) <- getOverrideArgs
    let funcName = ms ^. MS.csMethod
    MirHandle _name sig mh <- case cs ^? handleMap . ix funcName of
        Just x -> return x
        Nothing -> error $ "MethodSpec has bad method name " ++ show (ms ^. MS.csMethod) ++ "?"
    liftIO $ print ("enable spec for", mh)

    bindFnHandle mh $ UseOverride $ mkOverride' (handleName mh) (handleReturnType mh) $
        runSpec mh ms

runSpec :: forall sym t st fs args ret rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    FnHandle args ret -> MIRMethodSpec ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym ret)
runSpec mh ms = do
    liftIO $ print ("in runSpec", ms ^. MS.csMethod)
    sym <- getSymInterface
    RegMap argVals <- getOverrideArgs
    let argVals' = Map.fromList $ zip [0..] $ MS.assignmentToList argVals

    sgs <- readGlobals
    loc <- liftIO $ W4.getCurrentProgramLoc sym
    let freeVars = Set.fromList $
            ms ^.. MS.csPreState . MS.csFreshVars . each . to SAW.tecExt . to SAW.ecVarIndex

    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    let ng = W4.exprCounter sym
    sawSym <- liftIO $ SAW.newSAWCoreBackend W4.FloatUninterpretedRepr sc ng

    cache <- W4.newIdxCache
    let eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = SAW.evaluateExpr sawSym sc cache x

    -- `eval` makes up an arbitrary mapping from `W4.ExprBoundVar` to
    -- `SAW.ExtCns` for all the vars that appear in the arguments.  We need the
    -- reverse mapping to convert back from `SAW.Term` to `W4.Expr`.
    let f :: AnyValue sym -> Some (MethodSpecValue sym)
        f (AnyValue tpr rv) = Some (MethodSpecValue tpr rv)
    w4Vars <- liftIO $ liftM Set.toList $ gatherVars sym $
        map f $ MS.assignmentToList argVals
    w4VarMap <- liftIO $ liftM Map.fromList $ forM w4Vars $ \(Some var) -> do
        let expr = W4.BoundVarExpr var
        term <- eval expr
        ec <- case SAW.asExtCns term of
            Just ec -> return ec
            Nothing -> error "eval on BoundVarExpr produced non-ExtCns?"
        return (SAW.ecVarIndex ec, Some expr)

    -- Generate fresh variables for use in postconditions and result
    let postFresh = ms ^. MS.csPostState . MS.csFreshVars
    w4PostVarMap <- liftM Map.fromList $ forM postFresh $ \tec -> do
        let ec = SAW.tecExt tec
        nameSymbol <- case W4.userSymbol $ SAW.ecName ec of
            Left err -> error $ "w4PostVarMap: failed to convert ExtCns name " ++
                SAW.ecName ec ++ ": " ++ show err
            Right x -> return x
        Some btpr <- liftIO $ termToType sym sc (SAW.ecType ec)
        expr <- liftIO $ W4.freshConstant sym nameSymbol btpr
        stateContext . cruciblePersonality %= Crux.addVar loc (SAW.ecName ec) btpr expr
        return (SAW.ecVarIndex ec, Some expr)

    let retTpr = handleReturnType mh
    retVal <- case ms ^. MS.csRetValue of
        Just sv -> liftIO $ setupToReg sym sc (w4VarMap <> w4PostVarMap) retTpr sv
        Nothing -> case testEquality retTpr UnitRepr of
            Just Refl -> return ()
            Nothing -> error $ "no return value, but return type is " ++ show retTpr

    result <- liftIO $ MS.runOverrideMatcher sym sgs mempty mempty freeVars loc $ do
        -- Match argument SetupValues against argVals
        forM_ (Map.toList $ ms ^. MS.csArgBindings) $ \(i, (_, sv)) -> do
            AnyValue tpr rv <- case argVals' ^? ix i of
                Nothing -> error $ show ("wrong number of args", ms ^. MS.csMethod, i)
                Just x -> return x
            matchArg eval tpr rv sv

        -- Convert preconditions to `osAsserts`
        liftIO $ print ("look at preconditions", length $ ms ^. MS.csPreState . MS.csConditions)
        forM_ (ms ^. MS.csPreState . MS.csConditions) $ \cond -> do
            term <- condTerm sc cond
            pred <- liftIO $ termToPred sym sc w4VarMap term
            MS.addAssert pred $
                SimError loc (AssertFailureSimError (show $ W4.printSymExpr pred) "")

        -- Convert postconditions to `osAssumes`
        liftIO $ print ("look at postconditions", length $ ms ^. MS.csPostState . MS.csConditions)
        forM_ (ms ^. MS.csPostState . MS.csConditions) $ \cond -> do
            term <- condTerm sc cond
            pred <- liftIO $ termToPred sym sc (w4VarMap <> w4PostVarMap) term
            MS.addAssume pred

    ((), os) <- case result of
        Left err -> error $ show err
        Right x -> return x

    liftIO $ print ("termSub", os ^. MS.termSub)

    forM_ (os ^. MS.osAsserts) $ \lp ->
        liftIO $ addAssertion sym lp

    forM_ (os ^. MS.osAssumes) $ \p ->
        liftIO $ addAssumption sym $ W4.LabeledPred p $
            AssumptionReason loc "methodspec postcondition"

    return retVal


-- TODO:
-- - zip RegValue with SetupValue (arg matching)
--   - output a list of RegValue <-> Term equalities
--     - some can be solved by substitution (RegValue = ExtCns)
--     - if these are SAT, then the pattern match can succeed
--   - output MirReference <-> AllocIndex mapping?
--
-- - compute ExtCns substitution (VarIndex -> Term)
--   - needs RegValue -> Term conversion
--
-- - optional: build + check pattern match condition
--   - figure out which variables are still free/symbolic after substitution
--     - add a fresh symbolic var for each one
--   - if the condition SAT, we can assume it to fill in the remaining vars
--
-- - gather specs matching the above & generate branches
--   - if (precond) { fresh <post vars>; assume postcond; return value }
--   - future: also touch all memory modified by the spec


matchArg ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    TypeRepr tp -> RegValue sym tp -> MS.SetupValue MIR ->
    MS.OverrideMatcher' sym MIR rorw ()
matchArg eval (BVRepr w) expr (MS.SetupTerm tt) = do
    loc <- use MS.osLocation
    exprTerm <- liftIO $ eval expr
    var <- case SAW.asExtCns $ SAW.ttTerm tt of
        Just ec -> return $ SAW.ecVarIndex ec
        Nothing -> do
            MS.failure loc $ MS.BadTermMatch (SAW.ttTerm tt) exprTerm
    sub <- use MS.termSub
    when (Map.member var sub) $
        MS.failure loc MS.NonlinearPatternNotSupported
    MS.termSub %= Map.insert var exprTerm
matchArg _eval tpr rv sv = error $ show ("bad matchArg", tpr)

-- | Convert a `SetupCondition` to a boolean `SAW.Term`.
condTerm ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    SAW.SharedContext ->
    MS.SetupCondition MIR ->
    MS.OverrideMatcher' sym MIR rorw SAW.Term
condTerm sc (MS.SetupCond_Equal loc sv1 sv2) = do
    error $ "learnCond SetupCond_Equal NYI" -- TODO
condTerm sc (MS.SetupCond_Pred loc tt) = do
    sub <- use MS.termSub
    t' <- liftIO $ SAW.scInstantiateExt sc sub $ SAW.ttTerm tt
    return t'


regToSetup :: forall sym t st fs tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    (forall tp'. BaseTypeRepr tp' -> W4.Expr t tp' -> IO SAW.TypedTerm) ->
    TypeRepr tp -> RegValue sym tp -> IO (MS.SetupValue MIR)
regToSetup _sym eval tpr rv = go tpr rv
  where
    go :: forall tp'. TypeRepr tp' -> RegValue sym tp' -> IO (MS.SetupValue MIR)
    go (asBaseType -> AsBaseType btpr) expr = MS.SetupTerm <$> eval btpr expr
    go AnyRepr (AnyValue tpr rv) = go tpr rv
    -- TODO: UnitRepr
    -- TODO: MaybeRepr
    -- TODO: VectorRepr
    -- TODO: StructRepr
    -- TODO: VariantRepr
    -- TODO: MirReferenceRepr
    go tpr _ = error $ "regToSetup: can't handle " ++ show tpr

setupToReg :: forall sym t st fs tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    TypeRepr tp ->
    MS.SetupValue MIR ->
    IO (RegValue sym tp)
setupToReg sym sc regMap tpr sv = go tpr sv
  where
    go (asBaseType -> AsBaseType btpr) (MS.SetupTerm term) = do
        Some expr <- termToExpr sym sc regMap (SAW.ttTerm term)
        Refl <- case testEquality (W4.exprType expr) btpr of
            Just x -> return x
            Nothing -> error $ "setupToReg: expected " ++ show btpr ++ ", but got " ++
                show (W4.exprType expr)
        return expr
    go tpr _ = error $ "setupToReg: don't can't handle " ++ show tpr


termToPred :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    IO (W4.Pred sym)
termToPred sym sc varMap term = do
    Some expr <- termToExpr sym sc varMap term
    case W4.exprType expr of
        BaseBoolRepr -> return expr
        btpr -> error $ "termToPred: got result of type " ++ show btpr ++ ", not BaseBoolRepr"

termToExpr :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    SAW.Term ->
    IO (Some (W4.SymExpr sym))
termToExpr sym sc varMap term = do
    modmap <- SAW.scGetModuleMap sc
    let extcns ec = case Map.lookup (SAW.ecVarIndex ec) varMap of
            Just (Some expr) -> case SAW.symExprToValue (W4.exprType expr) expr of
                Just x -> return x
                Nothing -> error $ "termToExpr: failed to convert var " ++
                    SAW.ecName ec ++ " of what4 type " ++ show (W4.exprType expr)
            Nothing -> error $ "termToExpr: unknown variable " ++ SAW.ecName ec
    sv <- give sym $ SAW.w4SolveBasicWithSubst @sym modmap mempty extcns [] term
    case SAW.valueToSymExpr sv of
        Just x -> return x
        Nothing -> error $ "termToExpr: failed to convert SValue"

-- | Convert a `SAW.Term` representing a type to a `W4.BaseTypeRepr`.
termToType :: forall sym t st fs.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym ->
    SAW.SharedContext ->
    SAW.Term ->
    IO (Some W4.BaseTypeRepr)
termToType sym sc term = do
    modmap <- SAW.scGetModuleMap sc
    ref <- newIORef mempty
    sv <- give sym $ SAW.w4SolveBasic @sym modmap mempty ref [] term
    case sv of
        SAW.VBoolType -> return $ Some BaseBoolRepr
        SAW.VVecType (SAW.VNat w) SAW.VBoolType -> do
            Some w <- return $ mkNatRepr w
            LeqProof <- case testLeq (knownNat @1) w of
                Just x -> return x
                Nothing -> error "termToPred: zero-width bitvector"
            return $ Some $ BaseBVRepr w
        SAW.VVecType _ SAW.VBoolType -> error "termToPred: Vec ?? Bool"
        _ -> error $ "termToType: bad SValue"



-- TODO:
-- - find new assumptions between 2 states
-- - collect symbolic vars mentioned in assumptions + function args
-- - find new allocations (RefCells) between 2 states


testExtractPrecondition ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp (EmptyCtx ::> tp) UnitType ()
testExtractPrecondition = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry tpr val) <- getOverrideArgs
    liftIO $ putStrLn $ "hello " ++ show tpr
    cache <- W4.newIdxCache

    liftIO $ putStrLn $ "* visiting argument"
    visitRegValueExprs sym tpr val $ \expr ->
        liftIO $ visitExprVars cache expr $
            \v -> print (W4.bvarName v, W4.bvarType v)

    assumpts <- liftIO $ collectAssumptions sym
    liftIO $ putStrLn $ "* got " ++ show (Seq.length assumpts) ++ " assumptions"
    forM_ assumpts $ \assumpt -> do
        liftIO $ print $ W4.printSymExpr (assumpt ^. W4.labeledPred)
        liftIO $ visitExprVars cache (assumpt ^. W4.labeledPred) $
            \v -> print (W4.bvarName v, W4.bvarType v)

    goals <- liftIO $ proofGoalsToList <$> getProofObligations sym
    liftIO $ putStrLn $ "* got " ++ show (length goals) ++ " assertions"
    forM_ goals $ \goal -> do
        let pred = proofGoal goal ^. W4.labeledPred
        liftIO $ print $ W4.printSymExpr pred
        liftIO $ visitExprVars cache pred $
            \v -> print (W4.bvarName v, W4.bvarType v)

-- | Run `f` on each `SymExpr` in `v`.
visitRegValueExprs ::
    forall sym tp m.
    Monad m =>
    sym ->
    TypeRepr tp ->
    RegValue sym tp ->
    (forall btp. W4.SymExpr sym btp -> m ()) ->
    m ()
visitRegValueExprs _sym tpr_ v_ f = go tpr_ v_
  where
    go :: forall tp'. TypeRepr tp' -> RegValue sym tp' -> m ()
    go tpr v | AsBaseType btpr <- asBaseType tpr = f v
    go AnyRepr (AnyValue tpr' v') = go tpr' v'
    go UnitRepr () = return ()
    go (MaybeRepr tpr') W4.Unassigned = return ()
    go (MaybeRepr tpr') (W4.PE p v') = f p >> go tpr' v'
    go (VectorRepr tpr') vec = mapM_ (go tpr') vec
    go (StructRepr ctxr) fields = forMWithRepr_ ctxr fields $ \tpr' (RV v') -> go tpr' v'
    go (VariantRepr ctxr) variants = forMWithRepr_ ctxr variants $ \tpr' (VB pe) -> case pe of
        W4.Unassigned -> return ()
        W4.PE p v' -> f p >> go tpr' v'
    go tpr _ = error $ "visitRegValueExprs: unsupported: " ++ show tpr

    forMWithRepr_ :: forall ctx m f. Monad m =>
        CtxRepr ctx -> Ctx.Assignment f ctx -> (forall tp. TypeRepr tp -> f tp -> m ()) -> m ()
    forMWithRepr_ ctxr assn f = void $
        Ctx.zipWithM (\x y -> f x y >> return (Const ())) ctxr assn


-- | Run `f` on each free symbolic variable in `e`.
visitExprVars ::
    forall t tp m.
    W4.IdxCache t (Const ()) ->
    W4.Expr t tp ->
    (forall tp'. W4.ExprBoundVar t tp' -> IO ()) ->
    IO ()
visitExprVars cache e f = go Set.empty e
  where
    go :: Set (Some (W4.ExprBoundVar t)) -> W4.Expr t tp' -> IO ()
    go bound e = void $ W4.idxCacheEval cache e (go' bound e >> return (Const ()))

    go' :: Set (Some (W4.ExprBoundVar t)) -> W4.Expr t tp' -> IO ()
    go' bound e = case e of
        W4.BoundVarExpr v
          | not $ Set.member (Some v) bound -> f v
          | otherwise -> return ()
        W4.NonceAppExpr nae -> case W4.nonceExprApp nae of
            W4.Forall v e' -> go (Set.insert (Some v) bound) e'
            W4.Exists v e' -> go (Set.insert (Some v) bound) e'
            W4.Annotation _ _ e' -> go bound e'
            W4.ArrayFromFn _ -> error "unexpected ArrayFromFn"
            W4.MapOverArrays _ _ _ -> error "unexpected MapOverArrays"
            W4.ArrayTrueOnEntries _ _ -> error "unexpected ArrayTrueOnEntries"
            W4.FnApp _ _ -> error "unexpected FnApp"
        W4.AppExpr ae ->
            void $ W4.traverseApp (\e' -> go bound e' >> return e') $ W4.appExprApp ae
        W4.StringExpr _ _ -> return ()
        W4.BoolExpr _ _ -> return ()
        W4.SemiRingLiteral _ _ _ -> return ()
