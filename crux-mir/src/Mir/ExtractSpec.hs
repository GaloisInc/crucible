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
import Data.Parameterized.Context (Ctx(..), pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce
import Data.Parameterized.Pair
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
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
import GHC.Stack (HasCallStack)

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified What4.Expr.Builder as W4
import What4.FunctionName
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.Partial as W4
import What4.ProgramLoc

import Lang.Crucible.Backend
import Lang.Crucible.Backend.AssumptionStack (FrameIdentifier)
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


-- | A `RegValue` and its associated `TypeRepr`.
data MethodSpecValue sym tp = MethodSpecValue (TypeRepr tp) (RegValue sym tp)

data BuilderState sym t = BuilderState
    { _msbSpec :: MIRMethodSpec
    , _msbPre :: StateExtra sym t
    , _msbPost :: StateExtra sym t
    , _msbSnapshotFrame :: FrameIdentifier
    }

data StateExtra sym t = StateExtra
    { _seVars :: Set (Some (W4.ExprBoundVar t))
    , _seConds :: Seq (W4.Pred sym)
    }

initBuilderState :: MIRMethodSpec -> FrameIdentifier -> BuilderState sym t
initBuilderState spec snap = BuilderState
    { _msbSpec = spec
    , _msbPre = initStateExtra
    , _msbPost = initStateExtra
    , _msbSnapshotFrame = snap
    }

initStateExtra :: StateExtra sym t
initStateExtra = StateExtra
    { _seVars = Set.empty
    , _seConds = Seq.empty
    }

makeLenses ''BuilderState
makeLenses ''StateExtra


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



builderNew :: forall sym t st fs rtp.
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
    let state = initBuilderState ms snapFrame

    -- Common utilities shared by several methods.
    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    let ng = W4.exprCounter sym
    sawSym <- liftIO $ SAW.newSAWCoreBackend W4.FloatUninterpretedRepr sc ng

    cache <- W4.newIdxCache
    let eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = SAW.evaluateExpr sawSym sc cache x

    let col = cs ^. collection

    let methods = MethodSpecBuilderMethods
            { _msbmAddArg = builderAddArgImpl col sc eval
            , _msbmSetReturn = builderSetReturnImpl col sc eval
            , _msbmGatherAssumes = builderGatherAssumesImpl sc eval
            , _msbmGatherAsserts = builderGatherAssertsImpl sc eval
            , _msbmFinish = builderFinishImpl col sc ng eval
            }

    return $ MethodSpecBuilder state methods

builderAddArg ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType ::> MirReferenceType tp)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderAddArg = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder s ms)
        :> RegEntry (MirReferenceRepr tpr) argRef) <- getOverrideArgs
    s' <- (ms ^. msbmAddArg) tpr argRef s
    return $ MethodSpecBuilder s' ms

builderSetReturn ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType ::> MirReferenceType tp)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderSetReturn = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder s ms)
        :> RegEntry (MirReferenceRepr tpr) argRef) <- getOverrideArgs
    s' <- (ms ^. msbmSetReturn) tpr argRef s
    return $ MethodSpecBuilder s' ms

builderGatherAssumes ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderGatherAssumes = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder s ms)) <- getOverrideArgs
    s' <- (ms ^. msbmGatherAssumes) s
    return $ MethodSpecBuilder s' ms

builderGatherAsserts ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType)
        MethodSpecBuilderType
        (MethodSpecBuilder sym)
builderGatherAsserts = do
    sym <- getSymInterface
    RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder s ms)) <- getOverrideArgs
    s' <- (ms ^. msbmGatherAsserts) s
    return $ MethodSpecBuilder s' ms

builderFinish :: forall sym t st fs rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection ->
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType) MethodSpecType MIRMethodSpecWithNonce
builderFinish col = do
    RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder s ms)) <- getOverrideArgs
    msn <- (ms ^. msbmFinish) s
    return msn


builderAddArgImpl :: forall sym t st fs p rtp args ret tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection -> SAW.SharedContext ->
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    TypeRepr tp -> MirReferenceMux sym tp -> BuilderState sym t ->
    OverrideSim p sym MIR rtp args ret (BuilderState sym t)
builderAddArgImpl col sc eval tpr argRef builder = do
    sym <- getSymInterface

    let idx = Map.size $ builder ^. msbSpec . MS.csArgBindings
    let ty = case builder ^? msbSpec . MS.csArgs . ix idx of
            Just x -> x
            Nothing -> error $ "arg index out of range: " ++ show idx
    let shp = tyToShapeEq col ty tpr

    rv <- readMirRefSim tpr argRef
    vars <- liftIO $ gatherVars sym [Some (MethodSpecValue tpr rv)]
    sv <- liftIO $ regToSetup sym (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

    return $ builder
        & msbSpec . MS.csArgBindings . at (fromIntegral idx) .~ Just (ty, sv)
        & msbPre . seVars %~ Set.union vars

builderSetReturnImpl :: forall sym t st fs p rtp args ret tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection -> SAW.SharedContext ->
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    TypeRepr tp -> MirReferenceMux sym tp -> BuilderState sym t ->
    OverrideSim p sym MIR rtp args ret (BuilderState sym t)
builderSetReturnImpl col sc eval tpr argRef builder = do
    sym <- getSymInterface

    let ty = case builder ^. msbSpec . MS.csRet of
            Just x -> x
            Nothing -> M.TyTuple []
    let shp = tyToShapeEq col ty tpr

    rv <- readMirRefSim tpr argRef
    vars <- liftIO $ gatherVars sym [Some (MethodSpecValue tpr rv)]
    sv <- liftIO $ regToSetup sym (\_tpr expr -> SAW.mkTypedTerm sc =<< eval expr) shp rv

    return $ builder
        & msbSpec . MS.csRetValue .~ Just sv
        & msbPost . seVars %~ Set.union vars

builderGatherAssumesImpl :: forall sym t st fs p rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    SAW.SharedContext -> (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    BuilderState sym t ->
    OverrideSim p sym MIR rtp args ret (BuilderState sym t)
builderGatherAssumesImpl sc eval builder = do
    sym <- getSymInterface

    -- Find all vars that are mentioned in the arguments.
    let vars = builder ^. msbPre . seVars

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
            Right x -> map fst x

    let loc = builder ^. msbSpec . MS.csLoc
    assumeConds <- liftIO $ forM assumes' $ \pred -> do
        tt <- eval pred >>= SAW.mkTypedTerm sc
        return $ MS.SetupCond_Pred loc tt
    newVars <- liftIO $ gatherVars sym [Some (MethodSpecValue BoolRepr pred) | pred <- assumes']

    liftIO $ putStrLn $ "found " ++ show (length assumes') ++ " relevant assumes, " ++
        show (Seq.length assumes) ++ " total"

    return $ builder
        & msbSpec . MS.csPreState . MS.csConditions %~ (++ assumeConds)
        & msbPre . seVars %~ Set.union newVars

builderGatherAssertsImpl :: forall sym t st fs p rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    SAW.SharedContext -> (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    BuilderState sym t ->
    OverrideSim p sym MIR rtp args ret (BuilderState sym t)
builderGatherAssertsImpl sc eval builder = do
    sym <- getSymInterface

    -- Find all vars that are mentioned in the arguments or return value.
    let vars = (builder ^. msbPre . seVars) `Set.union` (builder ^. msbPost . seVars)

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
            Right x -> map fst x

    let loc = builder ^. msbSpec . MS.csLoc
    assertConds <- liftIO $ forM asserts' $ \pred -> do
        tt <- eval pred >>= SAW.mkTypedTerm sc
        return $ MS.SetupCond_Pred loc tt
    newVars <- liftIO $ gatherVars sym [Some (MethodSpecValue BoolRepr pred) | pred <- asserts']

    liftIO $ putStrLn $ "found " ++ show (length asserts') ++ " relevant asserts, " ++
        show (length asserts) ++ " total"

    return $ builder
        & msbSpec . MS.csPostState . MS.csConditions %~ (++ assertConds)
        & msbPost . seVars %~ Set.union newVars


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


builderFinishImpl :: forall sym t st fs p rtp args ret.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection -> SAW.SharedContext -> NonceGenerator IO t ->
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    BuilderState sym t ->
    OverrideSim p sym MIR rtp args ret MIRMethodSpecWithNonce
builderFinishImpl col sc ng eval builder = do
    sym <- getSymInterface

    -- TODO: also undo any changes to Crucible global variables / refcells
    liftIO $ popAssumptionFrameAndObligations sym (builder ^. msbSnapshotFrame)

    let preVars = builder ^. msbPre . seVars
    let postVars = builder ^. msbPost . seVars
    let postOnlyVars = postVars `Set.difference` preVars

    preVars' <- liftIO $ mapM (\(Some x) -> evalVar eval sc x) $ toList preVars
    postVars' <- liftIO $ mapM (\(Some x) -> evalVar eval sc x) $ toList postOnlyVars

    let loc = builder ^. msbSpec . MS.csLoc
    let ms = builder ^. msbSpec
            & MS.csPreState . MS.csFreshVars .~ preVars'
            & MS.csPostState . MS.csFreshVars .~ postVars'
    nonce <- liftIO $ freshNonce ng
    return $ MSN ms (indexValue nonce)

  where
    evalVar :: forall tp.
        (W4.Expr t tp -> IO SAW.Term) -> SAW.SharedContext ->
        W4.ExprBoundVar t tp -> IO SAW.TypedExtCns
    evalVar eval sc var = do
        tt <- eval (W4.BoundVarExpr var) >>= SAW.mkTypedTerm sc
        case SAW.asTypedExtCns tt of
            Just x -> return x
            Nothing -> error $ "BoundVarExpr translated to non-ExtCns term? " ++ show tt


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
        runSpec (cs ^. collection) mh ms

runSpec :: forall sym t st fs args ret rtp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection -> FnHandle args ret -> MIRMethodSpec ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym ret)
runSpec col mh ms = do
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
    liftIO $ print ("add fresh vars for result/postcond", map (SAW.ecName . SAW.tecExt) postFresh)
    w4PostVarMap <- liftM Map.fromList $ forM postFresh $ \tec -> do
        let ec = SAW.tecExt tec
        nameSymbol <- case W4.userSymbol $ SAW.ecName ec of
            Left err -> error $ "w4PostVarMap: failed to convert ExtCns name " ++
                SAW.ecName ec ++ ": " ++ show err
            Right x -> return x
        Some btpr <- liftIO $ termToType sym sc (SAW.ecType ec)
        liftIO $ print ("fresh post var", nameSymbol, btpr)
        expr <- liftIO $ W4.freshConstant sym nameSymbol btpr
        stateContext . cruciblePersonality %= Crux.addVar loc (SAW.ecName ec) btpr expr
        return (SAW.ecVarIndex ec, Some expr)

    let retTy = maybe (M.TyTuple []) id $ ms ^. MS.csRet
    let retTpr = handleReturnType mh
    let retShp = tyToShapeEq col retTy retTpr
    retVal <- case ms ^. MS.csRetValue of
        Just sv -> liftIO $ setupToReg sym sc (w4VarMap <> w4PostVarMap) retShp sv
        Nothing -> case testEquality retTpr UnitRepr of
            Just Refl -> return ()
            Nothing -> error $ "no return value, but return type is " ++ show retTpr

    result <- liftIO $ MS.runOverrideMatcher sym sgs mempty mempty freeVars loc $ do
        -- Match argument SetupValues against argVals
        forM_ (Map.toList $ ms ^. MS.csArgBindings) $ \(i, (_, sv)) -> do
            ty <- case ms ^. MS.csArgs ^? ix (fromIntegral i) of
                Nothing -> error $ show ("wrong number of args", ms ^. MS.csMethod, i)
                Just x -> return x
            AnyValue tpr rv <- case argVals' ^? ix i of
                Nothing -> error $ show ("wrong number of args", ms ^. MS.csMethod, i)
                Just x -> return x
            let shp = tyToShapeEq col ty tpr
            matchArg sym eval shp rv sv

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
    forall sym t st fs tp rorw.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    (forall tp'. W4.Expr t tp' -> IO SAW.Term) ->
    TypeShape tp -> RegValue sym tp -> MS.SetupValue MIR ->
    MS.OverrideMatcher' sym MIR rorw ()
matchArg sym eval shp rv sv = go shp rv sv
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp -> MS.SetupValue MIR ->
        MS.OverrideMatcher' sym MIR rorw ()
    go (UnitShape _) () (MS.SetupStruct () False []) = return ()
    go (PrimShape _ btpr) expr (MS.SetupTerm tt) = do
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
    go (TupleShape _ _ flds) rvs (MS.SetupStruct () False svs) = goFields flds rvs svs
    go (ArrayShape _ _ shp) vec (MS.SetupArray () svs) = case vec of
        MirVector_Vector v -> zipWithM_ (go shp) (toList v) svs
        MirVector_PartialVector pv -> forM_ (zip (toList pv) svs) $ \(p, sv) -> do
            rv <- liftIO $ accessPartial sym "vector element" (shapeType shp) p
            go shp rv sv
        MirVector_Array _ -> error $ "matchArg: MirVector_Array NYI"
    go (StructShape _ _ flds) (AnyValue tpr rvs) (MS.SetupStruct () False svs)
      | Just Refl <- testEquality tpr shpTpr = goFields flds rvs svs
      | otherwise = error $ "matchArg: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go shp _ _ = error $ "matchArg: type error: bad SetupValue for " ++ show (shapeType shp)

    goFields :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
        [MS.SetupValue MIR] -> MS.OverrideMatcher' sym MIR rorw ()
    goFields flds rvs svs = loop flds rvs (reverse svs)
      where
        loop :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
            [MS.SetupValue MIR] -> MS.OverrideMatcher' sym MIR rorw ()
        loop Empty Empty [] = return ()
        loop (flds :> fld) (rvs :> RV rv) (sv : svs) = do
            case fld of
                ReqField shp -> go shp rv sv
                OptField shp -> do
                    rv' <- liftIO $ accessPartial sym "field" (shapeType shp) rv
                    go shp rv' sv
            loop flds rvs svs
        loop _ rvs svs = error $ "matchArg: type error: got RegValues for " ++
            show (Ctx.sizeInt $ Ctx.size rvs) ++ " fields, but got " ++
            show (length svs) ++ " SetupValues"

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
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    (forall tp'. BaseTypeRepr tp' -> W4.Expr t tp' -> IO SAW.TypedTerm) ->
    TypeShape tp -> RegValue sym tp -> IO (MS.SetupValue MIR)
regToSetup sym eval shp rv = go shp rv
  where
    go :: forall tp. TypeShape tp -> RegValue sym tp -> IO (MS.SetupValue MIR)
    go (UnitShape _) () = return $ MS.SetupStruct () False []
    go (PrimShape _ btpr) expr = MS.SetupTerm <$> eval btpr expr
    go (TupleShape _ _ flds) rvs = MS.SetupStruct () False <$> goFields flds rvs
    go (ArrayShape _ _ shp) vec = do
        svs <- case vec of
            MirVector_Vector v -> mapM (go shp) (toList v)
            MirVector_PartialVector v -> forM (toList v) $ \p -> do
                rv <- accessPartial sym "vector element" (shapeType shp) p
                go shp rv
            MirVector_Array _ -> error $ "regToSetup: MirVector_Array NYI"
        return $ MS.SetupArray () svs
    go (StructShape _ _ flds) (AnyValue tpr rvs)
      | Just Refl <- testEquality tpr shpTpr =
        MS.SetupStruct () False <$> goFields flds rvs
      | otherwise = error $ "regToSetup: type error: expected " ++ show shpTpr ++
        ", but got Any wrapping " ++ show tpr
      where shpTpr = StructRepr $ fmapFC fieldShapeType flds
    go (RefShape _ tpr) _ = error $ "regToSetup: RefShape NYI"

    goFields :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
        IO [MS.SetupValue MIR]
    goFields flds rvs = loop flds rvs []
      where
        loop :: forall ctx. Assignment FieldShape ctx -> Assignment (RegValue' sym) ctx ->
            [MS.SetupValue MIR] -> IO [MS.SetupValue MIR]
        loop Empty Empty svs = return svs
        loop (flds :> fld) (rvs :> RV rv) svs = do
            sv <- case fld of
                ReqField shp -> go shp rv
                OptField shp -> accessPartial sym "field" (shapeType shp) rv >>= go shp
            loop flds rvs (sv : svs)

readPartial :: IsSymInterface sym => sym -> W4.PartExpr (W4.Pred sym) a -> IO (Maybe a)
readPartial sym W4.Unassigned = return Nothing
readPartial sym (W4.PE p v)
  | Just True <- W4.asConstantPred p = return $ Just v
  | otherwise = return Nothing

accessPartial :: forall tp sym. IsSymInterface sym =>
    sym -> String -> TypeRepr tp -> RegValue sym (MaybeType tp) ->
    IO (RegValue sym tp)
accessPartial sym desc tpr rv = readPartial sym rv >>= \x -> case x of
    Just x -> return x
    Nothing -> error $ "regToSetup: accessed possibly-uninitialized " ++ desc ++
        " of type " ++ show tpr

setupToReg :: forall sym t st fs tp.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
    sym ->
    SAW.SharedContext ->
    Map SAW.VarIndex (Some (W4.Expr t)) ->
    TypeShape tp ->
    MS.SetupValue MIR ->
    IO (RegValue sym tp)
setupToReg sym sc regMap shp sv = go shp sv
  where
    go :: forall tp. TypeShape tp -> MS.SetupValue MIR -> IO (RegValue sym tp)
    go (UnitShape _) (MS.SetupStruct _ False []) = return ()
    go (PrimShape _ btpr) (MS.SetupTerm tt) = do
        Some expr <- termToExpr sym sc regMap (SAW.ttTerm tt)
        Refl <- case testEquality (W4.exprType expr) btpr of
            Just x -> return x
            Nothing -> error $ "setupToReg: expected " ++ show btpr ++ ", but got " ++
                show (W4.exprType expr)
        return expr
    go (TupleShape _ _ flds) (MS.SetupStruct _ False svs) = goFields flds svs
    go (ArrayShape _ _ shp) (MS.SetupArray _ svs) = do
        rvs <- mapM (go shp) svs
        return $ MirVector_Vector $ V.fromList rvs
    go (StructShape _ _ flds) (MS.SetupStruct _ False svs) =
        AnyValue (StructRepr $ fmapFC fieldShapeType flds) <$> goFields flds svs
    go shp sv = error $ "setupToReg: type error: bad SetupValue for " ++ show (shapeType shp) ++
        ": " ++ show (MS.ppSetupValue sv)

    goFields :: forall ctx. Assignment FieldShape ctx -> [MS.SetupValue MIR] ->
        IO (Assignment (RegValue' sym) ctx)
    goFields shps svs = loop shps (reverse svs)
      where
        loop :: forall ctx. Assignment FieldShape ctx -> [MS.SetupValue MIR] ->
            IO (Assignment (RegValue' sym) ctx)
        loop Empty [] = return Empty
        loop (shps :> shp) (sv : svs) = do
            rv <- case shp of
                ReqField shp' -> go shp' sv
                OptField shp' -> W4.justPartExpr sym <$> go shp' sv
            rvs <- loop shps svs
            return $ rvs :> RV rv


data TypeShape (tp :: CrucibleType) where
    UnitShape :: M.Ty -> TypeShape UnitType
    PrimShape :: M.Ty -> BaseTypeRepr btp -> TypeShape (BaseToType btp)
    TupleShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape (StructType ctx)
    ArrayShape :: M.Ty -> M.Ty -> TypeShape tp -> TypeShape (MirVectorType tp)
    StructShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape AnyType
    RefShape :: M.Ty -> TypeRepr tp -> TypeShape (MirReferenceType tp)

data FieldShape (tp :: CrucibleType) where
    OptField :: TypeShape tp -> FieldShape (MaybeType tp)
    ReqField :: TypeShape tp -> FieldShape tp

-- | Return the `TypeShape` of `ty`.
--
-- It is guaranteed that the `tp :: CrucibleType` index of the resulting
-- `TypeShape` matches that returned by `tyToRepr`.
tyToShape :: M.Collection -> M.Ty -> Some TypeShape
tyToShape col ty = go ty
  where
    go :: M.Ty -> Some TypeShape
    go ty = case ty of
        M.TyBool -> goPrim ty
        M.TyChar -> goPrim ty
        M.TyInt _ -> goPrim ty
        M.TyUint _ -> goPrim ty
        M.TyTuple [] -> goUnit ty
        M.TyTuple tys -> goTuple ty tys
        M.TyClosure tys -> goTuple ty tys
        M.TyFnDef _ -> goUnit ty
        M.TyArray ty' _ | Some shp <- go ty' -> Some $ ArrayShape ty ty' shp
        M.TyAdt nm _ _ -> case Map.lookup nm (col ^. M.adts) of
            Just (M.Adt _ M.Struct [v] _ _) -> goStruct ty (v ^.. M.vfields . each . M.fty)
            Just (M.Adt _ ak _ _ _) -> error $ "tyToShape: AdtKind " ++ show ak ++ " NYI"
            Nothing -> error $ "tyToShape: bad adt: " ++ show ty
        M.TyRef ty' mutbl -> goRef ty ty' mutbl
        M.TyRawPtr ty' mutbl -> goRef ty ty' mutbl
        _ -> error $ "tyToShape: " ++ show ty ++ " NYI"

    goPrim :: M.Ty -> Some TypeShape
    goPrim ty | Some tpr <- tyToRepr ty, AsBaseType btpr <- asBaseType tpr =
        Some $ PrimShape ty btpr

    goUnit :: M.Ty -> Some TypeShape
    goUnit ty = Some $ UnitShape ty

    goTuple :: M.Ty -> [M.Ty] -> Some TypeShape
    goTuple ty tys | Some flds <- loop tys Empty = Some $ TupleShape ty tys flds
      where
        loop :: forall ctx. [M.Ty] -> Assignment FieldShape ctx -> Some (Assignment FieldShape)
        loop [] flds = Some flds
        loop (ty:tys) flds | Some fld <- go ty = loop tys (flds :> OptField fld)

    goStruct :: M.Ty -> [M.Ty] -> Some TypeShape
    goStruct ty tys | Some flds <- loop tys Empty = Some $ StructShape ty tys flds
      where
        loop :: forall ctx. [M.Ty] -> Assignment FieldShape ctx -> Some (Assignment FieldShape)
        loop [] flds = Some flds
        loop (ty:tys) flds | Some fld <- goField ty = loop tys (flds :> fld)

    goField :: M.Ty -> Some FieldShape
    goField ty | Some shp <- go ty = case canInitialize ty of
        True -> Some $ ReqField shp
        False -> Some $ OptField shp

    goRef :: M.Ty -> M.Ty -> M.Mutability -> Some TypeShape
    goRef ty ty' _ | isUnsized ty' = error $
        "tyToShape: fat pointer " ++ show ty ++ " NYI"
    goRef ty ty' _ | Some tpr <- tyToRepr ty' = Some $ RefShape ty tpr

-- | Given a `Ty` and the result of `tyToRepr ty`, produce a `TypeShape` with
-- the same index `tp`.  Raises an `error` if the `TypeRepr` doesn't match
-- `tyToRepr ty`.
tyToShapeEq :: M.Collection -> M.Ty -> TypeRepr tp -> TypeShape tp
tyToShapeEq col ty tpr | Some shp <- tyToShape col ty =
    case testEquality (shapeType shp) tpr of
        Just Refl -> shp
        Nothing -> error $ "tyToShapeEq: type " ++ show ty ++
            " does not have representation " ++ show tpr ++
            " (got " ++ show (shapeType shp) ++ " instead)"

shapeType :: TypeShape tp -> TypeRepr tp
shapeType shp = go shp
  where
    go :: forall tp. TypeShape tp -> TypeRepr tp
    go (UnitShape _) = UnitRepr
    go (PrimShape _ btpr) = baseToType btpr
    go (TupleShape _ _ flds) = StructRepr $ fmapFC fieldShapeType flds
    go (ArrayShape _ _ shp) = MirVectorRepr $ shapeType shp
    go (StructShape _ _ flds) = AnyRepr
    go (RefShape _ tpr) = MirReferenceRepr tpr

fieldShapeType :: FieldShape tp -> TypeRepr tp
fieldShapeType (ReqField shp) = shapeType shp
fieldShapeType (OptField shp) = MaybeRepr $ shapeType shp

shapeMirTy :: TypeShape tp -> M.Ty
shapeMirTy (UnitShape ty) = ty
shapeMirTy (PrimShape ty _) = ty
shapeMirTy (TupleShape ty _ _) = ty
shapeMirTy (ArrayShape ty _ _) = ty
shapeMirTy (StructShape ty _ _) = ty
shapeMirTy (RefShape ty _) = ty

fieldShapeMirTy :: FieldShape tp -> M.Ty
fieldShapeMirTy (ReqField shp) = shapeMirTy shp
fieldShapeMirTy (OptField shp) = shapeMirTy shp


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
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasCallStack) =>
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
    go (MirVectorRepr tpr') vec = case vec of
        MirVector_Vector v -> mapM_ (go tpr') v
        MirVector_PartialVector pv -> mapM_ (go (MaybeRepr tpr')) pv
        MirVector_Array _ -> error $ "visitRegValueExprs: unsupported: MirVector_Array"
    -- For now, we require that all references within a MethodSpec be
    -- nonoverlapping, and ignore the `SymExpr`s inside.  If we ever want to
    -- write a spec for e.g. `f(arr, &arr[i], i)`, where the second reference
    -- is offset from the first by a symbolic integer value, then we'd need to
    -- visit exprs from some suffix of each MirReference.
    go (MirReferenceRepr _) _ = return ()
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
