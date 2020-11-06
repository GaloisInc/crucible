{-# Language GADTs #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}
{-# Language DataKinds #-}
{-# Language TypeApplications #-}

module Mir.ExtractSpec where

import Control.Lens ((^.), (^?), (%=), (.=), use, at, ix, _Wrapped)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import Data.Functor.Const
import Data.IORef
import Data.Parameterized.Context (Ctx(..), pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
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
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Types

import qualified Lang.Crucible.Backend.SAWCore as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Term.Pretty as SAW

import qualified SAWScript.Crucible.Common.MethodSpec as MS

import Crux.Types (Model)

import Mir.DefId
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M
import Mir.TransTy


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
type instance MS.AllocSpec MIR = Void
type instance MS.PointsTo MIR = Void

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
        EmptyCtx MethodSpecBuilderType (MethodSpecBuilderHandle sym)
builderNew cs defId = do
    let tyArg = cs ^? collection . M.intrinsics . ix defId .
            M.intrInst . M.inSubsts . _Wrapped . ix 0
    fnDefId <- case tyArg of
        Just (M.TyFnDef did) -> return did
        _ -> error $ "expected TyFnDef argument, but got " ++ show tyArg
    let sig = case cs ^? collection . M.functions . ix fnDefId . M.fsig of
            Just x -> x
            _ -> error $ "failed to look up sig of " ++ show fnDefId

    let loc = mkProgramLoc (functionNameFromText $ idText defId) InternalPos
    let ms :: MIRMethodSpec = MS.makeCrucibleMethodSpecIR defId
            (sig ^. M.fsarg_tys) (Just $ sig ^. M.fsreturn_ty) loc cs

    Some retTpr <- return $ tyToRepr $ sig ^. M.fsreturn_ty

    let msb = MethodSpecBuilder
            { _msbSpec = ms
            , _msbResultType = retTpr
            , _msbResult = Nothing
            }

    liftIO $ MethodSpecBuilderHandle <$> newIORef msb


builderFinish ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecBuilderType) MethodSpecType MIRMethodSpec
builderFinish = do
    RegMap (Empty :> RegEntry _tpr (MethodSpecBuilderHandle handle)) <- getOverrideArgs
    builder <- liftIO $ readIORef handle
    return $ builder ^. msbSpec


specPrettyPrint ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    OverrideSim (Model sym) sym MIR rtp
        (EmptyCtx ::> MethodSpecType) (MirSlice (BVType 8)) (RegValue sym (MirSlice (BVType 8)))
specPrettyPrint = do
    RegMap (Empty :> RegEntry _tpr ms) <- getOverrideArgs
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
    sym ->
    Monad m =>
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
    forall t tp.
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
