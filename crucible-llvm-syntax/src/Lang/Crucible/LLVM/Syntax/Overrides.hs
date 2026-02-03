{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Syntax.Overrides
  ( registerLLVMOverrides
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable qualified as F
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text qualified as Text

import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.NatRepr qualified as NatRepr
import Data.Parameterized.Some qualified as Some
import Data.Parameterized.TraversableFC qualified as TFC

import Text.LLVM.AST qualified as L

import Lang.Crucible.Backend qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Types qualified as C

import Lang.Crucible.LLVM.Extension qualified as CLLVM
import Lang.Crucible.LLVM.Functions qualified as CLLVM
import Lang.Crucible.LLVM.Intrinsics qualified as CLLVM
import Lang.Crucible.LLVM.MemModel qualified as CLLVM
import Lang.Crucible.LLVM.Translation qualified as CLLVM
import Lang.Crucible.LLVM.TypeContext qualified as CLLVM

import What4.FunctionName (FunctionName)
import What4.FunctionName qualified as WFN

-- | Register overrides for libc functions and LLVM intrinsics
registerLLVMOverrides ::
  ( C.IsSymBackend sym bak
  , CLLVM.HasLLVMAnn sym
  , CLLVM.HasPtrWidth wptr
  , ?lc :: CLLVM.TypeContext
  , ?intrinsicsOpts :: CLLVM.IntrinsicsOptions
  , ?memOpts :: CLLVM.MemOptions
  , ext ~ CLLVM.LLVM
  , CLLVM.ArchWidth arch ~ wptr
  ) =>
  bak ->
  CLLVM.LLVMContext arch ->
  Map FunctionName C.SomeHandle ->
  C.OverrideSim p sym ext rtp a r [CLLVM.SomeLLVMOverride p sym ext]
registerLLVMOverrides bak llvmCtx fwdDecs = do
  let mkHdlDecl (C.SomeHandle hdl) =
        mkDeclare
          (Text.unpack (WFN.functionName (C.handleName hdl)))
          (C.handleArgTypes hdl)
          (C.handleReturnType hdl)
  let mvar = CLLVM.llvmMemVar llvmCtx
  let mDecls = traverse mkHdlDecl (Map.elems fwdDecs)
  decls <-
    case mDecls of
      Left err -> fail (show err)
      Right ok -> pure ok

  F.forM_ decls $ \decl -> do
    let L.Symbol name = L.decName decl
    let aliases = []
    -- See the module comment on "Lang.Crucible.LLVM.Functions" for why this
    -- part is necessary.
    C.modifyGlobal mvar $ \mem ->
      liftIO (CLLVM.registerFunPtr bak mem name (L.decName decl) aliases)

  ovs <- CLLVM.register_llvm_overrides_ llvmCtx CLLVM.declare_overrides decls

  -- Forward all of the `declare`d handles to the actual override
  F.forM_ ovs $ \(CLLVM.SomeLLVMOverride llOv) -> do
    let L.Symbol nm = L.decName (CLLVM.llvmOverride_declare llOv)
    let fnm = WFN.functionNameFromText (Text.pack nm)
    case Map.lookup fnm fwdDecs of
      Nothing -> pure ()
      Just (C.SomeHandle hdl) -> do
        let llArgs = CLLVM.llvmOverride_args llOv
        let llRet = CLLVM.llvmOverride_ret llOv
        let hdlArgs = C.handleArgTypes hdl
        let hdlRet = C.handleReturnType hdl
        o <- CLLVM.build_llvm_override fnm llArgs llRet hdlArgs hdlRet
               (\asgn -> CLLVM.llvmOverride_def llOv mvar asgn)
        C.registerFnBinding (C.FnBinding hdl (C.UseOverride o))

  pure ovs


-- | Lift a Crucible type to an LLVM type.
--
-- This function has several missing cases that can be filled in as necessary.
llvmType :: CLLVM.HasPtrWidth w => C.TypeRepr t -> Maybe L.Type
llvmType =
  \case
    C.AnyRepr{} -> Nothing
    C.BoolRepr -> Just (L.PrimType (L.Integer 1))
    C.CharRepr{} -> Nothing
    C.BVRepr w -> Just (intType w)
    C.ComplexRealRepr{} -> Nothing
    C.FloatRepr C.HalfFloatRepr -> Just (L.PrimType (L.FloatType L.Half))
    -- XXX not yet: BrainFloatRepr needs to be added in what4
    --C.FloatRepr C.BrainFloatRepr -> Just (L.PrimType (L.FloatType L.BFloat))
    C.FloatRepr C.SingleFloatRepr -> Just (L.PrimType (L.FloatType L.Float))
    C.FloatRepr C.DoubleFloatRepr -> Just (L.PrimType (L.FloatType L.Double))
    C.FloatRepr C.X86_80FloatRepr -> Just (L.PrimType (L.FloatType L.X86_fp80))
    C.FloatRepr C.DoubleDoubleFloatRepr -> Just (L.PrimType (L.FloatType L.PPC_fp128))
    C.FloatRepr C.QuadFloatRepr -> Just (L.PrimType (L.FloatType L.Fp128))
    C.FunctionHandleRepr{} -> Nothing
    C.IEEEFloatRepr{} -> Nothing -- TODO?
    C.IntegerRepr{} -> Nothing
    C.MaybeRepr{} -> Nothing
    C.NatRepr{} -> Nothing
    C.RealValRepr{} -> Nothing
    C.RecursiveRepr{} -> Nothing
    C.ReferenceRepr{} -> Nothing
    C.SequenceRepr{} -> Nothing
    C.StringRepr{} -> Nothing
    C.StringMapRepr{} -> Nothing
    C.StructRepr fieldAssn -> do
      fieldTys <-
        traverse (Some.viewSome llvmType) $
          TFC.toListFC Some.Some fieldAssn
      Just $ L.Struct fieldTys
    C.SymbolicArrayRepr{} -> Nothing
    C.SymbolicStructRepr{} -> Nothing
    C.UnitRepr -> Just (L.PrimType L.Void)
    C.VariantRepr{} -> Nothing
    -- HACK: It's not clear how to support other vector sizes, because Crucible
    -- vectors don't have the length as part of the type. We arbitrarily choose
    -- 4 here so that we can write tests for vectorized intrinsics of width 4
    -- in crucible-llvm-cli.
    C.VectorRepr t -> L.Vector 4 <$> llvmType t
    C.WordMapRepr{} -> Nothing
    CLLVM.LLVMPointerRepr w ->
      case C.testEquality w ?ptrWidth of
        Just C.Refl -> Just L.PtrOpaque
        Nothing -> Just (intType w)
    C.IntrinsicRepr{} -> Nothing
 where
  intType :: NatRepr.NatRepr n -> L.Type
  intType w = L.PrimType (L.Integer (fromIntegral (NatRepr.natValue w)))

-- | Create an LLVM declaration from Crucible types.
--
-- See https://github.com/GaloisInc/crucible/issues/1138 for progress on
-- obviating this code.
mkDeclare ::
  CLLVM.HasPtrWidth w =>
  String ->
  Ctx.Assignment C.TypeRepr args ->
  C.TypeRepr ret ->
  Either String L.Declare
mkDeclare name args ret = do
  let getType :: forall t. C.TypeRepr t -> Either String L.Type
      getType t =
        case llvmType t of
          Nothing -> Left ("Can't make LLVM type from Crucible type " ++ show t)
          Just llTy -> Right llTy
  llvmArgs <- sequence (TFC.toListFC getType args)
  llvmRet <- getType ret
  pure $
    L.Declare
      { L.decArgs = llvmArgs
      , L.decAttrs = []
      , L.decComdat = Nothing
      , L.decLinkage = Nothing
      , L.decName = L.Symbol name
      , L.decRetType = llvmRet
      , L.decVarArgs = False
      , L.decVisibility = Nothing
      }
