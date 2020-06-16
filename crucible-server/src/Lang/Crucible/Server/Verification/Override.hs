{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.Verification.Override
-- Copyright        : (c) Galois, Inc 2017
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Support for using verification harnesses at call sites in "override"
-- mode.
------------------------------------------------------------------------

module Lang.Crucible.Server.Verification.Override
  ( -- * High-level interface to harness overrides
    VerifState
  , verifStateRepr
  , VerificationOverrideFnHandle
  , verifFnRepr
  , verificationHarnessOverrideHandle

    -- * Low-level interface
  , N
  , SAWBack
  , Subst
  , SubstTerm(..)
  , termToSubstTerm
  , computeVarTypes
  , assertEquiv
  , assumeEquiv
  , computeVariableSubstitution
  , phaseUpdate
  , assumeConditions
  , assertConditions
  , simulateHarness
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Lens (folded)
import           Control.Monad
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Data.Word

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some

import qualified Cryptol.TypeCheck.AST as CT
import qualified Cryptol.Utils.PP as PP

import           What4.Interface
import           What4.Expr.Builder (Flags, FloatReal)
import           What4.FunctionName
import           What4.Partial
import qualified What4.Solver.Yices as Yices
import           What4.WordMap

import           Lang.Crucible.Backend
import qualified Lang.Crucible.Backend.SAWCore as SAW
import           Lang.Crucible.Types
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.SimError

import qualified Verifier.SAW.Simulator.SBV as SBV (sbvSolveBasic, toWord)
import qualified Data.SBV.Dynamic as SBV (svAsInteger)

import           Verifier.SAW.Conversion
import           Verifier.SAW.Rewriter
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedAST

import           Lang.Crucible.Server.CryptolEnv
import           Lang.Crucible.Server.MultipartOperations
import           Lang.Crucible.Server.Simulator
--import           Lang.Crucible.Server.TypedTerm
import           Lang.Crucible.Server.Verification.Harness


type VerifState rw w =
  EmptyCtx ::>
  BVType w ::>                      -- PC
  WordMapType rw (BaseBVType 8) ::> -- Register file
  WordMapType w  (BaseBVType 8)     -- Memory


type VerificationOverrideFnHandle rw w =
   FnHandle (VerifState rw w) (StructType (VerifState rw w))

verifStateRepr :: (1 <= w, 1 <= rw) => NatRepr rw -> NatRepr w -> CtxRepr (VerifState rw w)
verifStateRepr rw w = Ctx.empty Ctx.:> BVRepr w Ctx.:> WordMapRepr rw knownRepr Ctx.:> WordMapRepr w knownRepr

verifFnRepr :: (1 <= w, 1 <= rw) =>
   NatRepr rw ->
   NatRepr w ->
   TypeRepr (FunctionHandleType (VerifState rw w) (StructType (VerifState rw w)))
verifFnRepr rw w = FunctionHandleRepr (verifStateRepr rw w) (StructRepr (verifStateRepr rw w))

-- | Given a processed harness, compute a verification override, bind it to
--   a fresh function handle, and return that handle.  The address bus width
--   and register file width are fixed by the given NatReprs.
verificationHarnessOverrideHandle ::
  (1 <= w, 1 <= rw) =>
  Simulator p (SAWBack n) ->
  NatRepr rw ->
  NatRepr w ->
  CryptolEnv ->
  ProcessedHarness ->
  IO (VerificationOverrideFnHandle rw w)
verificationHarnessOverrideHandle sim rw w cryEnv harness =
  do sc <- SAW.sawBackendSharedContext =<< getInterface sim
     let nm = functionNameFromText (verificationOverrideName harness)
     simOverrideHandle sim (verifStateRepr rw w) (StructRepr (verifStateRepr rw w))
           (mkOverride' nm (StructRepr (verifStateRepr rw w))
              (verificationHarnessOverride sim rw w sc cryEnv harness))

type SAWBack n = SAW.SAWCoreBackend n (Yices.Connection n) (Flags FloatReal)
type N p n r args ret a = OverrideSim p (SAWBack n) () r args ret a

----------------------------------------------------------------------

data OverrideFailure where
  InvalidReturnType :: String -> TypeRepr want -> TypeRepr got -> OverrideFailure
  InvalidArgumentTypes :: String -> CtxRepr args1 -> CtxRepr args2 -> OverrideFailure
  BadWidth :: String -> Word64 -> OverrideFailure
  NegativeWidth :: String -> Word64 -> OverrideFailure
  WidthNotModulo8 :: String -> Word64 -> OverrideFailure

deriving instance Show OverrideFailure
instance X.Exception OverrideFailure

----------------------------------------------------------------------

-- | Define the behavior of a verification override.  First, bind the values of all the
--   verification harness variables from the prestate.
verificationHarnessOverride ::
   (1 <= w, 1 <= rw) =>
   Simulator p (SAWBack n) ->
   NatRepr rw ->
   NatRepr w ->
   SharedContext ->
   CryptolEnv ->
   ProcessedHarness ->
   N p n r (VerifState rw w) ret (RegValue (SAWBack n) (StructType (VerifState rw w)))
verificationHarnessOverride sim rw w sc cryEnv harness =
   do args <- getOverrideArgs
      case args of
        RegMap (Ctx.Empty Ctx.:> (regValue -> _pc) Ctx.:> (regValue -> regs) Ctx.:> (regValue -> mem)) ->
          do let prestateVarTypes = computeVarTypes Prestate harness
             let poststateVarTypes = computeVarTypes Poststate harness `Map.union` prestateVarTypes
             let endianness = verificationEndianness harness
             let sub0 = Map.empty
             sym <- getSymInterface

             (sub,cryEnv') <- computeVariableSubstitution sim sym rw w sc endianness cryEnv
                                       prestateVarTypes (verificationPrestate harness) regs mem sub0
             assertConditions sc cryEnv' (verificationPrestate harness)

             (_sub'',cryEnv'',regs',mem') <- phaseUpdate sim sym rw w sc poststateVarTypes endianness
                                                (verificationPoststate harness) (sub,cryEnv',regs,mem)
             assumeConditions sc cryEnv'' (verificationPoststate harness)

             pc' <- lookupWord sym w ReturnAddressVar sub
             return (Ctx.Empty Ctx.:> RV pc' Ctx.:> RV regs' Ctx.:> RV mem')

       -- _ -> fail "Impossible! failed to deconstruct verification override arguments"

assertConditions ::
   SharedContext ->
   CryptolEnv ->
   VerificationPhase CT.Name TCExpr ->
   N p n r args ret ()
assertConditions sc cryEnv phase =
   do sym <- getSymInterface
      forM_ (toList (phaseConds phase)) $ \(tp, ex) -> liftIO $
        do unless (CT.tIsBit tp) $ fail "Verification harness precondition does not have type 'Bit'"
           tm <- translateExpr sc cryEnv ex
           x  <- SAW.bindSAWTerm sym BaseBoolRepr tm
           assert sym x (AssertFailureSimError "Verification override precondition" "")


assumeConditions ::
   SharedContext ->
   CryptolEnv ->
   VerificationPhase CT.Name TCExpr ->
   N p n r args ret ()
assumeConditions sc cryEnv phase =
   do sym <- getSymInterface
      forM_ (toList (phaseConds phase)) $ \(tp, ex) -> liftIO $
        do unless (CT.tIsBit tp) $ fail "Verification harness postcondition does not have type 'Bit'"
           tm <- translateExpr sc cryEnv ex
           x  <- SAW.bindSAWTerm sym BaseBoolRepr tm
           loc <- getCurrentProgramLoc sym
           addAssumption sym (LabeledPred x (AssumptionReason loc "Verification postcondition"))

createFreshHarnessVar ::
  SAWBack n ->
  HarnessVar CT.Name ->
  HarnessVarType ->
  IO (SubstTerm (SAWBack n), Term)
createFreshHarnessVar sym var (HarnessVarWord n) =
  do Just (Some valSize) <- return (someNat (toInteger n))
     Just LeqProof <- return (isPosNat valSize)
     sc <- SAW.sawBackendSharedContext sym
     sawtp <- scBitvector sc (fromIntegral n)
     let nm = show (PP.pp var)
     tm <- SAW.sawCreateVar sym nm sawtp
     bv <- SAW.bindSAWTerm sym (BaseBVRepr valSize) tm
     return (SubstWord bv, tm)

createFreshHarnessVar sym var (HarnessVarArray elems n) =
  do Just (Some valSize) <- return (someNat (toInteger n))
     Just LeqProof <- return (isPosNat valSize)
     sc <- SAW.sawBackendSharedContext sym
     elemtp <- scBitvector sc (fromIntegral n)
     elems' <- scNat sc (fromIntegral elems)
     sawtp  <- scVecType sc elems' elemtp
     let nm = show (PP.pp var)
     tm <- SAW.sawCreateVar sym nm sawtp
     tms <- forM [0..elems-1] $ \i ->
               do i' <- scNat sc (fromIntegral i)
                  scAt sc elems' elemtp tm i'
     bvs <- mapM (SAW.bindSAWTerm sym (BaseBVRepr valSize)) tms
     return (SubstArray valSize (Seq.fromList bvs), tm)

withValidSize :: X.MonadThrow m =>
                 String -> Word64
              -> (forall x. 1 <= x => NatRepr x -> m a) -> m a
withValidSize nm sz f =
  case someNat (toInteger sz) of
    Nothing -> X.throwM $ BadWidth nm sz
    Just (Some w) ->
      case isPosNat w of
        Nothing -> X.throwM $ NegativeWidth nm sz
        Just LeqProof ->
          f w

phaseUpdate :: forall p n r args ret w rw.
   (1 <= w, 1 <= rw) =>
   Simulator p (SAWBack n) ->
   SAWBack n ->
   NatRepr rw ->
   NatRepr w ->
   SharedContext ->
   Map (HarnessVar CT.Name) HarnessVarType ->
   Endianness ->
   VerificationPhase CT.Name TCExpr ->
   ( Subst (SAWBack n)
   , CryptolEnv
   , WordMap (SAWBack n) rw (BaseBVType 8)
   , WordMap (SAWBack n) w (BaseBVType 8)
   ) ->
   N p n r args ret
     ( Subst (SAWBack n)
     , CryptolEnv
     , WordMap (SAWBack n) rw (BaseBVType 8)
     , WordMap (SAWBack n) w (BaseBVType 8)
     )
phaseUpdate sim sym rw w sc varTypes endianness phase = \x -> foldM go x (toList (phaseSetup phase))
 where

  updateSub var tm x sub cryEnv regs mem =
      do let cryEnv' = case var of
                          CryptolVar nm ->
                             cryEnv{ eTermEnv = Map.insert nm tm (eTermEnv cryEnv) }
                          _ -> cryEnv
         let sub' = Map.insert var x sub
         return (sub', cryEnv', regs, mem)

  go (sub,cryEnv,regs,mem) step = case step of
    DeclareFreshVariable var ->
      let hvar = CryptolVar var in
      case Map.lookup hvar sub of
        Just _ ->
          -- If the variable already has a definition, just discard this directive
          do return (sub,cryEnv,regs,mem)
        Nothing ->
          case Map.lookup hvar varTypes of
            Just htp ->
              do (subTm,tm) <- liftIO $ createFreshHarnessVar sym hvar htp
                 updateSub hvar tm subTm sub cryEnv regs mem
            Nothing ->
              fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

    BindVariable var (_tp,ex) ->
      case Map.lookup var varTypes of
        Just htp ->
          do tm <- liftIO $ translateExpr sc cryEnv ex
             x <- termToSubstTerm sym sc htp tm
             case Map.lookup var sub of
               Nothing ->
                 do updateSub var tm x sub cryEnv regs mem
               Just tm' ->
                 do assumeEquiv sym htp tm tm'
                    return (sub, cryEnv, regs, mem)
        Nothing ->
          fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

    RegisterVal offset var ->
      case Map.lookup var varTypes of
        Just (HarnessVarWord n) ->
          withValidSize (show $ PP.pp var) n $ \valSize -> do
             case Map.lookup var sub of
               Just substTm ->
                 do bv <- substTermAsBV sym valSize substTm
                    regs' <- writeReg sim rw offset n endianness (SomeBV bv) regs
                    return (sub,cryEnv,regs',mem)
               Nothing ->
                 do (substTm, tm) <- liftIO $ createFreshHarnessVar sym var (HarnessVarWord n)
                    bv <- substTermAsBV sym valSize substTm
                    regs' <- writeReg sim rw offset n endianness (SomeBV bv) regs
                    updateSub var tm substTm sub cryEnv regs' mem

        Just (HarnessVarArray _ _ ) ->
           fail (show (PP.text "Cannot write array types to registers for variable: " PP.<+> PP.pp var))
        Nothing ->
           fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

    MemPointsTo base offset val ->
      case Map.lookup base sub of
        Just basetm ->
          case Map.lookup val varTypes of
            Just (HarnessVarWord n) ->
              do baseAddr <- substTermAsBV sym w basetm
                 off <- liftIO $ bvLit sym w (BV.trunc' w (BV.word64 offset))
                 addr <- liftIO (bvAdd sym baseAddr off)
                 withValidSize ("MemPointsTo word " <> (show $ PP.pp val)) n $ \x ->
                  case Map.lookup val sub of
                   Just valtm ->
                     do bv <- substTermAsBV sym x valtm
                        mem' <- writeMap sim w addr n endianness (SomeBV bv) mem
                        return (sub,cryEnv,regs,mem')
                   Nothing ->
                     do (valtm, tm) <- liftIO $ createFreshHarnessVar sym val (HarnessVarWord n)
                        bv <- substTermAsBV sym x valtm
                        mem' <- writeMap sim w addr n endianness (SomeBV bv) mem
                        updateSub val tm valtm sub cryEnv regs mem'

            Just (HarnessVarArray elems n) ->
              do baseAddr <- substTermAsBV sym w basetm
                 off <- liftIO $ bvLit sym w (BV.trunc' w (BV.word64 offset))
                 addr <- liftIO (bvAdd sym baseAddr off)
                 withValidSize ("MemPointsTo array " <> (show $ PP.pp val)) n $ \x ->
                  case Map.lookup val sub of
                   Just valtm ->
                     do mem' <- writeArray sim sym w addr endianness elems n x valtm mem
                        return (sub,cryEnv,regs,mem')
                   Nothing ->
                     do (valtm, tm) <- liftIO $ createFreshHarnessVar sym val (HarnessVarArray elems n)
                        mem' <- writeArray sim sym w addr endianness elems n x valtm mem
                        updateSub val tm valtm sub cryEnv regs mem'

            Nothing ->
              fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp val))
        Nothing ->
          fail (show (PP.text "Base pointer not defined" PP.<+> PP.pp base))

substTermAsArray ::
   (MonadIO m, MonadFail m, 1 <= x) =>
   SAWBack n ->
   Word64 ->
   NatRepr x ->
   SubstTerm (SAWBack n) ->
   m (Seq (SymBV (SAWBack n) x))
substTermAsArray _sym elems x (SubstArray x' vs)
  | Just Refl <- testEquality x x'
  , Seq.length vs == fromIntegral elems
  = return vs

substTermAsArray sym elems x (SubstTerm tm)
  = liftIO $
      do sc <- SAW.sawBackendSharedContext sym
         elemtp <- scBitvector sc (fromIntegral (natValue x))
         elems' <- scNat sc (fromIntegral elems)
         tms <- forM [0..elems-1] $ \i ->
                   do i' <- scNat sc (fromIntegral i)
                      v <- scAt sc elems' elemtp tm i'
                      SAW.bindSAWTerm sym (BaseBVRepr x) v
         return (Seq.fromList tms)

substTermAsArray _sym _elems _x _
  = fail "Expected array value"

readArray ::
   (1 <= w, 1 <= x) =>
   Simulator p (SAWBack n) ->
   SAWBack n ->
   NatRepr w ->
   SymBV (SAWBack n) w ->
   Endianness ->
   Word64 ->
   Word64 ->
   NatRepr x ->
   WordMap (SAWBack n) w (BaseBVType 8) ->
   N p n r args ret (Seq (SymBV (SAWBack n) x))
readArray sim sym w addr endianness elems n x mem =
  Seq.fromList <$> (forM [ 0 .. elems-1 ] $ \i ->
    do off   <- liftIO $ bvLit sym w (BV.trunc' w (BV.word64 (i * (n `div` 8))))
       addr' <- liftIO $ bvAdd sym addr off
       SomeBV v <- readMap sim w addr' n endianness mem
       case testEquality (bvWidth v) x of
         Just Refl -> return v
         Nothing   -> fail "Size mismatch in readArray")


writeArray ::
   (1 <= w, 1 <= x) =>
   Simulator p (SAWBack n) ->
   SAWBack n ->
   NatRepr w ->
   SymBV (SAWBack n) w ->
   Endianness ->
   Word64 ->
   Word64 ->
   NatRepr x ->
   SubstTerm (SAWBack n) ->
   WordMap (SAWBack n) w (BaseBVType 8) ->
   N p n r args ret (WordMap (SAWBack n) w (BaseBVType 8))
writeArray sim sym w addr endianness elems n x val mem0 =
   do vals <- substTermAsArray sym elems x val
      foldM
        (\mem (i,v) ->
          do off <- liftIO $ bvLit sym w (BV.trunc' w (BV.word64 (i * (n `div` 8))))
             addr' <- liftIO $ bvAdd sym addr off
             liftIO (sendTextResponse sim (T.pack ("WriteArray: " ++ show (printSymExpr addr'))))
             writeMap sim w addr' n endianness (SomeBV v) mem
        )
        mem0
        (zip [ 0 .. (elems-1) ] (toList vals))



lookupWord ::
   (1 <= w) =>
   SAWBack n ->
   NatRepr w ->
   HarnessVar CT.Name ->
   Subst (SAWBack n) ->
   N p n r args ret (SymBV (SAWBack n) w)
lookupWord sym w var sub =
  case Map.lookup var sub of
    Just subtm -> substTermAsBV sym w subtm
    Nothing -> fail (show (PP.text "Undefined variable" PP.<+> PP.pp var))

computeVarTypes ::
   Phase ->
   ProcessedHarness ->
   Map (HarnessVar CT.Name) HarnessVarType
computeVarTypes ph harness = Map.fromList pairs

  where
  pairs = (ReturnAddressVar, addrType) : (StackPointerVar, addrType) : map f (toList decls)
  addrType = HarnessVarWord (verificationAddressWidth harness)
  f x = (CryptolVar (harnessVarIdent x), harnessVarType x)
  decls = phaseVars phase
  phase = case ph of
            Prestate  -> verificationPrestate harness
            Poststate -> verificationPoststate harness


type Subst sym = Map (HarnessVar CT.Name) (SubstTerm sym)

data SubstTerm sym where
  SubstTerm  :: Term -> SubstTerm sym
  SubstWord  :: (1 <= w) => SymExpr sym (BaseBVType w) -> SubstTerm sym
  SubstArray :: (1 <= w) => NatRepr w -> Seq (SymExpr sym (BaseBVType w)) -> SubstTerm sym

computeVariableSubstitution :: forall p n r args ret w rw.
   (1 <= rw, 1 <= w) =>
   Simulator p (SAWBack n) ->
   SAWBack n ->
   NatRepr rw ->
   NatRepr w ->
   SharedContext ->
   Endianness ->
   CryptolEnv ->
   Map (HarnessVar CT.Name) HarnessVarType ->
   VerificationPhase CT.Name TCExpr ->
   WordMap (SAWBack n) rw (BaseBVType 8) ->
   WordMap (SAWBack n) w (BaseBVType 8) ->
   Subst (SAWBack n) ->
   N p n r args ret (Subst (SAWBack n), CryptolEnv)
computeVariableSubstitution sim sym rw w sc endianness cryEnv0 varTypes phase regs mem sub0 =
    foldM go (sub0, cryEnv0) (toList (phaseSetup phase))

  where
  updateSub var tm x sub cryEnv =
      do let cryEnv' = case var of
                          CryptolVar nm ->
                             cryEnv{ eTermEnv = Map.insert nm tm (eTermEnv cryEnv) }
                          _ -> cryEnv
         let sub' = Map.insert var x sub
         return (sub', cryEnv')

  go (sub, cryEnv) step = case step of
    DeclareFreshVariable var ->
      let hvar = CryptolVar var in
      case Map.lookup hvar sub of
         Just _ -> return (sub,cryEnv)
         Nothing ->
           case Map.lookup hvar varTypes of
             Just htp ->
               do (subTm, tm) <- liftIO $ createFreshHarnessVar sym hvar htp
                  updateSub hvar tm subTm sub cryEnv
             Nothing ->
               fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

    BindVariable var (_tp,ex) ->
      case Map.lookup var varTypes of
        Just htp ->
          do tm <- liftIO $ translateExpr sc cryEnv ex
             x <- termToSubstTerm sym sc htp tm
             case Map.lookup var sub of
               Nothing ->
                 do updateSub var tm x sub cryEnv
               Just tm' ->
                 do assertEquiv sym htp tm tm'
                    return (sub, cryEnv)
        Nothing ->
          fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

    RegisterVal off var ->
      case Map.lookup var varTypes of
        Just (HarnessVarWord n) ->
          do SomeBV x <- readReg sim rw off n endianness regs
             tm <- liftIO $ SAW.toSC sym x
             case Map.lookup var sub of
               Nothing ->
                 do updateSub var tm (SubstWord x) sub cryEnv
               Just tm' ->
                 do assertEquiv sym (HarnessVarWord n) tm tm'
                    return (sub,cryEnv)

        Just (HarnessVarArray _ _ ) ->
           fail (show (PP.text "Cannot read array types from registers for variable: " PP.<+> PP.pp var))
        Nothing ->
           fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

    MemPointsTo base offset var ->
      case Map.lookup var varTypes of
        Just (HarnessVarWord n) ->
          do -- FIXME check that base is actually a address pointer
             case Map.lookup base sub of
               Just basetm ->
                    do baseAddr <- substTermAsBV sym w basetm
                       off <- liftIO $ bvLit sym w (BV.trunc' w (BV.word64 offset))
                       addr <- liftIO (bvAdd sym baseAddr off)
                       SomeBV x <- readMap sim w addr n endianness mem
                       tm <- liftIO $ SAW.toSC sym x
                       case Map.lookup var sub of
                         Nothing ->
                           do updateSub var tm (SubstWord x) sub cryEnv
                         Just tm' ->
                           do assertEquiv sym (HarnessVarWord n) tm tm'
                              return (sub,cryEnv)

               Nothing ->
                 fail (show (PP.text "Base pointer not defined"
                             PP.<+> PP.pp base))

        Just (HarnessVarArray elems n) ->
             case Map.lookup base sub of
               Just basetm ->
                    do baseAddr <- substTermAsBV sym w basetm
                       off <- liftIO $ bvLit sym w (BV.trunc' w (BV.word64 offset))
                       addr <- liftIO (bvAdd sym baseAddr off)
                       withValidSize ("MemPointsTo array.2 " <> (show $ PP.pp base)) n $ \valSize -> do
                         vals <- readArray sim sym w addr endianness elems n valSize mem
                         tm   <- liftIO $ arrayAsTerm sym n vals
                         case Map.lookup var sub of
                           Nothing ->
                             updateSub var tm (SubstArray valSize vals) sub cryEnv
                           Just tm' ->
                             do assertEquiv sym (HarnessVarArray elems n) tm tm'
                                return (sub,cryEnv)

               Nothing ->
                 fail (show (PP.text "Base pointer not defined"
                             PP.<+> PP.pp base))

        Nothing ->
           fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

arrayAsTerm ::
   SAWBack n ->
   Word64 ->
   Seq (SymBV (SAWBack n) x) ->
   IO Term
arrayAsTerm sym n vals =
  do sc <- SAW.sawBackendSharedContext sym
     elemtp <- scBitvector sc (fromIntegral n)
     scVector sc elemtp =<< mapM (SAW.toSC sym) (toList vals)

termToSubstTerm ::
   SAWBack n ->
   SharedContext ->
   HarnessVarType ->
   Term ->
   N p n r args ret (SubstTerm (SAWBack n))
termToSubstTerm sym sc (HarnessVarWord n) tm =
  do x <- liftIO $ termAsConcrete sc tm
     case x of
       Just i  -> withValidSize "substTerm" n $ \w -> do
                     bv <- liftIO $ bvLit sym w (BV.mkBV w i)
                     return (SubstWord bv)
       Nothing -> return (SubstTerm tm)

-- FIXME? try to extract concrete values?
termToSubstTerm _ _ (HarnessVarArray _ _) tm = return (SubstTerm tm)


substTermAsBV ::
   (1 <= x, MonadIO m, MonadFail m) =>
   SAWBack n ->
   NatRepr x ->
   SubstTerm (SAWBack n) ->
   m (SymBV (SAWBack n) x)
substTermAsBV sym w (SubstTerm tm) =
   do liftIO $ SAW.bindSAWTerm sym (BaseBVRepr w) tm
substTermAsBV _sym w (SubstWord x) =
    case testEquality w (bvWidth x) of
      Just Refl -> return x
      Nothing -> fail ("BV width mismatch " ++ show (w,bvWidth x))
substTermAsBV _sym _w (SubstArray _ _) =
   fail "Expected a bitvector term, but got an array"

-- Try to render the given SAWCore term, assumed to represent
-- a bitvector, as a concrete value.
termAsConcrete ::
   SharedContext ->
   Term ->
   IO (Maybe Integer)
termAsConcrete sc tm =
   do ss <- basic_ss sc
      tm' <- rewriteSharedTerm sc ss tm
      mmap <- scGetModuleMap sc
      case getAllExts tm' of
               [] -> do sbv <- SBV.toWord =<< SBV.sbvSolveBasic mmap Map.empty [] tm'
                        return (SBV.svAsInteger sbv)
               _ -> return Nothing

defRewrites :: SharedContext -> Ident -> IO [RewriteRule]
defRewrites sc ident =
   do mdef <- scFindDef sc ident
      case mdef of
        Nothing -> return []
        Just def -> scDefRewriteRules sc def

basic_ss :: SharedContext -> IO Simpset
basic_ss sc = do
  rs1 <- concat <$> traverse (defRewrites sc) (defs ++ defs')
  rs2 <- scEqsRewriteRules sc eqs
  return $ addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
  where
    eqs = map (mkIdent preludeName)
      [ "not_not", "bvAddZeroL", "bvAddZeroR", "ite_eq"
      , "and_True1", "and_True2", "and_False1", "and_False2", "and_idem"
      , "or_triv1", "and_triv1", "or_triv2", "and_triv2"
      ]
    defs = map (mkIdent preludeName)
      [ "not", "and", "or", "xor", "boolEq", "ite", "addNat", "mulNat"
      , "compareNat", "equalNat"
      , "bitvector"
      ]
    defs' = map (mkIdent (mkModuleName ["Cryptol"]))
            ["seq", "ecEq", "ecNotEq"]
    procs = [tupleConversion, recordConversion] ++
            bvConversions ++ natConversions ++ vecConversions


readReg ::
   (1 <= rw) =>
   Simulator p (SAWBack n) ->
   NatRepr rw ->
   Offset ->
   Word64 ->
   Endianness ->
   WordMap (SAWBack n) rw (BaseBVType 8) ->
   N p n r args ret (SomeBV (SAWBack n))
readReg sim rw offset size endianness regs =
   do sym <- getSymInterface
      addr <- liftIO $ bvLit sym rw (BV.trunc' rw (BV.word64 offset))
      readMap sim rw addr size endianness regs

writeReg ::
   (1 <= rw) =>
   Simulator p (SAWBack n) ->
   NatRepr rw ->
   Offset ->
   Word64 ->
   Endianness ->
   SomeBV (SAWBack n) ->
   WordMap (SAWBack n) rw (BaseBVType 8) ->
   N p n r args ret (WordMap (SAWBack n) rw (BaseBVType 8))
writeReg sim rw offset size endianness val regs =
  do sym <- getSymInterface
     addr <- liftIO $ bvLit sym rw (BV.trunc' rw (BV.word64 offset))
     writeMap sim rw addr size endianness val regs

writeMap ::
   (1 <= x) =>
   Simulator p (SAWBack n) ->
   NatRepr x ->
   SymBV (SAWBack n) x ->
   Word64 ->
   Endianness ->
   SomeBV (SAWBack n) ->
   WordMap (SAWBack n) x (BaseBVType 8) ->
   N p n r args ret (WordMap (SAWBack n) x (BaseBVType 8))
writeMap sim x addr size endianness (SomeBV val) wordmap
   | r == 0
   , Just (Some valWidth) <- (someNat (toInteger size))
   , cond1 <- testEquality valWidth (bvWidth val)
   , Just Refl <- cond1
   , Just LeqProof <- (isPosNat valWidth)
   =   do sym <- getSymInterface
          SomeHandle h <- liftIO $
             getPredefinedHandle sim (MultiPartStoreHandle (fromIntegral (natValue x)) 8 (fromIntegral bytes)) $
                SomeHandle <$> multipartStoreFn sim x (knownRepr :: NatRepr 8) valWidth (fromIntegral bytes)
          let argsTy = (Ctx.Empty Ctx.:>
                        BoolRepr Ctx.:>
                        BVRepr x Ctx.:>
                        BVRepr valWidth Ctx.:> retTy)
              retTy = WordMapRepr x (BaseBVRepr (knownRepr :: NatRepr 8))
          case testEquality (handleArgTypes h) argsTy of
            Just Refl ->
              case testEquality (handleReturnType h) retTy of
                Just Refl -> do
                  let endianBool = case endianness of
                                     BigEndian -> truePred sym
                                     LittleEndian -> falsePred sym
                  let args = Ctx.Empty Ctx.:> RegEntry knownRepr endianBool
                             Ctx.:> RegEntry (BVRepr x) addr
                             Ctx.:> RegEntry (BVRepr valWidth) val
                             Ctx.:> RegEntry (WordMapRepr x (BaseBVRepr knownRepr)) wordmap
                  regValue <$> callFnVal (HandleFnVal h) (RegMap args)
                Nothing -> X.throwM $ InvalidReturnType opstr retTy (handleReturnType h)
            Nothing -> X.throwM $ InvalidArgumentTypes opstr argsTy (handleArgTypes h)
   | otherwise = fail ("Invalid arguments to writeMap")
  where
   (bytes,r) = divMod size 8
   opstr = "writeMap " <> show size <> "@" <> show addr


readMap ::
   (1 <= x) =>
   Simulator p (SAWBack n) ->
   NatRepr x ->
   SymBV (SAWBack n) x ->
   Word64 ->
   Endianness ->
   WordMap (SAWBack n) x (BaseBVType 8) ->
   N p n r args ret (SomeBV (SAWBack n))
readMap sim x addr size endianness wordmap
   | r == 0 =
     case someNat (toInteger size) of
       Nothing -> X.throwM $ BadWidth opstr size
       Just (Some valWidth) -> do
         case isPosNat valWidth of
           Nothing -> X.throwM $ NegativeWidth opstr size
           Just LeqProof -> do
             SomeHandle h <-
               liftIO $ getPredefinedHandle sim
                        (MultiPartLoadHandle (fromIntegral (natValue x))
                         8 (fromIntegral bytes)) $
                        SomeHandle <$> (multipartLoadFn sim x
                                        (knownRepr :: NatRepr 8)
                                        valWidth (fromIntegral bytes))
             let argsTy = Ctx.Empty Ctx.:>
                          BoolRepr Ctx.:>
                          BVRepr x Ctx.:>
                          WordMapRepr x (BaseBVRepr (knownRepr :: NatRepr 8)) Ctx.:>
                          MaybeRepr (BVRepr (knownRepr :: NatRepr 8))
                 retTy = BVRepr valWidth
             case testEquality (handleArgTypes h) argsTy of
               Nothing -> X.throwM $ InvalidArgumentTypes opstr argsTy (handleArgTypes h)
               Just Refl ->
                 case testEquality (handleReturnType h) retTy of
                   Nothing -> X.throwM $ InvalidReturnType opstr retTy (handleReturnType h)
                   Just Refl -> do
                     sym <- getSymInterface
                     let endianBool = case endianness of
                                        BigEndian -> truePred sym
                                        LittleEndian -> falsePred sym
                     let args = Ctx.Empty Ctx.:> RegEntry knownRepr endianBool
                                Ctx.:> RegEntry (BVRepr x) addr
                                Ctx.:> RegEntry (WordMapRepr x (BaseBVRepr knownRepr)) wordmap
                                Ctx.:> RegEntry (MaybeRepr (BVRepr knownRepr)) Unassigned
                     SomeBV . regValue <$> callFnVal (HandleFnVal h) (RegMap args)
   | otherwise = X.throwM $ WidthNotModulo8 opstr size
  where
   (bytes,r) = divMod size 8
   opstr = "readMap " <> show size <> "@" <> show addr


data SomeBV sym where
  SomeBV :: forall sym w. (1 <= w) => SymExpr sym (BaseBVType w) -> SomeBV sym


assumeEquiv ::
   (MonadIO m, MonadFail m) =>
   SAWBack n ->
   HarnessVarType ->
   Term ->
   SubstTerm (SAWBack n) ->
   m ()
assumeEquiv sym hvt tm subTm =
     case hvt of
       HarnessVarWord n
         | Just (Some w) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat w
         -> do tm' <- liftIO $ SAW.bindSAWTerm sym (BaseBVRepr w) tm
               subTm' <- substTermAsBV sym w subTm
               eq  <- liftIO $ bvEq sym tm' subTm'
               loc <- liftIO $ getCurrentProgramLoc sym
               liftIO $ addAssumption sym (LabeledPred eq (AssumptionReason loc "Equality condition"))
         | otherwise -> fail ("Invalid word width in assumeEquiv" ++ show n)

       HarnessVarArray elems n
         | Just (Some w) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat w
         -> do vals  <- substTermAsArray sym elems w (SubstTerm tm)
               vals' <- substTermAsArray sym elems w subTm
               eq <- liftIO (andAllOf sym folded =<<
                       zipWithM (\v v' -> bvEq sym v v') (toList vals) (toList vals'))
               loc <- liftIO $ getCurrentProgramLoc sym
               liftIO $ addAssumption sym (LabeledPred eq (AssumptionReason loc "Equality condition"))
         | otherwise -> fail ("Invalid word width in assumeEquiv" ++ show n)

assertEquiv ::
   (MonadIO m, MonadFail m) =>
   SAWBack n ->
   HarnessVarType ->
   Term ->
   SubstTerm (SAWBack n) ->
   m ()
assertEquiv sym hvt tm subTm =
     case hvt of
       HarnessVarWord n
         | Just (Some w) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat w
         -> do tm' <- liftIO $ SAW.bindSAWTerm sym (BaseBVRepr w) tm
               subTm' <- substTermAsBV sym w subTm
               eq  <- liftIO $ bvEq sym tm' subTm'
               liftIO $ assert sym eq (AssertFailureSimError "Equality condition failed" "")
         | otherwise -> fail ("Invalid word width in assertEquiv" ++ show n)

       HarnessVarArray elems n
         | Just (Some w) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat w
         -> do vals  <- substTermAsArray sym elems w (SubstTerm tm)
               vals' <- substTermAsArray sym elems w subTm
               eq <- liftIO (andAllOf sym folded =<<
                       zipWithM (\v v' -> bvEq sym v v') (toList vals) (toList vals'))
               liftIO $ assert sym eq (AssertFailureSimError "Equality condition failed" "")
         | otherwise -> fail ("Invalid word width in assertEquiv" ++ show n)

simulateHarness ::
  (1 <= w, 1 <= rw) =>
  Simulator p (SAWBack n) ->
  NatRepr rw ->
  NatRepr w ->
  SharedContext ->
  CryptolEnv ->
  ProcessedHarness ->
  SymBV (SAWBack n) w {- ^ PC -} ->
  SymBV (SAWBack n) w {- ^ Stack pointer -} ->
  SymBV (SAWBack n) w {- ^ Return address -} ->
  FnVal (SAWBack n) (VerifState rw w) (StructType (VerifState rw w)) ->
  OverrideSim p (SAWBack n) () r args ret ()
simulateHarness sim rw w sc cryEnv harness pc stack ret fn =
  do sym <- liftIO $ getInterface sim
     let prestateVarTypes = computeVarTypes Prestate harness
     let poststateVarTypes = computeVarTypes Poststate harness `Map.union` prestateVarTypes
     let endianness = verificationEndianness harness
     let sub0 = Map.fromList
                  [ (StackPointerVar,  SubstWord stack)
                  , (ReturnAddressVar, SubstWord ret)
                  ]
     regs0 <- liftIO $ emptyWordMap sym rw knownRepr
     mem0  <- liftIO $ emptyWordMap sym w knownRepr
     (sub, cryEnv', regs, mem) <- phaseUpdate sim sym rw w sc prestateVarTypes endianness
                                      (verificationPrestate harness) (sub0,cryEnv,regs0,mem0)
     assumeConditions sc cryEnv' (verificationPrestate harness)


     res <- callFnVal' fn (Ctx.Empty Ctx.:> RV pc Ctx.:> RV regs Ctx.:> RV mem)

     case res of
        Ctx.Empty Ctx.:> RV _pc' Ctx.:> RV regs' Ctx.:> RV mem' ->
          do (_sub', cryEnv'') <- computeVariableSubstitution sim sym rw w sc endianness cryEnv'
                                    poststateVarTypes (verificationPoststate harness) regs' mem' sub

             assertConditions sc cryEnv'' (verificationPoststate harness)

             -- FIXME, ugh, it's annoying to deal with this...
             --traverse (\x -> liftIO $ translateExpr sc cryEnv'' (snd x)) (verificationOutput harness)

#if !MIN_VERSION_GLASGOW_HASKELL(8,10,0,0)
        _ -> fail "Impossible! failed to deconstruct verification result!"
#endif
