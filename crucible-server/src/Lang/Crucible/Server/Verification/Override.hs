{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Word

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some

import qualified Cryptol.TypeCheck.AST as CT
import qualified Cryptol.Utils.PP as PP

import           Lang.Crucible.Types
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Symbol
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial

import qualified Lang.Crucible.Solver.SAWCoreBackend as SAW

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
  Simulator p (SAW.SAWCoreBackend n) ->
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

type N p n r args ret a =
   OverrideSim p (SAW.SAWCoreBackend n) () r args ret a

-- | Define the behavior of a verification override.  First, bind the values of all the
--   verification harness variables from the prestate.
verificationHarnessOverride ::
   (1 <= w, 1 <= rw) =>
   Simulator p (SAW.SAWCoreBackend n) ->
   NatRepr rw ->
   NatRepr w ->
   SharedContext ->
   CryptolEnv ->
   ProcessedHarness ->
   N p n r (VerifState rw w) ret (RegValue (SAW.SAWCoreBackend n) (StructType (VerifState rw w)))
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

        _ -> fail "Impossible! failed to deconstruct verification override arguments"

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
           addAssertion sym x (AssertFailureSimError "Verification override precondition")


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
           addAssumption sym x


phaseUpdate ::
   (1 <= w, 1 <= rw) =>
   Simulator p (SAW.SAWCoreBackend n) ->
   SAW.SAWCoreBackend n ->
   NatRepr rw ->
   NatRepr w ->
   SharedContext ->
   Map (HarnessVar CT.Name) HarnessVarType ->
   Endianness ->
   VerificationPhase CT.Name TCExpr ->
   ( Subst (SAW.SAWCoreBackend n)
   , CryptolEnv
   , WordMap (SAW.SAWCoreBackend n) rw (BaseBVType 8)
   , WordMap (SAW.SAWCoreBackend n) w (BaseBVType 8)
   ) ->
   N p n r args ret
     ( Subst (SAW.SAWCoreBackend n)
     , CryptolEnv
     , WordMap (SAW.SAWCoreBackend n) rw (BaseBVType 8)
     , WordMap (SAW.SAWCoreBackend n) w (BaseBVType 8)
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
          case Map.lookup var sub of
            Just tm' ->
              do Just (Some valSize) <- return (someNat (toInteger n))
                 Just LeqProof <- return (isPosNat valSize)
                 bv <- substTermAsBV sym valSize tm'
                 regs' <- writeReg sim rw offset n endianness (SomeBV bv) regs
                 return (sub,cryEnv,regs',mem)
            Nothing ->
              do Just (Some valSize) <- return (someNat (toInteger n))
                 Just LeqProof <- return (isPosNat valSize)
                 --Right smb <- return $ userSymbol (show (PP.pp var))
                 let smb = emptySymbol
                 bv <- liftIO $ freshConstant sym smb (BaseBVRepr valSize)
                 tm <- liftIO $ SAW.toSC sym bv
                 regs' <- writeReg sim rw offset n endianness (SomeBV bv) regs
                 updateSub var tm (SubstWord bv) sub cryEnv regs' mem

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
                 off <- liftIO $ bvLit sym w (toInteger offset)
                 addr <- liftIO (bvAdd sym baseAddr off)
                 Just (Some x) <- return (someNat (toInteger n))
                 Just LeqProof <- return (isPosNat x)
                 case Map.lookup val sub of
                   Just valtm ->
                     do bv <- substTermAsBV sym x valtm
                        mem' <- writeMap sim w addr n endianness (SomeBV bv) mem
                        return (sub,cryEnv,regs,mem')
                   Nothing ->
                     do --Right smb <- return $ userSymbol (show (PP.pp val))
                        let smb = emptySymbol
                        bv <- liftIO $ freshConstant sym smb (BaseBVRepr x)
                        tm <- liftIO $ SAW.toSC sym bv
                        mem' <- writeMap sim w addr n endianness (SomeBV bv) mem
                        updateSub val tm (SubstWord bv) sub cryEnv regs mem'

            Just (HarnessVarArray _ _) ->
              fail (show (PP.text "FIXME! Implement array memory writes!: " PP.<+> PP.pp val))
            Nothing ->
              fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp val))
        Nothing ->
          fail (show (PP.text "Base pointer not defined" PP.<+> PP.pp base))

lookupWord ::
   (1 <= w) =>
   SAW.SAWCoreBackend n ->
   NatRepr w ->
   HarnessVar CT.Name ->
   Subst (SAW.SAWCoreBackend n) ->
   N p n r args ret (SymBV (SAW.SAWCoreBackend n) w)
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
  SubstWord  :: (1 <= w) => SymExpr sym (BaseBVType w) -> SubstTerm sym
  SubstTerm  :: Term -> SubstTerm sym
--  SubstArray :: (1 <= w) -> NatRepr w -> Seq (SymExpr sym (BaseBVType w)) -> SubstTerm sym

computeVariableSubstitution ::
   (1 <= rw, 1 <= w) =>
   Simulator p (SAW.SAWCoreBackend n) ->
   SAW.SAWCoreBackend n ->
   NatRepr rw ->
   NatRepr w ->
   SharedContext ->
   Endianness ->
   CryptolEnv ->
   Map (HarnessVar CT.Name) HarnessVarType ->
   VerificationPhase CT.Name TCExpr ->
   WordMap (SAW.SAWCoreBackend n) rw (BaseBVType 8) ->
   WordMap (SAW.SAWCoreBackend n) w (BaseBVType 8) ->
   Subst (SAW.SAWCoreBackend n) ->
   N p n r args ret (Subst (SAW.SAWCoreBackend n), CryptolEnv)
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
                       off <- liftIO $ bvLit sym w (toInteger offset)
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

        Just (HarnessVarArray _ _ ) ->
           fail (show (PP.text "FIXME! Implement array memory reads!: " PP.<+> PP.pp var))
        Nothing ->
           fail (show (PP.text "Impossible! Unknown type for variable: " PP.<+> PP.pp var))

termToSubstTerm ::
   SAW.SAWCoreBackend n ->
   SharedContext ->
   HarnessVarType ->
   Term ->
   N p n r args ret (SubstTerm (SAW.SAWCoreBackend n))
termToSubstTerm sym sc (HarnessVarWord n) tm =
  do x <- liftIO $ termAsConcrete sc tm
     case x of
       Just i  -> do Just (Some w) <- return (someNat (toInteger n))
                     Just LeqProof <- return (isPosNat w)
                     bv <- liftIO $ bvLit sym w i
                     return (SubstWord bv)
       Nothing -> return (SubstTerm tm)

-- FIXME? try to extract concrete values?
termToSubstTerm _ _ (HarnessVarArray _ _) tm = return (SubstTerm tm)


substTermAsBV ::
   (1 <= x, MonadIO m) =>
   SAW.SAWCoreBackend n ->
   NatRepr x ->
   SubstTerm (SAW.SAWCoreBackend n) ->
   m (SymBV (SAW.SAWCoreBackend n) x)
substTermAsBV sym w (SubstTerm tm) =
   do liftIO $ SAW.bindSAWTerm sym (BaseBVRepr w) tm
substTermAsBV _sym w (SubstWord x) =
    case testEquality w (bvWidth x) of
      Just Refl -> return x
      Nothing -> fail ("BV width mismatch " ++ show (w,bvWidth x))

-- Try to render the given SAWCore term, assumed to represent
-- a bitvector, as a concrete value.
termAsConcrete ::
   SharedContext ->
   Term ->
   IO (Maybe Integer)
termAsConcrete sc tm =
   do ss <- basic_ss sc
      tm' <- rewriteSharedTerm sc ss tm
      case getAllExts tm' of
               [] -> do sbv <- SBV.toWord =<< SBV.sbvSolveBasic (scModule sc) Map.empty [] tm'
                        return (SBV.svAsInteger sbv)
               _ -> return Nothing

defRewrites :: SharedContext -> Ident -> IO [RewriteRule]
defRewrites sc ident =
      case findDef (scModule sc) ident of
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
      , "not_not", "and_True", "and_False", "and_idem", "ite_eq"
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
   Simulator p (SAW.SAWCoreBackend n) ->
   NatRepr rw ->
   Offset ->
   Word64 ->
   Endianness ->
   WordMap (SAW.SAWCoreBackend n) rw (BaseBVType 8) ->
   N p n r args ret (SomeBV (SAW.SAWCoreBackend n))
readReg sim rw offset size endianness regs =
   do sym <- getSymInterface
      addr <- liftIO $ bvLit sym rw (toInteger offset)
      readMap sim rw addr size endianness regs

writeReg ::
   (1 <= rw) =>
   Simulator p (SAW.SAWCoreBackend n) ->
   NatRepr rw ->
   Offset ->
   Word64 ->
   Endianness ->
   SomeBV (SAW.SAWCoreBackend n) ->
   WordMap (SAW.SAWCoreBackend n) rw (BaseBVType 8) ->
   N p n r args ret (WordMap (SAW.SAWCoreBackend n) rw (BaseBVType 8))
writeReg sim rw offset size endianness val regs =
  do sym <- getSymInterface
     addr <- liftIO $ bvLit sym rw (toInteger offset)
     writeMap sim rw addr size endianness val regs

writeMap ::
   (1 <= x) =>
   Simulator p (SAW.SAWCoreBackend n) ->
   NatRepr x ->
   SymBV (SAW.SAWCoreBackend n) x ->
   Word64 ->
   Endianness ->
   SomeBV (SAW.SAWCoreBackend n) ->
   WordMap (SAW.SAWCoreBackend n) x (BaseBVType 8) ->
   N p n r args ret (WordMap (SAW.SAWCoreBackend n) x (BaseBVType 8))

writeMap sim x addr size endianness (SomeBV val) wordmap
   | r == 0
   , Just (Some valWidth) <- (someNat (toInteger size))
   , Just Refl <- testEquality valWidth (bvWidth val)
   , Just LeqProof <- (isPosNat valWidth)
   =   do sym <- getSymInterface
          SomeHandle h <- liftIO $
             getPredefinedHandle sim (MultiPartStoreHandle (fromIntegral (natValue x)) 8 (fromIntegral bytes)) $
                SomeHandle <$> multipartStoreFn sim x (knownRepr :: NatRepr 8) valWidth (fromIntegral bytes)
          Just Refl <- return (testEquality
                          (handleArgTypes h)
                          (Ctx.Empty Ctx.:>
                           BoolRepr Ctx.:>
                           BVRepr x Ctx.:>
                           BVRepr valWidth Ctx.:>
                           WordMapRepr x (BaseBVRepr (knownRepr :: NatRepr 8))))
          Just Refl <- return (testEquality (handleReturnType h)
                           (WordMapRepr x (BaseBVRepr (knownRepr :: NatRepr 8))))
          let endianBool = case endianness of BigEndian -> truePred sym; LittleEndian -> falsePred sym
          let args = Ctx.Empty Ctx.:> RegEntry knownRepr endianBool
                               Ctx.:> RegEntry (BVRepr x) addr
                               Ctx.:> RegEntry (BVRepr valWidth) val
                               Ctx.:> RegEntry (WordMapRepr x (BaseBVRepr knownRepr)) wordmap
          regValue <$> callFnVal (HandleFnVal h) (RegMap args)

   | otherwise = fail ("Invalid arguments to writeMap")
  where
   (bytes,r) = divMod size 8


readMap ::
   (1 <= x) =>
   Simulator p (SAW.SAWCoreBackend n) ->
   NatRepr x ->
   SymBV (SAW.SAWCoreBackend n) x ->
   Word64 ->
   Endianness ->
   WordMap (SAW.SAWCoreBackend n) x (BaseBVType 8) ->
   N p n r args ret (SomeBV (SAW.SAWCoreBackend n))
readMap sim x addr size endianness wordmap
   | r == 0 =
       do sym <- getSymInterface
          Just (Some valWidth) <- return (someNat (toInteger size))
          Just LeqProof <- return (isPosNat valWidth)
          SomeHandle h <- liftIO $
             getPredefinedHandle sim (MultiPartLoadHandle (fromIntegral (natValue x)) 8 (fromIntegral bytes)) $
                SomeHandle <$> multipartLoadFn sim x (knownRepr :: NatRepr 8) valWidth (fromIntegral bytes)
          Just Refl <- return (testEquality
                          (handleArgTypes h)
                          (Ctx.Empty Ctx.:>
                           BoolRepr Ctx.:>
                           BVRepr x Ctx.:>
                           WordMapRepr x (BaseBVRepr (knownRepr :: NatRepr 8)) Ctx.:>
                           MaybeRepr (BVRepr (knownRepr :: NatRepr 8))))
          Just Refl <- return (testEquality (handleReturnType h) (BVRepr valWidth))
          let endianBool = case endianness of BigEndian -> truePred sym; LittleEndian -> falsePred sym
          let args = Ctx.Empty Ctx.:> RegEntry knownRepr endianBool
                               Ctx.:> RegEntry (BVRepr x) addr
                               Ctx.:> RegEntry (WordMapRepr x (BaseBVRepr knownRepr)) wordmap
                               Ctx.:> RegEntry (MaybeRepr (BVRepr knownRepr)) Unassigned
          SomeBV . regValue <$> callFnVal (HandleFnVal h) (RegMap args)

   | otherwise = fail ("Word size not a multiple of 8: " ++ show size)
  where
   (bytes,r) = divMod size 8


data SomeBV sym where
  SomeBV :: forall sym w. (1 <= w) => SymExpr sym (BaseBVType w) -> SomeBV sym

{-
concatBVs ::
   forall sym.
   IsExprBuilder sym =>
   sym ->
   [SomeBV sym] ->
   IO (SomeBV sym)
concatBVs sym [] = fail "cannot concat an empty sequence of bitvectors"
concatBVs sym (x:xs) = go x xs
 where
 go acc [] = return acc
 go (SomeBV (acc :: SymExpr sym (BaseBVType a)))
    (SomeBV (h   :: SymExpr sym (BaseBVType b)) : t) =
     let proof :: LeqProof 1 (a+b)
         proof = leqAdd (leqProof (Proxy :: Proxy 1) (Proxy :: Proxy a)) (Proxy :: Proxy b)
      in withLeqProof proof $
          do z <- bvConcat sym acc h
             go (SomeBV z) t

wordMapLoad ::
   (1 <= w) =>
   (1 <= n) =>
   IsSymInterface sym =>
   sym ->
   NatRepr w ->
   NatRepr n ->
   Endianness ->
   Integer ->
   SymBV sym w ->
   WordMap sym w (BaseBVType n) ->
   IO (SomeBV sym)
wordMapLoad sym w n endianness num idx map
  | num < 1 = fail "Must load at least one byte"
  | otherwise =
      do cells <- mapM (\off -> do i <- bvAdd sym idx =<< bvLit sym w off
                                   x <- lookupWordMap sym w (BaseBVRepr n) i map
                                   let msg = "WordMap: read an undefined index" ++
                                              case asUnsignedBV i of
                                                Nothing  -> ""
                                                Just idx -> " 0x" ++ showHex idx ""
                                   let ex = ReadBeforeWriteSimError msg
                                   SomeBV <$> readPartExpr sym x ex)
                       offsets
         concatBVs sym cells

  where
   offsets = case endianness of
               BigEndian    -> [0 .. num-1]
               LittleEndian -> reverse [0 .. num-1]
-}

assumeEquiv ::
   MonadIO m =>
   SAW.SAWCoreBackend n ->
   HarnessVarType ->
   Term ->
   SubstTerm (SAW.SAWCoreBackend n) ->
   m ()
assumeEquiv sym hvt tm subTm =
     case hvt of
       HarnessVarWord n
         | Just (Some w) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat w
         -> do tm' <- liftIO $ SAW.bindSAWTerm sym (BaseBVRepr w) tm
               subTm' <- substTermAsBV sym w subTm
               eq  <- liftIO $ bvEq sym tm' subTm'
               liftIO $ addAssumption sym eq
         | otherwise -> fail ("Invalid word width in assumeEquiv" ++ show n)

       HarnessVarArray _elems _n ->
         fail "FIXME assumeEquiv for arrays"


assertEquiv ::
   MonadIO m =>
   SAW.SAWCoreBackend n ->
   HarnessVarType ->
   Term ->
   SubstTerm (SAW.SAWCoreBackend n) ->
   m ()
assertEquiv sym hvt tm subTm =
     case hvt of
       HarnessVarWord n
         | Just (Some w) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat w
         -> do tm' <- liftIO $ SAW.bindSAWTerm sym (BaseBVRepr w) tm
               subTm' <- substTermAsBV sym w subTm
               eq  <- liftIO $ bvEq sym tm' subTm'
               liftIO $ addAssertion sym eq (AssertFailureSimError "Equality condition failed")
         | otherwise -> fail ("Invalid word width in assertEquiv" ++ show n)

       HarnessVarArray _elems _n ->
         fail "FIXME assertEquiv for arrays"


simulateHarness ::
  (1 <= w, 1 <= rw) =>
  Simulator p (SAW.SAWCoreBackend n) ->
  NatRepr rw ->
  NatRepr w ->
  SharedContext ->
  CryptolEnv ->
  ProcessedHarness ->
  SymBV (SAW.SAWCoreBackend n) w {- ^ PC -} ->
  SymBV (SAW.SAWCoreBackend n) w {- ^ Stack pointer -} ->
  SymBV (SAW.SAWCoreBackend n) w {- ^ Return address -} ->
  FnVal (SAW.SAWCoreBackend n) (VerifState rw w) (StructType (VerifState rw w)) ->
  OverrideSim p (SAW.SAWCoreBackend n) () r args ret ()
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

        _ -> fail "Impossible! failed to deconstruct verification result!"


{-
data VerificationSetupStep id ex
  = BindVariable (HarnessVar id) ex
  | RegisterVal Offset (HarnessVar id)
  | MemPointsTo (HarnessVar id) Offset (HarnessVar id)
 deriving (Functor)
-}