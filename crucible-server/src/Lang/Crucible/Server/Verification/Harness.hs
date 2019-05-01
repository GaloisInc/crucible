-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.Verification.Harness
-- Copyright        : (c) Galois, Inc 2017
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Support for manipulating compositional verification harnesses.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Server.Verification.Harness
  ( -- * Verification Harness data types
    Offset
  , HarnessVarType(..)
  , harnessToCryptolType
  , HarnessVarDecl(..)
  , HarnessVar(..)
  , Phase(..)
  , VerificationSetupStep(..)
  , VerificationPhase(..)
  , Endianness(..)
  , VerificationHarness(..)
  , displayHarness

    -- * Parsing and preparing verification harnesses
  , ProcessedHarness
  , TCExpr
  , processHarness
  ) where

import           Control.Exception
import           Control.Lens
import           Control.Monad.State.Strict
import           Control.Monad.Reader
import           Control.Monad.Writer.Strict
--import           Control.Monad
import           Data.Foldable
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Tuple
import           Data.Word

import qualified Cryptol.ModuleSystem.Base as MB
import qualified Cryptol.ModuleSystem.Renamer as MR
import qualified Cryptol.ModuleSystem.Monad as MM
import qualified Cryptol.Parser.AST as CP
import qualified Cryptol.Parser as CP
import qualified Cryptol.Parser.Names as CP
import qualified Cryptol.TypeCheck.AST as CT
--import qualified Cryptol.TypeCheck.Monad as CT
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.PP as PP



import qualified Lang.Crucible.Proto as P

import           Verifier.SAW.SharedTerm
import           Lang.Crucible.Server.CryptolEnv

type Offset = Word64

-- | The types of values that can be involved in a verification harness
data HarnessVarType
  = HarnessVarWord Word64
    -- ^ A bitvector variable, with the given width.
    --   INVARIANT: the width is a multple of 8.
  | HarnessVarArray Word64 Word64
    -- ^ A variable representing an array of bitvectors,
    --   with the given number of elements and word width.
    --   INVARIANT: the width is a multple of 8.

-- | Compute the Cryptol type that corresponds to the given
--   harness type.
harnessToCryptolType :: HarnessVarType -> CT.Type
harnessToCryptolType (HarnessVarWord n) =
    CT.tWord (CT.tNum n)
harnessToCryptolType (HarnessVarArray elems n) =
    CT.tSeq (CT.tNum elems) (CT.tWord (CT.tNum n))

instance PP.PP HarnessVarType where
  ppPrec i = PP.ppPrec i . harnessToCryptolType

-- | A harness variable declaration, consisting of an identifier
--   and a harness type.
data HarnessVarDecl id
  = HarnessVarDecl
  { harnessVarIdent :: id
  , harnessVarType  :: HarnessVarType
  }

instance PP.PP id => PP.PP (HarnessVarDecl id) where
  ppPrec _i x = PP.pp (harnessVarIdent x) PP.<+> PP.text "::" PP.<+> PP.pp (harnessVarType x)


-- | A variable that can appear in harness setup steps.
data HarnessVar id
  = CryptolVar id
    -- ^ A user-declared variable
  | ReturnAddressVar
    -- ^ The special built-in variable representing the
    --   return address
  | StackPointerVar
    -- ^ The special built-in variable representing the
    --   current stack pointer
 deriving (Eq, Ord, Functor)

instance PP.PP id => PP.PP (HarnessVar id) where
  ppPrec i x =
     case x of
       CryptolVar nm -> PP.ppPrec i nm
       ReturnAddressVar -> PP.text "return"
       StackPointerVar  -> PP.text "stack"

-- | Verification setup steps capture the steps that are necessary
--   to setup/check the state of registers and memory before/after
--   running a verification, or when using a specification as an override.
--
--   Each of the setup steps below cause a harness variable to be set to
--   a particular value.  The semantics of this are such that, if the variable
--   is already set to some value, an equality constraint is generated to state
--   that the old value is equal to the new value.
data VerificationSetupStep id ex
  = BindVariable (HarnessVar id) ex
    -- ^ The given harness variable is assigned the given expression.

  | DeclareFreshVariable id
    -- ^ Create a fresh symbolic value and bind it to the named harness variable.

  | RegisterVal Offset (HarnessVar id)
    -- ^ Fetch the value of the given register offset into the given harness variable.
    --   The number of bytes fetched from the register file is determined by the type
    --   of the harness variable.

  | MemPointsTo (HarnessVar id) Offset (HarnessVar id)
    -- ^ The first harness var argument is interpreted as a base pointer value; the given
    --   offset is added to this value, and the value in memory is fetched and bound to the
    --   value of the second harness variable.
 deriving (Functor)

instance (PP.PP id, PP.PP ex) => PP.PP (VerificationSetupStep id ex) where
  ppPrec _i (BindVariable var ex) =
     PP.pp var PP.<+> PP.text ":=" PP.<+> PP.pp ex
  ppPrec _ (DeclareFreshVariable var) =
     PP.pp var PP.<+> PP.text ":=" PP.<+> PP.text "<fresh>"
  ppPrec _i (RegisterVal off var) =
     PP.text "reg[" PP.<.> PP.integer (fromIntegral off) PP.<.> PP.text "] :=" PP.<+> PP.pp var
  ppPrec _i (MemPointsTo base off var) =
     PP.pp base PP.<+> PP.text "+" PP.<+> PP.integer (fromIntegral off) PP.<+> PP.text "|->" PP.<+> PP.pp var

-- | A verification phase represents either the pre or post condition of a verification.
--   In either case, some fresh variables may be introduced, and their values bound using
--   the verification setup steps.  Finally, some general logical conditions can be asserted
--   as pre/post conditions.  In preconditions, such conditions will be assumed, whereas they
--   will be asserted as proof obligations in postconditions.
data VerificationPhase id ex
  = VerificationPhase
  { phaseVars  :: Seq (HarnessVarDecl id)
  , phaseSetup :: Seq (VerificationSetupStep id ex)
  , phaseConds :: Seq ex
  }
 deriving (Functor)

instance (PP.PP id, PP.PP ex) => PP.PP (VerificationPhase id ex) where
  ppPrec _i phase =
     PP.text "== Variables =="
     PP.$$
     PP.vcat (map PP.pp $ toList (phaseVars phase))
     PP.$$
     PP.text "== Setup =="
     PP.$$
     PP.vcat (map PP.pp $ toList (phaseSetup phase))
     PP.$$
     PP.text "== Conditions =="
     PP.$$
     PP.vcat (map PP.pp $ toList (phaseConds phase))

-- | Is the architecture big or little endian?
data Endianness
  = LittleEndian
  | BigEndian
 deriving (Eq, Ord, Show)

-- | A verification harness represents a function specification.
--   These harness may be used in two different modes
--
--   First, they can be used to perform a verification.  In this case,
--   the prestate phase is used to set up a fresh memory and register
--   state, before symbolically executing the program.  After the program
--   termiantes, the poststate phase is used to fetch values from the final
--   register and memory state and to collect proof obligations.
--
--   Secondly, verification harness can be used to construct "override" functions.
--   These functions render the function specification as callable subroutines
--   that simply implement the specification semantics.  In this mode, the prestate
--   is used to fetch values from the register file and memory and collect proof
--   obligiations (that the call site satisfies the preconditions).  Then, the
--   poststate phase is used to update the memory and register file.  Any generated
--   equalities or postconditions are asserted, and control is returned to the caller.
data VerificationHarness id ex
  = VerificationHarness
  { verificationOverrideName :: Text   -- ^ Human-readable name
  , verificationRegFileWidth :: Word64 -- ^ Number of bits required to address a register
  , verificationAddressWidth :: Word64 -- ^ Number of bits in a pointer for the architecture (must be a multiple of 8)
  , verificationEndianness   :: Endianness -- ^ Big or little endian?
  , verificationPrestate     :: VerificationPhase id ex -- ^ Function prestate
  , verificationPoststate    :: VerificationPhase id ex -- ^ Function poststate
  , verificationOutput       :: Maybe ex                -- ^ Optional function output (for term extraction)
  }
 deriving (Functor)

instance (PP.PP id, PP.PP ex) => PP.PP (VerificationHarness id ex) where
  ppPrec _i harness =
    PP.text ("==== Harness: " ++ (T.unpack (verificationOverrideName harness)) ++ " ====")
    PP.$$
    PP.text ( "Address width: " ++ show (verificationAddressWidth harness) ++
              "     " ++
              "Register file width: " ++ show (verificationRegFileWidth harness) ++
              "     " ++
              "Endianness: " ++ show (verificationEndianness harness))
    PP.$$
    PP.text "=== Prestate ==="
    PP.$$
    PP.pp (verificationPrestate harness)
    PP.$$
    PP.text "=== Poststate ==="
    PP.$$
    PP.pp (verificationPoststate harness)
    PP.<.>
    case (verificationOutput harness) of
      Nothing -> PP.empty
      Just o  -> PP.empty PP.$$
                 PP.text "=== Output ==="
                 PP.$$ PP.pp o

type ParseExpr = CP.Expr CP.PName
type TCExpr    = (CT.Type, CT.Expr)
type M         = ReaderT (String -> IO (), SharedContext) (StateT CryptolEnv IO)
type ProcessedHarness = VerificationHarness CT.Name TCExpr

io :: IO a -> M a
io = lift . lift

runM :: (String -> IO ()) -> SharedContext -> CryptolEnv -> M a -> IO (CryptolEnv, a)
runM hout sc cryEnv m = swap <$> runStateT (runReaderT m (hout,sc)) cryEnv

-- | Take the wire format for harness and plug the various pieces into
--   the processed verification harness data structure.
--
--   Among other tasks, this involve parsing and typechecking any embedded
--   Cryptol expressions in the verification setup steps.  This may have
--   the effect of adding new Cryptol variables to the supplied CryptolEnv.
processHarness ::
  (String -> IO ()) ->
  SharedContext ->
  CryptolEnv ->
  P.VerificationHarness ->
  IO (CryptolEnv, ProcessedHarness)
processHarness hout sc env h = runM hout sc env (doProcessHarness h)


doProcessHarness ::
   P.VerificationHarness ->
   M ProcessedHarness
doProcessHarness rawHarness =
   do let addrWidth = rawHarness^.P.verificationHarness_address_width
      let regFileWidth = rawHarness^.P.verificationHarness_reg_file_width
      let endianness = case rawHarness^.P.verificationHarness_endianness of
                           P.BigEndian -> BigEndian
                           P.LittleEndian -> LittleEndian

      mapM_ loadCryptolSource (rawHarness^.P.verificationHarness_cryptol_sources)

      prestate  <- processPhase Prestate addrWidth endianness
                      (rawHarness^.P.verificationHarness_prestate_specification)
      poststate <- processPhase Poststate addrWidth endianness
                      (rawHarness^.P.verificationHarness_poststate_specification)
      output    <- processOutputExpr (rawHarness^.P.verificationHarness_output_expr)
      unless (addrWidth `mod` 8 == 0 && addrWidth > 0)
             (fail $ "Invalid address width: " ++ show addrWidth)
      return VerificationHarness
             { verificationOverrideName = rawHarness^.P.verificationHarness_name
             , verificationPrestate     = prestate
             , verificationPoststate    = poststate
             , verificationAddressWidth = addrWidth
             , verificationRegFileWidth = regFileWidth
             , verificationEndianness   = endianness
             , verificationOutput       = output
             }

loadCryptolSource :: Text -> M ()
loadCryptolSource fname =
  do (_,sc)   <- ask
     cenv <- get
     let im = Import
              { iModule = Left $ T.unpack fname
              , iAs = Nothing
              , iSpec = Nothing
              }
     cenv' <- io $ importModule sc cenv im
     put cenv'

displayHarness ::
   PP.PP id =>
   PP.PP ex =>
   VerificationHarness id ex ->
   Text
displayHarness harness =
   T.pack . PP.render . PP.pp $ harness

processOutputExpr ::
   Text ->
   M (Maybe TCExpr)
processOutputExpr rawex
  | T.null rawex = return Nothing
  | otherwise    = Just <$>
  do cryEnv <- get
     pex <- parseCryptolExpr "extraction output term" rawex
     (cryEnv', sch, ex) <- io $ inferTerm cryEnv pex
     put cryEnv'
     case CT.isMono sch of
       Nothing -> fail "Expected monomorphic type in extraction output term"
       Just ty -> return (ty, ex)

processPhase ::
   Phase ->
   Word64 ->
   Endianness ->
   P.StateSpecification ->
   M (VerificationPhase CT.Name TCExpr)
processPhase phase addrWidth _endianness rawPhase =
   tcPhase phase addrWidth =<< parsePhase phase addrWidth rawPhase

parsePhase ::
   Phase ->
   Word64 ->
   P.StateSpecification ->
   M (VerificationPhase C.Ident ParseExpr)
parsePhase phase addrWidth rawPhase =
   do vars  <- mapM parseVar        (rawPhase^.P.stateSpecification_variables)
      specialDecls <- specialPhaseDecls phase addrWidth
      regs  <- mapM parseRegAssign  (rawPhase^.P.stateSpecification_register_assignments)
      mems  <- mapM parseMemAssign  (rawPhase^.P.stateSpecification_memory_assignments)
      binds <- mapM parseVarBinding (rawPhase^.P.stateSpecification_variable_bindings)
      conds <- mapM (parseCondition phase) (rawPhase^.P.stateSpecification_conditions)
      return VerificationPhase
             { phaseVars  = vars <> specialDecls
             , phaseSetup = regs <> mems <> binds
             , phaseConds = conds
             }

-- | Certain special variables are automatically brought into scopte in the prestate
--   of a function verification.  These are the stack pointer (which is usually located
--   in a register which is known according to the platform ABI) and the return address,
--   which is generally found either in a distinguished location on the stack or in
--   a distinguished register.
specialPhaseDecls ::
   Phase ->
   Word64 ->
   M (Seq (HarnessVarDecl C.Ident))
specialPhaseDecls Prestate addrWidth =
  do let htp = HarnessVarWord addrWidth
     return $ Seq.fromList
              [ HarnessVarDecl (fromString "stack")  htp
              , HarnessVarDecl (fromString "return") htp
              ]
specialPhaseDecls Poststate _ =
     return mempty

parseVar ::
   P.VariableSpecification ->
   M (HarnessVarDecl C.Ident)
parseVar vspec =
   do let v = C.mkIdent (vspec^.P.variableSpecification_name)
      tp <- case toList (vspec^.P.variableSpecification_dimensions) of
               [elems,width] | width `mod` 8 == 0 ->
                   return $ HarnessVarArray elems width
               [width] | width `mod` 8 == 0 ->
                   return $ HarnessVarWord width
               dims ->
                  io $ throwIO $ userError $
                     "Variable " <> T.unpack (C.identText v) <>
                     " declared with disallowed dimensions: " <>
                     show dims
      return HarnessVarDecl
             { harnessVarIdent = v
             , harnessVarType  = tp
             }

parseVariableReference ::
   P.VariableReference ->
   M (HarnessVar C.Ident)
parseVariableReference vref =
   case vref^.P.variableReference_code of
     P.StackPointerVar  -> return StackPointerVar
     P.ReturnAddressVar -> return ReturnAddressVar
     P.UserVar          -> return . CryptolVar . C.mkIdent $ vref^.P.variableReference_var_name

parseRegAssign ::
   P.RegisterAssignment ->
   M (VerificationSetupStep C.Ident ParseExpr)
parseRegAssign asgn =
   do let off = asgn^.P.registerAssignment_reg_offset
      var <- parseVariableReference (asgn^.P.registerAssignment_value)
      return $ RegisterVal off var

parseMemAssign ::
   P.MemoryAssignment ->
   M (VerificationSetupStep C.Ident ParseExpr)
parseMemAssign asgn =
   do base <- parseVariableReference (asgn^.P.memoryAssignment_base)
      let off = asgn^.P.memoryAssignment_offset
      val <- parseVariableReference (asgn^.P.memoryAssignment_value)
      return $ MemPointsTo base off val

parseVarBinding ::
   P.VariableBinding ->
   M (VerificationSetupStep C.Ident ParseExpr)
parseVarBinding bnd =
   do var  <- parseVariableReference (bnd^.P.variableBinding_var)
      let msg = "Variable binding of '" ++ show (PP.pp var) ++ "'"
      expr <- parseCryptolExpr msg (bnd^.P.variableBinding_expr)
      return $ BindVariable var expr

parseCondition ::
   Phase ->
   Text ->
   M ParseExpr
parseCondition phase expr =
  do let msg = "logical condition of " ++ phaseName phase ++ " phase"
     parseCryptolExpr msg expr

parseCryptolExpr ::
   String ->
   Text ->
   M ParseExpr
parseCryptolExpr nm expr =
   case CP.parseExpr expr of
     Left parseErr -> fail msg
        where
        msg = unlines [ ""
                      , "Parse failure while parsing Cryptol expression in " ++ nm ++ ":"
                      , "  " ++ show expr
                      , show (CP.ppError parseErr)
                      ]
     Right ex -> return ex

data Phase = Prestate | Poststate

phaseName :: Phase -> String
phaseName Prestate = "prestate"
phaseName Poststate = "poststate"

-- | Given verification phase that has been parsed off the wire, we need to
--   typecheck the raw Cryptol AST.  We first declare all the phase variables
--   with their associated types.  Then we typecheck the setup steps, and reorder
--   them (see reorderSteps).  Finally, logical conditions are typechecked.
tcPhase ::
   Phase ->
   Word64 ->
   VerificationPhase C.Ident ParseExpr ->
   M (VerificationPhase CT.Name TCExpr)
tcPhase phase addrWidth parsedPhase =
   do vars'   <- traverse declareVar (phaseVars parsedPhase)
      tcSteps <- traverse (tcSetupStep addrWidth) (phaseSetup parsedPhase)
      let varSetupSteps = fmap (DeclareFreshVariable . harnessVarIdent) vars'
      steps'  <- reorderSteps (declaredVarSet phase vars') (varSetupSteps <> tcSteps)
      conds'  <- traverse tcCond (phaseConds parsedPhase)
      return VerificationPhase
             { phaseVars  = vars'
             , phaseSetup = steps'
             , phaseConds = conds'
             }


declaredVarSet ::
   Phase ->
   Seq (HarnessVarDecl CT.Name) ->
   Set CT.Name
declaredVarSet _phase names = foldr insVar mempty names
 where
 insVar x s = Set.insert (harnessVarIdent x) s

declareVar ::
   HarnessVarDecl C.Ident ->
   M (HarnessVarDecl CT.Name)
declareVar (HarnessVarDecl ident harnessTp) =
  do let tp = harnessTypeToCryptolType harnessTp
     cryenv <- get
     let (name, cryenv') = declareIdent ident tp cryenv
     put cryenv'
     return $ HarnessVarDecl name harnessTp

tcSetupStep ::
   Word64 ->
   VerificationSetupStep C.Ident ParseExpr ->
   M (VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr))
tcSetupStep _addrWidth (DeclareFreshVariable var) =
  do (var', _tp) <- tcVar var
     return $ DeclareFreshVariable var'
tcSetupStep addrWidth (BindVariable hvar ex) =
  do (hvar', tp) <- tcHarnessVar addrWidth hvar
     ex'   <- tcExpr ex tp
     return $ BindVariable hvar' ex'
tcSetupStep addrWidth (RegisterVal offset hvar) =
  do (hvar', _tp) <- tcHarnessVar addrWidth hvar
-- FIXME, check type, should have tp == [addrWidth]
     return $ RegisterVal offset hvar'
tcSetupStep addrWidth (MemPointsTo base offset val) =
  do (base', _baseTp) <- tcHarnessVar addrWidth base
     (val' , _valTp)  <- tcHarnessVar addrWidth val
-- FIXME, check types:
--     should have baseTp == [addrWidth]
--     valTp... does it need any checks?
     return $ MemPointsTo base' offset val'

addressType :: Word64 -> CT.Type
addressType n = CT.tWord (CT.tNum n)

tcHarnessVar ::
  Word64 ->
  HarnessVar C.Ident ->
  M (HarnessVar CT.Name, CT.Type)
tcHarnessVar addrWidth var =
  case var of
    ReturnAddressVar ->
      do let tp = addressType addrWidth
         return (ReturnAddressVar, tp)
    StackPointerVar ->
      do let tp = addressType addrWidth
         return (StackPointerVar, tp)
    CryptolVar ident ->
      do (nm,tp) <- tcVar ident
         return (CryptolVar nm, tp)


tcVar ::
  C.Ident ->
  M (CT.Name, CT.Type)
tcVar ident =
      do (hout,_) <- ask
         cryEnv <- get
         let nameEnv = eExtraNames cryEnv
         let modEnv  = eModuleEnv cryEnv
         (res, ws) <- io $ MM.runModuleM (defaultEvalOpts, modEnv)
                        (MM.interactive (MB.rename C.interactiveName nameEnv (MR.renameVar (CP.mkUnqual ident))))
         unless (null ws) $ io $
           mapM_ (hout . show . PP.pp) ws
         case res of
           Left err -> fail $ "Cryptol error:\n" ++ show (PP.pp err)
           Right (nm, modEnv') ->
              case Map.lookup nm (eExtraTypes cryEnv) of
                Just (CT.Forall [] [] ty) ->
                  do put cryEnv{ eModuleEnv =  modEnv' }
                     return (nm, ty)
                _ ->
                  fail ("User harness variable not in scope: " ++ show ident)

tcExpr ::
   ParseExpr ->
   CT.Type ->
   M (CP.Expr CT.Name, TCExpr)
tcExpr pex tp =
  do cryEnv <- get
     (cryEnv1, reexpr) <- io $ renameTerm cryEnv pex
     (cryEnv2, tcexpr) <- io $ checkTerm cryEnv1 reexpr tp
     put cryEnv2
     return (reexpr, (tp,tcexpr))


tcCond ::
   ParseExpr ->
   M TCExpr
tcCond pex = snd <$> tcExpr pex CT.tBit


harnessTypeToCryptolType ::
  HarnessVarType ->
  CT.Schema
harnessTypeToCryptolType tp = CT.Forall [] [] monotype
 where
 monotype = case tp of
              HarnessVarWord sz ->
                 CT.tSeq (CT.tNum sz) $
                 CT.tBit
              HarnessVarArray elems sz ->
                 CT.tSeq (CT.tNum elems) $
                 CT.tSeq (CT.tNum sz) $
                 CT.tBit

resolveSetupVar ::
   HarnessVar CT.Name ->
   M CT.Name
resolveSetupVar var =
 case var of
   CryptolVar nm -> return nm
   StackPointerVar -> renameIdent (fromString "stack")
   ReturnAddressVar -> renameIdent (fromString "return")

 where
  renameIdent ident =
      do (hout,_) <- ask
         cryEnv <- get
         let nameEnv = eExtraNames cryEnv
         let modEnv  = eModuleEnv cryEnv
         (res, ws) <- io $ MM.runModuleM (defaultEvalOpts, modEnv)
                        (MM.interactive (MB.rename C.interactiveName nameEnv (MR.renameVar (CP.mkUnqual ident))))
         unless (null ws) $ io $
           mapM_ (hout . show . PP.pp) ws
         case res of
           Left err -> fail $ "Cryptol error:\n" ++ show (PP.pp err)
           Right (nm, modEnv') ->
                  do put cryEnv{ eModuleEnv =  modEnv' }
                     return nm

setupStepDef ::
   VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr) ->
   M CT.Name
setupStepDef (RegisterVal _ var)   = resolveSetupVar var
setupStepDef (MemPointsTo _ _ var) = resolveSetupVar var
setupStepDef (BindVariable var _)  = resolveSetupVar var
setupStepDef (DeclareFreshVariable var) = return var

setupStepUses ::
   Set CT.Name ->
   VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr) ->
   M (Set CT.Name)
setupStepUses _ (DeclareFreshVariable _) = return mempty
setupStepUses _ (RegisterVal _ _) = return mempty
setupStepUses declaredNames (MemPointsTo base _ _) =
   do basenm <- resolveSetupVar base
      return $ if Set.member basenm declaredNames then Set.singleton basenm else mempty
setupStepUses declaredNames (BindVariable _ (ex,_)) =
   return . Set.intersection declaredNames . CP.namesE $ ex


type GraphEdge = (VerificationSetupStep CT.Name TCExpr, CT.Name, Set CT.Name)

setupStepGraphEdge ::
   Set CT.Name ->
   VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr) ->
   M GraphEdge
setupStepGraphEdge declaredNames step =
   do def <- setupStepDef step
      us <- setupStepUses declaredNames step
      return (fmap snd step, def, us)


--  | This function reorders verification setps to ensure that,
--    whenever possible, variables are defined before they are used
--    (which minimizes the creation of fresh variables); and then to
--    prefer variable binding statements, then register lookup
--    statements, then memory points-to statements for defining the
--    values of variables.  This generally improves the results of
--    symbolic execution by making variable bindings more concrete.
--
--    This process works by scanning the verification setup steps in order,
--    and selecting the "best" step to perform next, and removing it from the
--    list.  A verification step can only be performed if all the variables
--    it depends on are already defined.  This process continues until no more
--    steps can be performed.  If there are any remaining steps still in the work
--    list, this means that some variables have no definition, or are part
--    of a cycle of definitions.
--
--    If a literal cycle of definitions is actually desired, the front-end should
--    introduce a "DeclareFreshVariable" step to break the cycle.
reorderSteps ::
   Set CT.Name {- ^ All delcared names in scope -} ->
   Seq (VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr)) {- ^ setup setups to reorder -} ->
   M (Seq (VerificationSetupStep CT.Name TCExpr))
reorderSteps declaredNames steps =
   do grEdges <- mapM (setupStepGraphEdge declaredNames) steps
      (definedNames, steps') <- runWriterT (processEdges mempty grEdges)
      let undefinedNames = Set.difference declaredNames definedNames
      unless (Set.null undefinedNames)
             (fail (show (PP.text "The following harness variables were declared, but"
                          PP.$$
                          PP.text "either have no definition, or have cyclic definitions:"
                          PP.$$
                          PP.nest 4 (PP.vcat (map PP.pp (toList undefinedNames))))))
      return steps'


processEdges ::
   Set CT.Name ->
   Seq GraphEdge ->
   WriterT (Seq (VerificationSetupStep CT.Name TCExpr)) M (Set CT.Name)
processEdges definedNames edges = go Nothing mempty edges

 where
 betterCandidate _ Nothing = True

 -- selecting a value from memory or registers is to be preferred to declaring
 -- a fresh symbolic value
 betterCandidate (RegisterVal _ _) (Just (DeclareFreshVariable _,_,_)) = True
 betterCandidate (MemPointsTo{}) (Just (DeclareFreshVariable _,_,_)) = True

 -- selecting from a register is generally a better way to define a value than
 -- selecting from memory
 betterCandidate (RegisterVal _ _) (Just (MemPointsTo{},_,_)) = True

 betterCandidate _ _ = False


 processEdge (step,_,_) = tell (Seq.singleton step)

 maybeSeq Nothing  = mempty
 maybeSeq (Just x) = Seq.singleton x

 go candidate zs xs = case Seq.viewl xs of
      edge@(step,def,us) Seq.:< xs'
        -- Drop variable declarations if they declare names that have
        -- already been given definitions
        | DeclareFreshVariable v <- step
        , v `Set.member` definedNames
        -> go candidate zs xs'

        -- Immediately select a variable definition step if all the variables
        -- it refers to are already defined
        | Set.isSubsetOf us definedNames
        , BindVariable _ _ <- step
        -> do processEdge edge
              processEdges (Set.insert def definedNames) (zs <> maybeSeq candidate <> xs')

        -- Tentatively select a non-variable-binding step if all the variables it
        -- refers to are already defined
        | Set.isSubsetOf us definedNames
        , betterCandidate step candidate
        -> go (Just edge) (zs <> maybeSeq candidate) xs'

        -- In all other cases, continue searching down the worklist
        | otherwise
        -> go candidate (zs Seq.|> edge) xs'

      -- We've reached the end of the worklist.  Process the candidate edge we tenatively
      -- chose earlier, or finish if no candidate was chosen.
      Seq.EmptyL -> case candidate of
                      Just edge@(_,def,_) ->
                        do processEdge edge
                           processEdges (Set.insert def definedNames) zs
                      Nothing ->
                        do return definedNames
