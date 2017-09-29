{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}

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

module Lang.Crucible.Server.Verification.Harness where

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
import qualified Data.Text.Lazy as LT
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

data HarnessVarType
  = HarnessVarWord Word64
    -- ^ A bitvector variable, with the given width.
    --   INVARIANT: the width is a multple of 8.
  | HarnessVarArray Word64 Word64
    -- ^ A variable representing an array of bitvectors,
    --   with the given number of elements and word width.
    --   INVARIANT: the width is a multple of 8.

harnessToCryptolType :: HarnessVarType -> CT.Type
harnessToCryptolType (HarnessVarWord n) =
    CT.tWord (CT.tNum n)
harnessToCryptolType (HarnessVarArray elems n) =
    CT.tSeq (CT.tNum elems) (CT.tWord (CT.tNum n))

instance PP.PP HarnessVarType where
  ppPrec i = PP.ppPrec i . harnessToCryptolType

data HarnessVarDecl id
  = HarnessVarDecl
  { harnessVarIdent :: id
  , harnessVarType  :: HarnessVarType
  }

instance PP.PP id => PP.PP (HarnessVarDecl id) where
  ppPrec _i x = PP.pp (harnessVarIdent x) PP.<+> PP.text "::" PP.<+> PP.pp (harnessVarType x)

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

data VerificationSetupStep id ex
  = BindVariable (HarnessVar id) ex
  | RegisterVal Offset (HarnessVar id)
  | MemPointsTo (HarnessVar id) Offset (HarnessVar id)
 deriving (Functor)


instance (PP.PP id, PP.PP ex) => PP.PP (VerificationSetupStep id ex) where
  ppPrec _i (BindVariable var ex) =
     PP.pp var PP.<+> PP.text ":=" PP.<+> PP.pp ex
  ppPrec _i (RegisterVal off var) =
     PP.text "reg[" PP.<> PP.integer (fromIntegral off) PP.<> PP.text "] :=" PP.<+> PP.pp var
  ppPrec _i (MemPointsTo base off var) =
     PP.pp base PP.<+> PP.text "+" PP.<+> PP.integer (fromIntegral off) PP.<+> PP.text "|->" PP.<+> PP.pp var

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

data Endianness
  = LittleEndian
  | BigEndian
 deriving (Eq, Ord, Show)

data VerificationHarness id ex
  = VerificationHarness
  { verificationOverrideName :: Text
  , verificationAddressWidth :: Word64
  , verificationEndianness   :: Endianness
  , verificationPrestate     :: VerificationPhase id ex
  , verificationPoststate    :: VerificationPhase id ex
  }
 deriving (Functor)

instance (PP.PP id, PP.PP ex) => PP.PP (VerificationHarness id ex) where
  ppPrec _i harness =
    PP.text ("==== Harness: " ++ (T.unpack (verificationOverrideName harness)) ++ " ====")
    PP.$$
    PP.text ( "Address width: " ++ show (verificationAddressWidth harness) ++
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

type ParseExpr = CP.Expr CP.PName
type TCExpr    = (CT.Type, CT.Expr)
type M         = ReaderT SharedContext (StateT CryptolEnv IO)
type ProcessedHarness = VerificationHarness CT.Name TCExpr

io :: IO a -> M a
io = lift . lift

runM :: SharedContext -> CryptolEnv -> M a -> IO (CryptolEnv, a)
runM sc cryEnv m = swap <$> runStateT (runReaderT m sc) cryEnv

processHarness ::
   P.VerificationHarness ->
   M ProcessedHarness
processHarness rawHarness =
   do let addrWidth = rawHarness^.P.verificationHarness_address_width
      let endianness = case rawHarness^.P.verificationHarness_endianness of
                           P.BigEndian -> BigEndian
                           P.LittleEndian -> LittleEndian
      prestate  <- processPhase Prestate addrWidth endianness
                      (rawHarness^.P.verificationHarness_prestate_specification)
      poststate <- processPhase Poststate addrWidth endianness
                      (rawHarness^.P.verificationHarness_poststate_specification)
      unless (addrWidth `mod` 8 == 0 && addrWidth > 0)
             (fail $ "Invalid address width: " ++ show addrWidth)
      return VerificationHarness
             { verificationOverrideName = rawHarness^.P.verificationHarness_name
             , verificationPrestate     = prestate
             , verificationPoststate    = poststate
             , verificationAddressWidth = addrWidth
             , verificationEndianness   = endianness
             }

displayHarness ::
   PP.PP id =>
   PP.PP ex =>
   VerificationHarness id ex ->
   Text
displayHarness harness =
   T.pack . PP.render . PP.pp $ harness

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
   case CP.parseExpr (LT.fromStrict expr) of
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

tcPhase ::
   Phase ->
   Word64 ->
   VerificationPhase C.Ident ParseExpr ->
   M (VerificationPhase CT.Name TCExpr)
tcPhase phase addrWidth parsedPhase =
   do vars'  <- traverse declareVar (phaseVars parsedPhase)
      steps' <- reorderSteps (declaredVarSet phase vars') =<< traverse (tcSetupStep addrWidth) (phaseSetup parsedPhase)
      conds' <- traverse tcCond (phaseConds parsedPhase)
      return VerificationPhase
             { phaseVars  = vars'
             , phaseSetup = steps'
             , phaseConds = conds'
             }


declaredVarSet ::
   Phase ->
   Seq (HarnessVarDecl CT.Name) ->
   Set CT.Name
declaredVarSet phase names = foldr insVar mempty names
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
tcSetupStep addrWidth (BindVariable hvar ex) =
  do (hvar', tp) <- tcHarnessVar addrWidth hvar
     ex'   <- tcExpr ex tp
     return $ BindVariable hvar' ex'
tcSetupStep addrWidth (RegisterVal offset hvar) =
  do (hvar', tp) <- tcHarnessVar addrWidth hvar
-- FIXME, check type, should have tp == [addrWidth]
     return $ RegisterVal offset hvar'
tcSetupStep addrWidth (MemPointsTo base offset val) =
  do (base', baseTp) <- tcHarnessVar addrWidth base
     (val' , valTp)  <- tcHarnessVar addrWidth val
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

 where
  tcVar ident =
      do cryEnv <- get
         let nameEnv = eExtraNames cryEnv
         let modEnv  = eModuleEnv cryEnv
         (res, _ws) <- io $ MM.runModuleM modEnv
                        (MM.interactive (MB.rename C.interactiveName nameEnv (MR.renameVar (CP.mkUnqual ident))))
         -- ?? FIXME, what about warnings?
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
  do sc <- ask
     cryEnv <- get
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
      do cryEnv <- get
         let nameEnv = eExtraNames cryEnv
         let modEnv  = eModuleEnv cryEnv
         (res, _ws) <- io $ MM.runModuleM modEnv
                        (MM.interactive (MB.rename C.interactiveName nameEnv (MR.renameVar (CP.mkUnqual ident))))
         -- ?? FIXME, what about warnings?
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

setupStepUses ::
   Set CT.Name ->
   VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr) ->
   M (Set CT.Name)
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
      uses <- setupStepUses declaredNames step
      return (fmap snd step, def, uses)

reorderSteps ::
   Set CT.Name ->
   Seq (VerificationSetupStep CT.Name (CP.Expr CT.Name, TCExpr)) ->
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
 betterCandidate (RegisterVal _ _) (Just (MemPointsTo _ _ _,_,_)) = True
 betterCandidate _ _ = False

 processEdge (step,_,_) = tell (Seq.singleton step)

 maybeSeq Nothing  = mempty
 maybeSeq (Just x) = Seq.singleton x

 go candidate zs xs = case Seq.viewl xs of
      edge@(step,def,uses) Seq.:< xs'
        | Set.isSubsetOf uses definedNames
        , BindVariable _ _ <- step
        -> do processEdge edge
              processEdges (Set.insert def definedNames) (zs <> maybeSeq candidate <> xs')

        | Set.isSubsetOf uses definedNames
        , betterCandidate step candidate
        -> go (Just edge) (zs <> maybeSeq candidate) xs'

        | otherwise
        -> go candidate (zs Seq.|> edge) xs'

      Seq.EmptyL -> case candidate of
                      Just edge@(_,def,_) ->
                        do processEdge edge
                           processEdges (Set.insert def definedNames) zs
                      Nothing ->
                        do return definedNames
