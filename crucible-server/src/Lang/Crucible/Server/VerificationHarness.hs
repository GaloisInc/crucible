-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.VerificationHarness
-- Copyright        : (c) Galois, Inc 2017
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Support for manipulating compositional verification harnesses.
------------------------------------------------------------------------

module Lang.Crucible.Server.VerificationHarness where

import           Control.Lens
--import           Control.Monad
import           Data.Foldable
import           Data.Monoid
import           Data.Sequence (Seq)
--import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import           Data.Word

import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.TypeCheck.AST as CT
import qualified Cryptol.TypeCheck.Monad as CT
import qualified Cryptol.Parser.AST as CP
import qualified Cryptol.Parser as CP
import qualified Cryptol.Utils.PP as PP

import qualified Lang.Crucible.Proto as P

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

data HarnessVarDecl
  = HarnessVarDecl
  { harnessVarIdent :: C.Ident
  , harnessVarType  :: HarnessVarType
  }

instance PP.PP HarnessVarDecl where
  ppPrec _i x = PP.pp (harnessVarIdent x) PP.<+> PP.text "::" PP.<+> PP.pp (harnessVarType x)

data HarnessVar
  = CryptolVar C.Ident
    -- ^ A user-declared variable
  | ReturnAddressVar
    -- ^ The special built-in variable representing the
    --   return address
  | StackPointerVar
    -- ^ The special built-in variable representing the
    --   current stack pointer

instance PP.PP HarnessVar where
  ppPrec i x =
     case x of
       CryptolVar nm -> PP.ppPrec i nm
       ReturnAddressVar -> PP.text "<return>"
       StackPointerVar  -> PP.text "<stack>"

data VerificationSetupStep ex
  = BindVariable HarnessVar ex
  | RegisterVal Offset HarnessVar
  | MemPointsTo HarnessVar Offset HarnessVar

instance PP.PP ex => PP.PP (VerificationSetupStep ex) where
  ppPrec _i (BindVariable var ex) =
     PP.pp var PP.<+> PP.pp ex
  ppPrec _i (RegisterVal off var) =
     PP.text "reg[" PP.<> PP.integer (fromIntegral off) PP.<> PP.text "] :=" PP.<+> PP.pp var
  ppPrec _i (MemPointsTo base off var) =
     PP.pp base PP.<+> PP.text "+" PP.<+> PP.integer (fromIntegral off) PP.<+> PP.text "|->" PP.<+> PP.pp var

data VerificationPhase ex
  = VerificationPhase
  { phaseVars  :: Seq HarnessVarDecl
  , phaseSetup :: Seq (VerificationSetupStep ex)
  , phaseConds :: Seq ex
  }

instance PP.PP ex => PP.PP (VerificationPhase ex) where
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


data VerificationHarness ex
  = VerificationHarness
  { verificationOverrideName :: Text
  , verificationPrestate     :: VerificationPhase ex
  , verificationPoststate    :: VerificationPhase ex
  }

type ParseExpr = CP.Expr CP.PName
type TCExpr    = CT.Expr
type M         = CT.InferM

processHarness ::
   P.VerificationHarness ->
   M (VerificationHarness TCExpr)
processHarness rawHarness =
   do prestate  <- processPhase mempty (rawHarness^.P.verificationHarness_prestate_specification)
      let prestateVars = phaseVars prestate
      poststate <- processPhase prestateVars (rawHarness^.P.verificationHarness_poststate_specification)
      return VerificationHarness
             { verificationOverrideName = rawHarness^.P.verificationHarness_name
             , verificationPrestate     = prestate
             , verificationPoststate    = poststate
             }



processPhase ::
   Seq HarnessVarDecl ->
   P.StateSpecification ->
   M (VerificationPhase TCExpr)
processPhase initVars rawPhase =
  do parsed <- parsePhase rawPhase
     CT.io $ print $ PP.pp $ parsed
     orderPhase =<< tcPhase initVars parsed

  --orderPhase <=< tcPhase initVars <=< parsePhase

parsePhase ::
   P.StateSpecification ->
   M (VerificationPhase ParseExpr)
parsePhase rawPhase =
   do vars  <- mapM parseVar        (rawPhase^.P.stateSpecification_variables)
      regs  <- mapM parseRegAssign  (rawPhase^.P.stateSpecification_register_assignments)
      mems  <- mapM parseMemAssign  (rawPhase^.P.stateSpecification_memory_assignments)
      binds <- mapM parseVarBinding (rawPhase^.P.stateSpecification_variable_bindings)
      conds <- mapM parseCondition  (rawPhase^.P.stateSpecification_conditions)
      return VerificationPhase
             { phaseVars  = vars
             , phaseSetup = regs <> mems <> binds
             , phaseConds = conds
             }

parseVar ::
   P.VariableSpecification ->
   M HarnessVarDecl
parseVar vspec =
   do let v = C.mkIdent (vspec^.P.variableSpecification_name)
      tp <- case toList (vspec^.P.variableSpecification_dimensions) of
               [elems,width] | width `mod` 8 == 0 ->
                   return $ HarnessVarArray elems width
               [width] | width `mod` 8 == 0 ->
                   return $ HarnessVarWord width
               dims ->
                   fail $
                     "Variable " <> T.unpack (C.identText v) <>
                     " declared with disallowed dimensions: " <>
                     show dims
      return HarnessVarDecl
             { harnessVarIdent = v
             , harnessVarType  = tp
             }

parseVariableReference ::
   P.VariableReference ->
   M HarnessVar
parseVariableReference vref =
   case vref^.P.variableReference_code of
     P.StackPointerVar  -> return StackPointerVar
     P.ReturnAddressVar -> return ReturnAddressVar
     P.UserVar          -> return . CryptolVar . C.mkIdent $ vref^.P.variableReference_var_name

parseRegAssign ::
   P.RegisterAssignment ->
   M (VerificationSetupStep ParseExpr)
parseRegAssign asgn =
   do let off = asgn^.P.registerAssignment_reg_offset
      var <- parseVariableReference (asgn^.P.registerAssignment_value)
      return $ RegisterVal off var

parseMemAssign ::
   P.MemoryAssignment ->
   M (VerificationSetupStep ParseExpr)
parseMemAssign asgn =
   do base <- parseVariableReference (asgn^.P.memoryAssignment_base)
      let off = asgn^.P.memoryAssignment_offset
      val <- parseVariableReference (asgn^.P.memoryAssignment_value)
      return $ MemPointsTo base off val

parseVarBinding ::
   P.VariableBinding ->
   M (VerificationSetupStep ParseExpr)
parseVarBinding bnd =
   do var  <- parseVariableReference (bnd^.P.variableBinding_var)
      expr <- parseCryptolExpr (bnd^.P.variableBinding_expr)
      return $ BindVariable var expr

parseCondition ::
   Text ->
   M ParseExpr
parseCondition = parseCryptolExpr


parseCryptolExpr ::
   Text ->
   M ParseExpr
parseCryptolExpr expr =
   case CP.parseExpr (LT.fromStrict expr) of
     Left msg -> fail (show msg)
     Right ex -> return ex


tcPhase ::
   Seq HarnessVarDecl ->
   VerificationPhase ParseExpr ->
   M (VerificationPhase TCExpr)
tcPhase _initVars _parsedPhase =
   fail "FIXME: implement tcPhase"

orderPhase ::
   VerificationPhase TCExpr ->
   M (VerificationPhase TCExpr)
orderPhase _checkedPhase =
   fail "FIXME: implement orderPhase"
