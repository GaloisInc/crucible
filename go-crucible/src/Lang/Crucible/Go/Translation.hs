{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}

module Lang.Crucible.Go.Translation (translateFunction) where

import Language.Go.AST
import Language.Go.Types

import qualified Lang.Crucible.Core as C
import qualified Lang.Crucible.Generator as Gen
import Lang.Crucible.Types
import Lang.Crucible.SSAConversion( toSSA )
import Lang.Crucible.FunctionHandle
import Lang.Crucible.FunctionName (functionNameFromText)
import Lang.Crucible.ProgramLoc

import Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Foldable as F
import Data.Maybe ( maybeToList )
import Control.Monad.ST ( ST )
import Control.Monad ( liftM, zipWithM, void )
import qualified Control.Monad.State as St
import Data.Text (Text)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Default.Class
import qualified Data.List.NonEmpty as NE

-- | (Currently) the entry point of the module: translates one go
-- function to a Crucible control-flow graph. The parameters are the
-- same as for the `FunctionDecl` AST constructor.
translateFunction :: forall h. (?machineWordWidth :: Int)
                  => Id SourceRange -- ^ Function name
                  -> ParameterList SourceRange -- ^ Function parameters
                  -> ReturnList SourceRange
                  -> [Statement SourceRange] -> ST h C.AnyCFG
translateFunction (Id _ bind fname) params returns body =
  withHandleAllocator $ \ha ->
  bindReturns returns $ \(retctx :: CtxRepr tretctx) setupReturns ->
  bindParams params $ \(ctx :: CtxRepr tctx) setupParams ->
  do fnhandle <- mkHandle' ha (functionNameFromText fname) ctx (StructRepr retctx)
     (Gen.SomeCFG g, []) <- Gen.defineFunction InternalPos fnhandle
                        (\assignment -> (def,
                                         do retslots <- setupReturns
                                            St.modify' (\ts -> ts {returnSlots = retslots})

                                            setupParams assignment
                                            graphGenerator body retctx))
     case toSSA g of
       C.SomeCFG gs -> return $ C.AnyCFG gs

type GoGenerator h s rctx a = Gen.Generator h s (TransState rctx) (StructType rctx) a

-- | Bind the list of return values to both the function return type
-- in the crucible CFG and, if the return values are named, to
-- crucible registers mapped to the names. Like many functions here,
-- uses, continuation-passing style to construct heterogeneous lists
-- and work with type-level literals.
bindReturns :: (?machineWordWidth :: Int)
            => ReturnList SourceRange
            -> (forall ctx. CtxRepr ctx -> (forall s rctx. GoGenerator h s rctx (Maybe (VariableAssignment s ctx))) -> a)
            -> a
bindReturns rlist f =
  let goNamed :: [NamedParameter SourceRange]
              -> (forall ctx. CtxRepr ctx -> (forall s rctx. GoGenerator h s rctx (VariableAssignment s ctx)) -> a)
              -> a
      goNamed [] k = k Ctx.empty (return Ctx.empty)
      goNamed (np@(NamedParameter _ (Id _ _ rname) _):ps) k =
        translateType {- TODO Abstract this: implicit parameter or generator state -}
           (fromRight $ getType np) (\t zv ->
                    goNamed ps (\ctx gen -> k (ctx Ctx.%> t)
                                 (do assign <- gen
                                     reg <- declareVar rname zv t
                                     return (assign Ctx.%> GoVarOpen reg))
                               ))
      goAnon :: [Type SourceRange] -> (forall ctx. CtxRepr ctx -> a) -> a
      goAnon [] k = k Ctx.empty
      goAnon (t:ts) k = case getType t of
        Right vt -> translateType vt $ \t' _ ->
          goAnon ts (\ctx -> k (ctx Ctx.%> t'))
        _ -> error "Expecting a semantic type inferred for a return type, but found none"
  in case rlist of
    NamedReturnList _ nrets -> goNamed nrets $ \ctx gen -> f ctx (Just <$> gen)
    AnonymousReturnList _ rtypes -> goAnon rtypes $ \ctx -> f ctx (return Nothing)


type VariableAssignment s ctx = Ctx.Assignment (GoVarOpen s) ctx

-- | GoVarReg and GoVarOpen are respectively the closed (abstracting
-- from type parameters) and open representations of Crucible
-- registers that store the value of a variable with a given type.

newtype GoVarOpen s tp = GoVarOpen {unGoVarOpen :: Gen.Reg s (ReferenceType tp)}
data GoVarReg s where
  GoVarReg :: TypeRepr tp -> Gen.Reg s (ReferenceType tp) -> GoVarReg s

-- | Generate the Crucible type context and bind parameter names to
-- (typed) Crucible registers.
bindParams :: (?machineWordWidth :: Int)
           => ParameterList SourceRange
           -> (forall ctx. CtxRepr ctx
               -> (forall s. Ctx.Assignment (Gen.Atom s) ctx -> GoGenerator h s rctx ())
               -> a)
           -> a
bindParams plist f =
  let go :: [NamedParameter SourceRange]
         -> (forall ctx. CtxRepr ctx
             -> (forall s. Ctx.Assignment (Gen.Atom s) ctx -> GoGenerator h s rctx ())
             -> a)
         -> a
      go []     k = k Ctx.empty (\_ -> return ())
      go (np@(NamedParameter _ (Id _ _ pname) _):ps) k =
        translateType 
        (fromRight $ getType np) $ \t zv -> go ps (\ctx f' -> k (ctx Ctx.%> t) 
                                                       (\a -> do f' (Ctx.init a)
                                                                 void $ declareVar pname (Gen.AtomExpr (Ctx.last a)) t))
  in case plist of
    NamedParameterList _ params mspread -> go (params ++ maybeToList mspread) f
    AnonymousParameterList _ _ _ -> error "Unexpected anonymous parameter list in a function definition"

-- | State of translation: the user state part of the Generator monad used here.
data TransState ctx s = TransState
  {lexenv :: !(HashMap Text (GoVarReg s)) -- ^ A mapping from variable names to registers
  ,explicitLabels :: !(HashMap Text (Gen.Label s))
  -- ^ A mapping of explicitly-introduced Go label names to their
  -- corresponding Crucible block labels
  ,enclosingBreaks :: !(LabelStack s)
  -- ^ The stack of enclosing break labels
  ,enclosingContinues :: !(LabelStack s)
  -- ^ The stack of enclosing continue labels
  ,returnSlots :: !(Maybe (VariableAssignment s ctx))
   -- ^ The list of registers that represent the components of the
   -- return value. Crucible functions can only have one return value,
   -- while Go functions can have multiple. To deal with that we
   -- multiplex return values in a struct that would store references
   -- to return values. The struct is going to be created from the
   -- variable assignment in this component of the user state.
  ,machineWordWidth :: !Int -- ^ size of the machine word
  }

instance Default (TransState ctx s) where
  def = TransState {lexenv = HM.empty
                   ,explicitLabels = HM.empty
                   ,enclosingBreaks = LabelStack []
                   ,enclosingContinues = LabelStack []
                   ,returnSlots = Nothing
                   ,machineWordWidth = 32
                   }


newtype LabelStack s = LabelStack [Gen.Label s]

getMachineWordWidth :: GoGenerator h s rctx Int
getMachineWordWidth = St.gets machineWordWidth

setMachineWordWidth :: Int -> GoGenerator h s rctx ()
setMachineWordWidth w = St.modify' (\ts -> ts {machineWordWidth = w})

-- | Fully specialize a type with the current machine word width
specializeTypeM :: SemanticType -> GoGenerator h s rctx SemanticType
specializeTypeM typ = do w <- getMachineWordWidth
                         return $ specializeType w typ

declareVar :: Text -> Gen.Expr s tp -> TypeRepr tp -> GoGenerator h s rctx (Gen.Reg s (ReferenceType tp))
declareVar name value t = do ref <- Gen.newReference value
                             reg <- Gen.newReg ref
                             St.modify' (\ts -> ts {lexenv = HM.insert name (GoVarReg t reg) (lexenv ts)})
                             return reg

graphGenerator :: [Statement SourceRange] -> CtxRepr rctx -> GoGenerator h s rctx a --(Gen.Expr s (StructType rctx))
graphGenerator body ctxrepr = do
  -- First, traverse all of the statements of the function to allocate
  -- Crucible labels for each source level label.  We need this to
  -- handle gotos, named breaks, and named continues.
  -- Gen.endNow $ \cont -> do
  --   entry_label <- Gen.newLabel
  --   labelMap <- F.foldlM buildLabelMap HM.empty body
  --   St.modify' $ \s -> s { explicitLabels = labelMap }
  --   Gen.resume_ entry_label cont

  mapM_ (\s -> translateStatement s ctxrepr) body
  -- The following is going to be a fallthrough block that would
  -- never be reachable if all the exit paths in the function graph
  -- end with a return statement.
  Gen.reportError $ Gen.App (C.TextLit "Expected a return statement, but found none.")

-- | For each statement defining a label, populate the hash map with a
-- fresh crucible label.
buildLabelMap :: HashMap Text (Gen.Label s)
              -> Statement SourceRange
              -> Gen.End h s t init ret (HashMap Text (Gen.Label s))
buildLabelMap m stmt =
  case stmt of
    LabeledStmt _ (Label _ labelName) stmt' -> do
      lbl <- Gen.newLabel
      buildLabelMap (HM.insert labelName lbl m) stmt'
    BlockStmt _ stmts -> F.foldlM buildLabelMap m stmts
    IfStmt _ mguard _ then_ else_ -> do
      m1 <- maybe (return m) (buildLabelMap m) mguard
      m2 <- F.foldlM buildLabelMap m1 then_
      F.foldlM buildLabelMap m2 else_
    ExprSwitchStmt _ mguard _ clauses -> do
      m1 <- maybe (return m) (buildLabelMap m) mguard
      F.foldlM (\m' (ExprClause _ _ stmts) -> F.foldlM buildLabelMap m' stmts) m1 clauses
    TypeSwitchStmt _ mguard _ clauses -> do
      m1 <- maybe (return m) (buildLabelMap m) mguard
      F.foldlM (\m' (TypeClause _ _ stmts) -> F.foldlM buildLabelMap m' stmts) m1 clauses
    ForStmt _ (ForClause _ minit _ mpost) stmts -> do
      m1 <- maybe (return m) (buildLabelMap m) minit
      m2 <- maybe (return m1) (buildLabelMap m1) mpost
      F.foldlM buildLabelMap m2 stmts
    ForStmt _ (ForRange {}) stmts ->
      F.foldlM buildLabelMap m stmts
    GoStmt {} -> return m
    SelectStmt _ clauses ->
      F.foldlM (\m' (CommClause _ _ stmts) -> F.foldlM buildLabelMap m' stmts) m clauses
    BreakStmt {} -> return m
    ContinueStmt {} -> return m
    ReturnStmt {} -> return m
    GotoStmt {} -> return m
    FallthroughStmt {} -> return m
    DeferStmt {} -> return m
    ShortVarDeclStmt {} -> return m
    AssignStmt {} -> return m
    UnaryAssignStmt {} -> return m
    DeclStmt {} -> return m
    ExpressionStmt {} -> return m
    EmptyStmt {} -> return m
    SendStmt {} -> return m

-- | Translates individual statements. This is where Go statement
-- semantics is encoded.
--
-- Note that we currently only support single return values (and no
-- return via named return values).
translateStatement :: Statement SourceRange
                   -> CtxRepr rctx
                   -> GoGenerator h s rctx ()
translateStatement s retCtxRepr = case s of
  DeclStmt _ (VarDecl _ varspecs)     -> mapM_ translateVarSpec varspecs
  DeclStmt _ (ConstDecl _ constspecs) -> mapM_ translateConstSpec constspecs
  DeclStmt _ (TypeDecl _ _) ->
    -- type declarations are only reflected in type analysis results
    -- and type translations; they are not executable
    return ()
  ExpressionStmt _ expr -> withTranslatedExpression expr (const (return ()))
    -- The number of expressions (|e|) in `lhs` and `rhs` should
    -- either be the same, or |rhs| = 1. Assigning multi-valued
    -- right-hand sides (|rhs|=1 and |lhs| > 1) is not currently
    -- supported.
  AssignStmt _ lhs Assignment rhs
    | F.length lhs == F.length rhs -> mapM_ translateAssignment (NE.zip lhs rhs)
    | otherwise -> error "Mismatched assignment expression lengths"
  ReturnStmt _ [e] ->
    withTranslatedExpression e $ \e' ->
      case e' of
        _ | Just Refl <- testEquality (Ctx.empty Ctx.%> (exprType e')) retCtxRepr ->
            Gen.returnFromFunction $ Gen.App $ C.MkStruct retCtxRepr (Ctx.empty Ctx.%> e')
          | otherwise -> error ("translateStatement error: Incorrect return type: " ++ show e ++ " Expected type: " ++ show retCtxRepr ++ " Actual type: " ++ show (exprType e'))
  ReturnStmt _ _ -> error ("translateStatement: Multiple return values are not yet supported: " ++ show s)
  EmptyStmt _ -> return ()
  LabeledStmt _ (Label _ labelName) stmt -> do
    Gen.endNow $ \cont -> do
      exit_lbl <- Gen.newLabel
      lbls <- St.gets explicitLabels
      lbl <- case HM.lookup labelName lbls of
        Nothing -> error ("Missing definition of label: " ++ show labelName)
        Just l -> return l

      Gen.endCurrentBlock (Gen.Jump lbl)
      Gen.defineBlock lbl $ do
        -- NOTE: I'm not sure if this state modification is valid in
        -- the presence of this continuation... will require testing.
        St.modify' $ \st -> st { explicitLabels = HM.insert labelName lbl (explicitLabels st) }
        translateStatement stmt retCtxRepr
      Gen.resume_ exit_lbl cont
  GotoStmt _ (Label _ labelName) -> do
    lbls <- St.gets explicitLabels
    case HM.lookup labelName lbls of
      Nothing -> error ("Jump to undeclared label: " ++ show s)
      Just lbl -> Gen.jump lbl
  BlockStmt _ body -> translateBlock body retCtxRepr
  IfStmt _ mguard e then_ else_ -> do
    F.forM_ mguard $ flip translateStatement retCtxRepr
    withTranslatedExpression e $ \e' -> do
      case e' of
        _ | Just Refl <- testEquality (exprType e') BoolRepr ->
              Gen.ifte_ e' (translateBlock then_ retCtxRepr) (translateBlock else_ retCtxRepr)
          | otherwise -> error ("translateStatement: Invalid type for if statement condition: " ++ show e)

  -- This translation is very verbose because we can't re-use the
  -- Gen.when combinator.  We need the labels to implement break and
  -- continue, and Gen.when would make them inaccessible.  Note that
  -- this will still be tricky, because we somehow need to get those
  -- labels out of the End monad so that we can store them in the
  -- state.
  --
  -- Instead of that, maybe we just need to explicitly pass the
  -- current loop context into translateStatement and translateBlock.
  -- Maybe we can just capture them in the scope of translateBlock.
  ForStmt _ (ForClause _ minitializer mcondition mincrement) body -> do
    F.forM_ minitializer $ \initializer -> translateStatement initializer retCtxRepr
    Gen.endNow $ \cont -> do
      cond_lbl <- Gen.newLabel
      loop_lbl <- Gen.newLabel
      exit_lbl <- Gen.newLabel

      Gen.endCurrentBlock (Gen.Jump cond_lbl)

      Gen.defineBlock cond_lbl $ do
        case mcondition of
          Nothing -> Gen.jump loop_lbl
          Just cond -> do
            withTranslatedExpression cond $ \cond' -> do
              case cond' of
                _ | Just Refl <- testEquality (exprType cond') BoolRepr ->
                    Gen.branch cond' loop_lbl exit_lbl
                  | otherwise -> error ("Invalid condition type in for loop: " ++ show s)
      Gen.defineBlock loop_lbl $ do
        -- Push the break and continue labels onto the stack so that
        -- nested break statements can reference them.  We'll pop them
        -- back off once we are done translating the body.
        withLoopLabels exit_lbl cond_lbl $ do
          translateBlock body retCtxRepr
          F.forM_ mincrement $ \increment -> translateStatement increment retCtxRepr

        Gen.jump cond_lbl
      Gen.resume_ exit_lbl cont

  BreakStmt _ Nothing -> do
    bs <- St.gets enclosingBreaks
    case bs of
      LabelStack (b:_) -> Gen.jump b
      LabelStack [] -> error "Empty break stack for break statement"
  BreakStmt _ (Just _) -> error "Named breaks are not supported yet"
  ContinueStmt _ Nothing -> do
    cs <- St.gets enclosingContinues
    case cs of
      LabelStack (c:_) -> Gen.jump c
      LabelStack [] -> error "Empty continue stack for continue statement"
  ContinueStmt _ (Just _) -> error "Named continues are not supported yet"
  SendStmt {} -> error "Send statements are not supported yet"
  UnaryAssignStmt {} -> error "Unary assignments are not supported yet"
  ExprSwitchStmt {} -> error "Expr switch statements are not supported yet"
  TypeSwitchStmt {} -> error "Type switch statements are not supported yet"
  GoStmt {} -> error "go statements are not supported yet"
  ForStmt _ (ForRange {}) _ -> error "For range statements are not supported yet"
  AssignStmt _ _ (ComplexAssign _) _ -> error "Complex assignments are not supported yet"
  SelectStmt {} -> error "Select statements are not supported yet"
  FallthroughStmt {} -> error "Fallthrough statements are not supported yet"
  DeferStmt {} -> error "Defer statements are not supported yet"
  ShortVarDeclStmt {} -> error "Short variable declarations are not supported yet"

withLoopLabels :: Gen.Label s
               -> Gen.Label s
               -> GoGenerator h s ctx ()
               -> GoGenerator h s ctx ()
withLoopLabels breakLabel contLabel gen = do
  pushLabels breakLabel contLabel
  gen
  popLabels

pushLabels :: Gen.Label s -> Gen.Label s -> GoGenerator h s ctx ()
pushLabels breakLabel contLabel =
  St.modify' $ \s ->
    case (enclosingBreaks s, enclosingContinues s) of
      (LabelStack bs, LabelStack cs) ->
        s { enclosingBreaks = LabelStack (breakLabel : bs)
          , enclosingContinues = LabelStack (contLabel : cs)
          }

popLabels :: GoGenerator h s ctx ()
popLabels = do
  St.modify' $ \s ->
    case (enclosingBreaks s, enclosingContinues s) of
      (LabelStack [], _) -> error "popLabels: empty break stack"
      (_, LabelStack []) -> error "popLabels: empty continue stack"
      (LabelStack (_:bs), LabelStack (_:cs)) ->
        s { enclosingBreaks = LabelStack bs
          , enclosingContinues = LabelStack cs
          }

-- | Translate a basic block, saving and restoring the lexical
-- environment around the block
translateBlock :: (Traversable t)
               => t (Statement SourceRange)
               -> CtxRepr ctx
               -> GoGenerator h s ctx ()
translateBlock stmts retCtxRepr = do
  env0 <- St.gets lexenv
  mapM_ (\s -> translateStatement s retCtxRepr) stmts
  St.modify' $ \s -> s { lexenv = env0 }

exprType :: Gen.Expr s typ -> TypeRepr typ
exprType (Gen.App app) = C.appType app
exprType (Gen.AtomExpr atom) = Gen.typeOfAtom atom

fromRight :: Either a b -> b
fromRight (Right x) = x

translateAssignment :: (Expression SourceRange, Expression SourceRange)
                    -> GoGenerator h s rctx ()
translateAssignment (lhs, rhs) =
  withTranslatedExpression rhs $ \rhs' ->
    case lhs of
      Name _ Nothing (Id _ _ ident) -> do
        lenv <- St.gets lexenv
        case HM.lookup ident lenv of
          Nothing -> error ("translateAssignment: Undefined identifier: " ++ show ident)
          Just (GoVarReg typeRep refReg)
            | Just Refl <- testEquality typeRep (exprType rhs') -> do
                regExp <- Gen.readReg refReg
                Gen.writeReference regExp rhs'
            | otherwise -> error ("translateAssignment: type mismatch between lhs and rhs: " ++ show (lhs, rhs))
      _ -> error ("translateAssignment: unsupported LHS: " ++ show lhs)

translateVarSpec :: VarSpec SourceRange -> GoGenerator h s rctx ()
translateVarSpec s = case s of
  -- the rules for matching multiple variables and expressions are the
  -- same as for normal assignment expressions, with the addition of
  -- an empty list of initial values. We don't support multi-valued
  -- right-hand-sides yet.
  TypedVarSpec _ identifiers typ initialValues ->
    translateTypeM (fromRight $ getType typ) $
    \typeRepr zeroVal ->
      if null initialValues then
        -- declare variables with zero values;
        mapM_ (\ident -> declareIdent ident zeroVal typeRepr ) $ NE.toList identifiers
      else if NE.length identifiers /= length initialValues then error "The number of variable declared doesn't match the number of initial values provided. This is either a syntax error or a destructuring assignment. The latter is not supported."
           else void $ zipWithM bindExpr (NE.toList identifiers) initialValues
  UntypedVarSpec _ identifiers initialValues -> error "Untyped variable declarations will be supported in V4"
  where
    bindExpr ident value = do
      withTranslatedExpression value $ \expr ->
        declareIdent ident expr (exprType expr)

-- | Translate a Go expression into a Crucible expression
--
-- This needs to be in 'Generator' because:
--
-- 1) We need access to the 'lexenv' in 'TransState' to look up the
--    Crucible register associated with each reference, and
--
-- 2) We need to be able to dereference all of the references holding
--    values, and 'readReference' is in 'Generator'
withTranslatedExpression :: Expression SourceRange
                         -> (forall typ . Gen.Expr s typ -> GoGenerator h s rctx a)
                         -> GoGenerator h s rctx a
withTranslatedExpression e k = case e of
  IntLit _ i ->
    (translateTypeM (fromRight $ getType e)) $ \typerepr _ ->
    case typerepr of
      (BVRepr repr) -> k (Gen.App (C.BVLit repr i))
      _ -> error ("withTranslatedExpression: impossible literal type: " ++ show e)
  FloatLit _ d -> k (Gen.App (C.RationalLit (realToFrac d)))
  StringLit _ t -> k (Gen.App (C.TextLit t))
  Name _ Nothing (Id _ _ ident) -> do
    lenv <- St.gets lexenv
    case HM.lookup ident lenv of
      Nothing -> error ("withTranslatedExpression: Undefined identifier: " ++ show ident)
      Just (GoVarReg _typeRep refReg) -> do
        regExp <- Gen.readReg refReg
        Gen.readReference regExp >>= k
  UnaryExpr _ op operand -> do
    withTranslatedExpression operand $ \innerExpr ->
      translateUnaryExpression e k op innerExpr
  BinaryExpr _ op e1 e2 -> do
    withTranslatedExpression e1 $ \e1' ->
      withTranslatedExpression e2 $ \e2' ->
        case (exprType e1', exprType e2') of
          (BVRepr w1, BVRepr w2)
            | Just Refl <- testEquality w1 w2
            , Just LeqProof <- isPosNat w1 ->
              case (getType e1, getType e2) of
                (Right (Int _ isSigned1), Right (Int _ isSigned2))
                  | isSigned1 && isSigned2 -> translateBitvectorBinaryOp k op Signed w1 e1' e2'
                  | not isSigned1 && not isSigned2 -> translateBitvectorBinaryOp k op Unsigned w1 e1' e2'
                _ -> error ("withTranslatedExpression: mixed signedness in binary operator: " ++ show (op, e1, e2))
          (RealValRepr, RealValRepr) -> translateFloatingOp e k op e1' e2'
          (BoolRepr, BoolRepr) -> translateBooleanBinaryOp e k op e1' e2'
          _ -> error ("withTranslatedExpression: unsupported operation: " ++ show (op, e1, e2))
  Conversion _ toType baseE ->
    withTranslatedExpression baseE $ \baseE' ->
      case getType toType of
        Right toType' -> translateTypeM toType' $ \typerepr _ ->
          translateConversion k typerepr baseE'
        Left err -> error ("withTranslatedType: Unexpected conversion type: " ++ show (toType, err))
  _ -> error "Unsuported expression type"

translateConversion :: (forall toTyp . Gen.Expr s toTyp -> GoGenerator h s rctx a)
                    -> TypeRepr toTyp
                    -> Gen.Expr s fromTyp
                    -> GoGenerator h s rctx a
translateConversion k toType e =
  case (exprType e, toType) of
    (BoolRepr, BVRepr w) -> k (Gen.App (C.BoolToBV w e))
    -- FIXME: Need sign information if this is integral
    -- (BVRepr w1, ReprAndValue (BVRepr w2) _)
    --   | Just LeqProof <- isPosNat w1
    --   , Just LeqProof <- isPosNat w2
    --   , Just LeqProof <- testLeq (incNat w2) w1 -> k (Gen.App (C.BVSext w1 w2 e))

data SignedOrUnsigned = Signed | Unsigned

isSigned :: SignedOrUnsigned -> Bool
isSigned Signed = True
isSigned Unsigned = False

-- We need to be able to desugar these with short circuiting.
translateBooleanBinaryOp :: Expression SourceRange
                         -> (Gen.Expr s BoolType -> a)
                         -> BinaryOp
                         -> Gen.Expr s BoolType
                         -> Gen.Expr s BoolType
                         -> a
translateBooleanBinaryOp =
  error "Boolean binary operators are not supported"

-- | Translate floating point arithmetic to Crucible
--
-- Note that the translation is to *real* valued arithmetic, as we
-- don't have models of IEEE floats.
translateFloatingOp :: Expression SourceRange
                    -> (forall typ . Gen.Expr s typ -> a)
                    -> BinaryOp
                    -> Gen.Expr s RealValType
                    -> Gen.Expr s RealValType
                    -> a
translateFloatingOp e k op e1 e2 =
  case op of
    Add -> k (Gen.App (C.RealAdd e1 e2))
    Subtract -> k (Gen.App (C.RealSub e1 e2))
    Multiply -> k (Gen.App (C.RealMul e1 e2))
    Equals -> k (Gen.App (C.RealEq e1 e2))
    NotEquals -> k (Gen.App (C.Not (Gen.App (C.RealEq e1 e2))))
    Less -> k (Gen.App (C.RealLt e1 e2))
    LessEq -> k (Gen.App (C.Not (Gen.App (C.RealLt e2 e1))))
    Greater -> k (Gen.App (C.RealLt e2 e1))
    GreaterEq -> k (Gen.App (C.Not (Gen.App (C.RealLt e1 e2))))
    Divide -> error ("translateFloatingOp: Division is not supported: " ++ show e)
    Remainder -> error ("translateFloatingOp: Remainder is not supported: " ++ show e)
    BitwiseAnd -> error ("translateFloatingOp: BitwiseAnd is not supported: " ++ show e)
    BitwiseOr -> error ("translateFloatingOp: BitwiseOr is not supported: " ++ show e)
    BitwiseXOr -> error ("translateFloatingOp: BitwiseXOr is not supported: " ++ show e)
    BitwiseNAnd -> error ("translateFloatingOp: BitwiseNAnd is not supported: " ++ show e)
    LeftShift -> error ("translateFloatingOp: LeftShift is not supported: " ++ show e)
    RightShift -> error ("translateFloatingOp: RightShift is not supported: " ++ show e)
    LogicalAnd -> error ("translateFloatingOp: LogicalAnd is not supported: " ++ show e)
    LogicalOr -> error ("translateFloatingOp: LogicalOr is not supported: " ++ show e)

-- | Translate a binary operation over bitvectors
--
-- This includes translations for ==, /=, <, >, <=, and >= (which also
-- need other implementations for other types)
translateBitvectorBinaryOp :: (1 <= w)
                         => (forall typ . Gen.Expr s typ -> a)
                         -> BinaryOp
                         -> SignedOrUnsigned
                         -> NatRepr w
                         -> Gen.Expr s (BVType w)
                         -> Gen.Expr s (BVType w)
                         -> a
translateBitvectorBinaryOp k op sou w e1 e2 =
  case op of
    Add -> k (Gen.App (C.BVAdd w e1 e2))
    Subtract -> k (Gen.App (C.BVSub w e1 e2))
    Multiply -> k (Gen.App (C.BVMul w e1 e2))
    Divide | isSigned sou -> k (Gen.App (C.BVSdiv w e1 e2))
           | otherwise -> k (Gen.App (C.BVUdiv w e1 e2))
    Remainder | isSigned sou -> k (Gen.App (C.BVSrem w e1 e2))
              | otherwise -> k (Gen.App (C.BVUrem w e1 e2))
    BitwiseAnd -> k (Gen.App (C.BVAnd w e1 e2))
    BitwiseOr -> k (Gen.App (C.BVOr w e1 e2))
    BitwiseXOr -> k (Gen.App (C.BVXor w e1 e2))
    BitwiseNAnd -> k (Gen.App (C.BVNot w (Gen.App (C.BVAnd w e1 e2))))
    LeftShift -> k (Gen.App (C.BVShl w e1 e2))
    RightShift | isSigned sou -> k (Gen.App (C.BVAshr w e1 e2))
               | otherwise -> k (Gen.App (C.BVLshr w e1 e2))
    Equals -> k (Gen.App (C.BVEq w e1 e2))
    NotEquals -> k (Gen.App (C.Not (Gen.App (C.BVEq w e1 e2))))
    LessEq | isSigned sou -> k (Gen.App (C.BVSle w e1 e2))
           | otherwise -> k (Gen.App (C.BVUle w e1 e2))
    Less | isSigned sou -> k (Gen.App (C.BVSlt w e1 e2))
         | otherwise -> k (Gen.App (C.BVUlt w e1 e2))
    GreaterEq | isSigned sou -> k (Gen.App (C.Not (Gen.App (C.BVSlt w e1 e2))))
              | otherwise -> k (Gen.App (C.Not (Gen.App (C.BVUlt w e1 e2))))
    Greater | isSigned sou -> k (Gen.App (C.Not (Gen.App (C.BVSle w e1 e2))))
            | otherwise -> k (Gen.App (C.Not (Gen.App (C.BVUle w e1 e2))))
    LogicalAnd -> error "translateBitvectorBinaryOp: logical and of bitvectors is not supported"
    LogicalOr -> error "translateBitvectorBinaryOp: logical and of bitvectors is not supported"


translateUnaryExpression :: Expression SourceRange
                         -> (Gen.Expr s tp -> GoGenerator h s rctx a)
                         -> UnaryOp
                         -> Gen.Expr s tp
                         -> GoGenerator h s rctx a
translateUnaryExpression e k op innerExpr =
  exprTypeRepr e $ \typerepr zero ->
  case (op, exprType innerExpr, typerepr) of
    (Plus, _, _) -> k innerExpr
    (Minus, BVRepr w, BVRepr w')
      | Just Refl <- testEquality w w'
      , Just LeqProof <- isPosNat w ->
        k (Gen.App (C.BVSub w zero innerExpr))
    (Minus, _, _) -> error ("withTranslatedExpression: invalid argument to unary minus: " ++ show e)
    (Not, BoolRepr, BoolRepr) ->
      k (Gen.App (C.Not innerExpr))
    (Not, _, _) -> error ("withTranslatedExpression: invalid argument to not: " ++ show e)
    (Complement, BVRepr w, BVRepr w')
      | Just Refl <- testEquality w w'
      , Just LeqProof <- isPosNat w ->
        k (Gen.App (C.BVNot w innerExpr))
    (Complement, _, _) -> error ("withTranslatedExpression: invalid argument to complement: " ++ show e)
    (Receive, _, _) -> error "withTranslatedExpression: unary Receive is not supported"
    (Address, _, _) -> error "withTranslatedExpression: addressof is not supported"
    (Deref, _, _) -> error "withTranslatedExpression: deref is not supported"

-- | This is a trivial wrapper around 'getType' and 'toTypeRepr' to
-- fix the Monad instance of 'getType' (inlining this without a type
-- annotation gives an ambiguous type variable error). Note that it
-- can potentially `fail` if the expression cannot be typed
-- (e.g. because of type or lexical mismatch), but, in practice, the
-- parser guarantees that expressions will be well typed.
exprTypeRepr :: Expression SourceRange
             -> (forall typ. TypeRepr typ -> (forall s. Gen.Expr s typ) -> GoGenerator h s rctx a)
               -> GoGenerator h s rctx a
exprTypeRepr e k = case getType e of
  Left err -> fail "err"
  Right typ -> translateTypeM typ k
                   

-- | Declares an identifier; ignores blank identifiers. A thin wrapper
-- around `declareVar` that doesn't return the register
declareIdent :: Id a -> Gen.Expr s tp -> TypeRepr tp -> GoGenerator h s rctx ()
declareIdent ident value typ = case ident of
  BlankId _ -> return ()
  Id _ _ name -> void $ declareVar name value typ

translateConstSpec :: ConstSpec SourceRange -> GoGenerator h s rctx ()
translateConstSpec = undefined

-- | Translate a Go type to a Crucible type. This is where type semantics is encoded.
translateType :: forall a. (?machineWordWidth :: Int) => SemanticType
              -> (forall typ. TypeRepr typ -> (forall s. Gen.Expr s typ) -> a)
              -> a 
translateType typ = typeAsRepr (specializeType ?machineWordWidth typ)

translateTypeM :: forall h s rctx a. SemanticType
               -> (forall typ. TypeRepr typ -> (forall s. Gen.Expr s typ) -> GoGenerator h s rctx a)
               -> GoGenerator h s rctx a
translateTypeM typ f = do w <- getMachineWordWidth
                          let ?machineWordWidth = w in translateType typ f

typeAsRepr :: forall a. SemanticType
           -> (forall typ. TypeRepr typ -> (forall s. Gen.Expr s typ) -> a)
           -> a
typeAsRepr typ lifter = injectType (toTypeRepr typ)
   where injectType :: ReprAndValue -> a
         injectType (ReprAndValue repr zv) = lifter repr zv


-- | Compute the Crucible 'TypeRepr' and zero initializer value for a
-- given Go AST type. Do not use this function on it's own: use
-- `translateType` or `translateTypeM`.
toTypeRepr :: SemanticType -> ReprAndValue
toTypeRepr typ = case typ of
  Int (Just width) _ -> case someNat (fromIntegral width) of
    Just (Some w) | Just LeqProof <- isPosNat w -> ReprAndValue (BVRepr w) (Gen.App (C.BVLit w 0))
    _ -> error $ unwords ["invalid integer width",show width]
  Int Nothing _ -> error $ "Type translation: Unexpected integer type without width: expectin all integers to have width specified explicitly."
  Float _width -> ReprAndValue RealValRepr real0
  Boolean -> ReprAndValue BoolRepr (Gen.App (C.BoolLit False))
  Complex _width -> ReprAndValue ComplexRealRepr (Gen.App (C.Complex real0 real0))
  Iota -> ReprAndValue IntegerRepr undefined
  Nil -> ReprAndValue (MaybeRepr AnyRepr) (Gen.App (C.NothingValue AnyRepr))
  String -> ReprAndValue (VectorRepr $ BVRepr (knownNat :: NatRepr 8)) undefined
  Function _mrecvtyp _paramtyps _mspreadtyp _returntyps -> undefined -- Ctx.Assignment????
  Array _ typ' -> typeAsRepr typ' $ \t _tzv -> ReprAndValue (VectorRepr t) undefined
  Struct _fields -> undefined
  Pointer _typ -> ReprAndValue (ReferenceRepr AnyRepr) undefined
  Interface _sig -> undefined
  Map _keyType _valueType -> undefined
  Slice typ' -> typeAsRepr typ' $ \_t _zv -> ReprAndValue (StructRepr undefined) undefined
  Channel _ typ' -> toTypeRepr typ'
  BuiltIn _name -> undefined -- ^ built-in function
  Alias (TypeName _ _ _) -> undefined
  _ -> error $ "Unmatched pattern for " ++ show typ
  where
    real0 = Gen.App (C.RationalLit (realToFrac (0::Int)))



-- | The 'TypeRepr' and the zero initializer value for a given type
data ReprAndValue = forall typ. ReprAndValue (TypeRepr typ) (forall s. Gen.Expr s typ)
