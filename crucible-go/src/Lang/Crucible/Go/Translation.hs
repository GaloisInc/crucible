{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}

module Lang.Crucible.Go.Translation (mkFnEnv, translateFunction) where

import           Control.Monad.ST (ST)
import           Control.Monad (zipWithM, void)
import           Control.Monad.Fail (MonadFail)
import qualified Control.Monad.State as St

import qualified Data.Foldable as F
import           Data.Maybe (maybeToList)
import           Data.Text as T (Text, empty, pack)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Default.Class
import qualified Data.List.NonEmpty as NE

import           Debug.Trace (trace)

import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx

import           Language.Go.AST
import           Language.Go.Types

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Generator as Gen
import           Lang.Crucible.Go.Types
import           Lang.Crucible.Types
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle

import           What4.FunctionName (functionNameFromText)
import           What4.ProgramLoc
import qualified What4.Utils.StringLiteral as C


-- Given a list of top-level definitions, build a function environment
-- mapping function names to newly allocated function handles along
-- with the corresponding TopLevel data).
mkFnEnv :: forall p sym.
  (?machineWordWidth :: Int)
  => HandleAllocator
  -> [TopLevel SourceRange]
  -> IO (HM.HashMap Text SomeHandle)
mkFnEnv _ [] = return HM.empty
mkFnEnv halloc (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
  env <- mkFnEnv halloc toplevels
  paramTypes params $ \paramsRepr ->
    returnTypes returns $ \retRepr -> do
    h <- mkHandle' halloc (functionNameFromText fnm) paramsRepr (StructRepr retRepr)
    return $ HM.insert fnm (SomeHandle h) env

-- Build crucible type context from parameter list.
paramTypes :: (?machineWordWidth :: Int)
  => ParameterList SourceRange
  -> (forall ctx. CtxRepr ctx -> a) -> a
paramTypes l k = case l of
   NamedParameterList _ ps Nothing -> go ps k
   AnonymousParameterList _ ps Nothing -> go ps k
   _ -> error "paramTypes: unexpected variadic parameter"
  where
    go :: (Typed p, ?machineWordWidth :: Int) => [p] -> (forall ctx. CtxRepr ctx -> a) -> a
    go [] k = k Ctx.empty
    go (p : ps) k =
      go ps $ \ctx ->
      translateType (fromRight $ getType p) $ \trepr -> k $ ctx Ctx.:> trepr

-- Build crucible type context from return list.
returnTypes :: (?machineWordWidth :: Int)
  => ReturnList SourceRange
  -> (forall ctx. CtxRepr ctx -> a) -> a
returnTypes l k = case l of
   NamedReturnList _ rs -> go rs k
   AnonymousReturnList _ rs -> go rs k
  where
    go :: (Typed r, ?machineWordWidth :: Int) => [r] -> (forall ctx. CtxRepr ctx -> a) -> a
    go [] k = k Ctx.empty
    go (r : rs) k =
      go rs $ \ctx ->
      translateType (fromRight $ getType r) $ \trepr -> k $ ctx Ctx.:> trepr

lookupNil :: TypeRepr tp -> [ReprAndValue] -> Maybe (Gen.Expr ext s tp)
lookupNil repr [] = Nothing
lookupNil repr (ReprAndValue repr' val : reprs) =
  case testEquality repr repr' of
    Just Refl -> return val
    Nothing   -> lookupNil repr reprs

-- -- | (Currently) the entry point of the module: translates one go
-- -- function to a Crucible control-flow graph. The parameters after
-- -- the first two are the same as for the `FunctionDecl` AST
-- -- constructor.
translateFunction :: forall ext args ret.
  (C.IsSyntaxExtension ext, ?machineWordWidth :: Int)
  => FnHandle args ret
  -> HashMap Text SomeHandle
  -> Id SourceRange -- ^ Function name
  -> ParameterList SourceRange -- ^ Function parameters
  -> ReturnList SourceRange
  -> [Statement SourceRange]
  -> IO (C.SomeCFG ext args ret)
translateFunction h handleMap (Id _ _bind fname) params returns body =
  bindReturns @ext returns $ \(retctx :: CtxRepr tretctx) setupReturns ->
  bindParams @ext params $ \(ctx :: CtxRepr tctx) setupParams -> do
  Refl <- failIfNotEqual (StructRepr retctx) (handleReturnType h) $
          "translateFunction: checking return type"
  Refl <- failIfNotEqual ctx (handleArgTypes h) $
          "translateFunction: checking argument types"
  sng <- newIONonceGenerator
  (Gen.SomeCFG g, []) <- Gen.defineFunction InternalPos sng h
    (\assignment -> (def,
                      do retslots <- setupReturns
                         St.modify' (\ts -> ts { returnSlots = retslots
                                               , delta = handleMap })
                         setupParams assignment
                         graphGenerator body retctx))
  case toSSA g of
    C.SomeCFG gs -> return $ C.SomeCFG gs


-- | State of translation: the user state part of the Generator monad used here.
data TransState ctx s = TransState
  { lexenv :: !(HashMap Text (GoVarReg s)) -- ^ A mapping from variable names to registers
  , delta :: !(HashMap Text SomeHandle) -- ^ Function environment
  , explicitLabels :: !(HashMap Text (Gen.Label s))
    -- ^ A mapping of explicitly-introduced Go label names to their
    -- corresponding Crucible block labels
  , enclosingBreaks :: !(LabelStack s)
    -- ^ The stack of enclosing break labels
  , enclosingContinues :: !(LabelStack s)
    -- ^ The stack of enclosing continue labels
  , returnSlots :: !(Maybe (VariableAssignment s ctx))
     -- ^ The list of registers that represent the components of the
     -- return value. Crucible functions can only have one return value,
     -- while Go functions can have multiple. To deal with that we
     -- multiplex return values in a struct that would store references
     -- to return values. The struct is going to be created from the
     -- variable assignment in this component of the user state.
     -- TODO: why references?
  , machineWordWidth :: !Int -- ^ size of the machine word
  }

instance Default (TransState ctx s) where
  def = TransState { lexenv = HM.empty
                   , delta = HM.empty
                   , explicitLabels = HM.empty
                   , enclosingBreaks = LabelStack []
                   , enclosingContinues = LabelStack []
                   , returnSlots = Nothing
                   , machineWordWidth = 32
                   }

-- The Go generator monad.
type GoGenerator ext s rctx a = Gen.Generator ext s (TransState rctx) (StructType rctx) IO a


-- | Bind the list of return values to both the function return type
-- in the crucible CFG and, if the return values are named, to
-- crucible registers mapped to the names. Like many functions here,
-- uses, continuation-passing style to construct heterogeneous lists
-- and work with type-level literals.
bindReturns :: (C.IsSyntaxExtension ext, ?machineWordWidth :: Int)
            => ReturnList SourceRange
            -> (forall ctx. CtxRepr ctx ->
                (forall s rctx. GoGenerator ext s rctx (Maybe (VariableAssignment s ctx))) -> a)
            -> a
bindReturns rlist f =
  let goNamed :: (C.IsSyntaxExtension ext) =>
                 [NamedParameter SourceRange]
              -> (forall ctx. CtxRepr ctx ->
                  (forall s rctx. GoGenerator ext s rctx (VariableAssignment s ctx)) -> a)
              -> a
      goNamed [] k = k Ctx.empty (return Ctx.empty)
      goNamed (np@(NamedParameter _ (Id _ _ rname) _):ps) k =
        translateType {- TODO Abstract this: implicit parameter or generator state -}
           (fromRight $ getType np) (\t ->
                    goNamed ps (\ctx gen -> k (ctx Ctx.:> t)
                                 (do assign <- gen
                                     reg <- declareVar rname (zeroValue t) t
                                     return (assign Ctx.:> GoVarOpen reg))
                               ))
      goAnon :: [Type SourceRange] -> (forall ctx. CtxRepr ctx -> a) -> a
      goAnon [] k = k Ctx.empty
      goAnon (t:ts) k = case getType t of
        Right vt -> translateType vt $ \t' ->
          goAnon ts (\ctx -> k (ctx Ctx.:> t'))
        _ -> error "Expecting a semantic type inferred for a return type, but found none"
  in case rlist of
    NamedReturnList _ nrets -> goNamed nrets $ \ctx gen -> f ctx (Just <$> gen)
    AnonymousReturnList _ rtypes -> goAnon rtypes $ \ctx -> f ctx (return Nothing)

-- | Generate the Crucible type context and bind parameter names to
-- (typed) Crucible registers.
bindParams ::
  (C.IsSyntaxExtension ext, ?machineWordWidth :: Int)
  => ParameterList SourceRange
  -> (forall ctx. CtxRepr ctx ->
      (forall s rctx a. Ctx.Assignment (Gen.Atom s) ctx -> GoGenerator ext s rctx ()) -> a)
  -> a
bindParams plist f =
  let go ::  (C.IsSyntaxExtension ext) =>
             [NamedParameter SourceRange]
         -> (forall ctx. CtxRepr ctx
             -> (forall s rctx a. Ctx.Assignment (Gen.Atom s) ctx -> GoGenerator ext s rctx ())
             -> a)
         -> a
      go []     k = k Ctx.empty (\_ -> return ())
      go (np@(NamedParameter _ (Id _ _ pname) _):ps) k =
        translateType
        (fromRight $ getType np) $ \t ->
        go ps (\ctx f' -> k (ctx Ctx.:> t) 
                          (\a -> do f' (Ctx.init a)
                                    void $ declareVar pname (Gen.AtomExpr (Ctx.last a)) t))
  in case plist of
    NamedParameterList _ params mspread -> go (params ++ maybeToList mspread) f
    AnonymousParameterList _ [] Nothing -> go [] f
    AnonymousParameterList _ _ _ -> error "Unexpected anonymous parameter list in a function definition"

getMachineWordWidth :: GoGenerator ext s rctx Int
getMachineWordWidth = St.gets machineWordWidth

setMachineWordWidth :: Int -> GoGenerator ext s rctx ()
setMachineWordWidth w = St.modify' (\ts -> ts {machineWordWidth = w})

-- | Fully specialize a type with the current machine word width
specializeTypeM :: VarType -> GoGenerator ext s rctx VarType
specializeTypeM typ = do w <- getMachineWordWidth
                         return $ specializeType w typ

declareVar :: (C.IsSyntaxExtension ext) =>
              Text -> Gen.Expr ext s tp -> TypeRepr tp ->
              GoGenerator ext s rctx (Gen.Reg s (ReferenceType tp))
declareVar name value t = do ref <- Gen.newReference value
                             reg <- Gen.newReg ref
                             trace ("declareVar") $
                               trace ("name: " ++ show name) $
                               trace ("reg: " ++ show reg) $ do
                               St.modify' (\ts -> ts {lexenv = HM.insert name (GoVarReg t reg) (lexenv ts)})
                               return reg

graphGenerator :: (C.IsSyntaxExtension ext) =>
  [Statement SourceRange] -> CtxRepr rctx -> GoGenerator ext s rctx a --(Gen.Expr s (StructType rctx))
graphGenerator body ctxrepr = do
  -- First, traverse all of the statements of the function to allocate
  -- Crucible labels for each source level label.  We need this to
  -- handle gotos, named breaks, and named continues.
  -- Gen.endNow $ \cont -> do
  --   entry_label <- Gen.newLabel
  --   labelMap <- F.foldlM buildLabelMap HM.empty body
  --   St.modify' $ \s -> s { explicitLabels = labelMap }
  --   Gen.resume_ entry_label cont

  mapM_ (translateStatement ctxrepr) body
  -- The following is going to be a fallthrough block that would
  -- never be reachable if all the exit paths in the function graph
  -- end with a return statement.
  -- TODO: insert missing returns for void functions?
  Gen.reportError $ Gen.App (C.StringLit "Expected a return statement, but found none.")

-- | For each statement defining a label, populate the hash map with a
-- fresh crucible label.
buildLabelMap :: HashMap Text (Gen.Label s)
              -> Statement SourceRange
              -> GoGenerator ext s rctx (HashMap Text (Gen.Label s))
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
translateStatement :: (C.IsSyntaxExtension ext) =>
                      CtxRepr rctx
                   -> Statement SourceRange
                   -> GoGenerator ext s rctx ()
translateStatement retCtxRepr s = case s of
  DeclStmt _ (VarDecl _ varspecs)     -> mapM_ translateVarSpec varspecs
  DeclStmt _ (ConstDecl _ constspecs) -> mapM_ translateConstSpec constspecs
  ShortVarDeclStmt annot ids inits -> translateVarSpec (UntypedVarSpec annot ids inits)
  DeclStmt _ (TypeDecl _ _) ->
    -- type declarations are only reflected in type analysis results
    -- and type translations; they are not executable
    return ()
  ExpressionStmt _ expr -> withTranslatedExpression expr $ \_ _ -> return ()
    -- The number of expressions (|e|) in `lhs` and `rhs` should
    -- either be the same, or |rhs| = 1. Assigning multi-valued
    -- right-hand sides (|rhs|=1 and |lhs| > 1) is not currently
    -- supported.
  AssignStmt _ lhs Assignment rhs
    | F.length lhs == F.length rhs -> mapM_ translateAssignment (NE.zip lhs rhs)
    | otherwise -> error "Mismatched assignment expression lengths"
  ReturnStmt _ [] ->
    case testEquality retCtxRepr Ctx.empty of
      Just Refl -> Gen.returnFromFunction $ Gen.App $ C.MkStruct retCtxRepr Ctx.empty
    -- This doesnt work because retCtxRepr is a CtxRepr, not a TypeRepr
    -- case testEquality retCtxRepr UnitRepr of
    --   Just Refl -> Gen.returnFromFunction $ Gen.App $ C.EmptyApp
      _ -> error $ "translateStatement error: expected null return type, got " ++ show retCtxRepr
  ReturnStmt _ [e] ->
    withTranslatedExpression e $ \_ e' ->
      case e' of
        _ | Just Refl <- testEquality (Ctx.empty Ctx.:> (exprType e')) retCtxRepr ->
            Gen.returnFromFunction $ Gen.App $ C.MkStruct retCtxRepr (Ctx.empty Ctx.:> e')
          | otherwise -> error ("translateStatement error: Incorrect return type: " ++ show e ++ " Expected type: " ++ show retCtxRepr ++ " Actual type: " ++ show (exprType e'))
  ReturnStmt _ _ -> error ("translateStatement: Multiple return values are not yet supported: " ++ show s)
  EmptyStmt _ -> return ()
  LabeledStmt _ (Label _ labelName) stmt -> do
    lbls <- St.gets explicitLabels
    lbl <- case HM.lookup labelName lbls of
      Nothing -> error ("Missing definition of label: " ++ show labelName)
      Just l -> return l
    exit_label <- Gen.newLabel
    Gen.defineBlock lbl $ do
      -- NOTE: I'm not sure if this state modification is valid in
      -- the presence of this continuation... will require testing.
      -- St.modify' $ \st -> st { explicitLabels = HM.insert labelName lbl (explicitLabels st) }
      translateStatement retCtxRepr stmt
      Gen.jump exit_label
    Gen.continue exit_label (Gen.jump lbl)    
  GotoStmt _ (Label _ labelName) -> do
    lbls <- St.gets explicitLabels
    case HM.lookup labelName lbls of
      Nothing -> error ("Jump to undeclared label: " ++ show s)
      Just lbl -> Gen.jump lbl
  BlockStmt _ body -> translateBlock body retCtxRepr
  IfStmt _ mguard e then_ else_ -> do
    F.forM_ mguard $ translateStatement retCtxRepr
    withTranslatedExpression e $ \_ e' -> do
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
    F.forM_ minitializer $ translateStatement retCtxRepr
    cond_lbl <- Gen.newLabel
    loop_lbl <- Gen.newLabel
    exit_lbl <- Gen.newLabel

    Gen.defineBlock cond_lbl $ do
      case mcondition of
        Nothing -> Gen.jump loop_lbl
        Just cond -> do
          withTranslatedExpression cond $ \_ cond' -> do
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
        F.forM_ mincrement $ translateStatement retCtxRepr

      Gen.jump cond_lbl

    Gen.continue exit_lbl (Gen.jump cond_lbl)

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

  UnaryAssignStmt _ e incdec ->
    withTranslatedExpression e $ \mAssignLoc e' -> do
    case mAssignLoc of
      Nothing -> error ("Assignment to unassignable location: " ++ show e)
      Just loc ->
        withIncDecWrapper (exprType e') incdec $ \op -> do
          ref0 <- Gen.readReg loc
          e0 <- Gen.readReference ref0
          Gen.writeReference ref0 (op e0)

  ExprSwitchStmt {} -> error "Expr switch statements are not supported yet"
  TypeSwitchStmt {} -> error "Type switch statements are not supported yet"
  GoStmt {} -> error "go statements are not supported yet"
  ForStmt _ (ForRange {}) _ -> error "For range statements are not supported yet"
  AssignStmt _ _ (ComplexAssign _) _ -> error "Complex assignments are not supported yet"
  SelectStmt {} -> error "Select statements are not supported yet"
  FallthroughStmt {} -> error "Fallthrough statements are not supported yet"
  DeferStmt {} -> error "Defer statements are not supported yet"

-- | Given a type witness, return the correct expression constructor
-- to either add or subtract one from the expression
--
-- Only integral (bitvector) and float (real) types are supported.
withIncDecWrapper :: TypeRepr tp
                  -> IncDec
                  -> ((Gen.Expr ext s tp -> Gen.Expr ext s tp) -> GoGenerator ext s ctx a)
                  -> GoGenerator ext s ctx a
withIncDecWrapper tp incdec k =
  case (tp, incdec) of
    (C.BVRepr w, Inc) -> k (\val -> Gen.App (C.BVAdd w val (Gen.App (C.BVLit w 1))))
    (C.RealValRepr, Inc) -> k (\val -> Gen.App (C.RealAdd val (Gen.App (C.RationalLit 1))))
    (C.BVRepr w, Dec) -> k (\val -> Gen.App (C.BVSub w val (Gen.App (C.BVLit w 1))))
    (C.RealValRepr, Dec) -> k (\val -> Gen.App (C.RealSub val (Gen.App (C.RationalLit 1))))
    _ -> error ("Unsupported increment/decrement base type: " ++ show tp)

withLoopLabels :: Gen.Label s
               -> Gen.Label s
               -> GoGenerator ext s ctx ()
               -> GoGenerator ext s ctx ()
withLoopLabels breakLabel contLabel gen = do
  pushLabels breakLabel contLabel
  gen
  popLabels

pushLabels :: Gen.Label s -> Gen.Label s -> GoGenerator ext s ctx ()
pushLabels breakLabel contLabel =
  St.modify' $ \s ->
    case (enclosingBreaks s, enclosingContinues s) of
      (LabelStack bs, LabelStack cs) ->
        s { enclosingBreaks = LabelStack (breakLabel : bs)
          , enclosingContinues = LabelStack (contLabel : cs)
          }

popLabels :: GoGenerator ext s ctx ()
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
translateBlock :: (C.IsSyntaxExtension ext, Traversable t)
               => t (Statement SourceRange)
               -> CtxRepr ctx
               -> GoGenerator ext s ctx ()
translateBlock stmts retCtxRepr = do
  env0 <- St.gets lexenv
  mapM_ (translateStatement retCtxRepr) stmts
  St.modify' $ \s -> s { lexenv = env0 }

exprType :: (C.IsSyntaxExtension ext) => Gen.Expr ext s typ -> TypeRepr typ
exprType (Gen.App app) = C.appType app
exprType (Gen.AtomExpr atom) = Gen.typeOfAtom atom

fromRight :: Either a b -> b
fromRight (Right x) = x

translateAssignment :: (C.IsSyntaxExtension ext) =>
                       (Expression SourceRange, Expression SourceRange)
                    -> GoGenerator ext s rctx ()
translateAssignment (lhs, rhs) =
  withTranslatedExpression lhs $ \mAssignLoc lhs' -> do
    withTranslatedExpression rhs $ \_ rhs' -> do
      case () of
        _ | Just Refl <- testEquality (exprType lhs') (exprType rhs')
          , Just reg <- mAssignLoc -> do
            ref0 <- Gen.readReg reg
            Gen.writeReference ref0 rhs'
          | otherwise -> error ("translateAssignment: type mismatch between lhs and rhs: " ++ show (lhs, rhs))

translateVarSpec :: (C.IsSyntaxExtension ext) => VarSpec SourceRange -> GoGenerator ext s rctx ()
translateVarSpec s = case s of
  -- the rules for matching multiple variables and expressions are the
  -- same as for normal assignment expressions, with the addition of
  -- an empty list of initial values. We don't support multi-valued
  -- right-hand-sides yet.
  TypedVarSpec _ identifiers typ initialValues ->
    translateTypeM (fromRight $ getType typ) $
    \typeRepr ->
      if null initialValues then
        -- declare variables with zero values;
        mapM_ (\ident -> declareIdent ident (zeroValue typeRepr) typeRepr) $ NE.toList identifiers
      else if NE.length identifiers /= length initialValues then error "The number of variable declared doesn't match the number of initial values provided. This is either a syntax error or a destructuring assignment. The latter is not supported."
           else void $ zipWithM bindExpr (NE.toList identifiers) initialValues
  UntypedVarSpec _ identifiers initialValues
    | F.length identifiers == F.length initialValues ->
      void $ zipWithM bindExpr (F.toList identifiers) (F.toList initialValues)
    | otherwise -> error "Mismatched length untyped variable declarations will be supported in V4"
  where
    bindExpr ident value = do
      withTranslatedExpression value $ \_ expr ->
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
--
-- The continuation is called with the assignable location associated
-- with the expression, if any (e.g., the address of operation returns
-- an expression along with an assignable location, while a simple
-- binary addition only returns an expression).
--
-- We can only update reference locations, so the target of an
-- assignment *must* be an addressable location.  Addressable
-- locations are:
--
-- 1) Named variables
--
-- 2) Field selectors
--
-- 3) Index expressions
--
-- 4) Dereference expressions

withTranslatedExpression :: (C.IsSyntaxExtension ext)
                         => Expression SourceRange
                         -> (forall typ .
                              Maybe (Gen.Reg s (ReferenceType typ)) ->
                              Gen.Expr ext s typ -> GoGenerator ext s rctx a)
                         -> GoGenerator ext s rctx a
withTranslatedExpression e k = case e of
  -- NilLit _ -> k Nothing $ Gen.App $ C.NothingValue
  NilLit _ -> k Nothing undefined
  BoolLit _ b -> k Nothing $ Gen.App $ C.BoolLit b
  IntLit _ i ->
    (translateTypeM (fromRight $ getType e)) $ \typerepr ->
    case typerepr of
      (BVRepr repr) -> k Nothing (Gen.App (C.BVLit repr i))
      _ -> error ("withTranslatedExpression: impossible literal type: " ++ show e)
  FloatLit _ d -> k Nothing (Gen.App (C.RationalLit (realToFrac d)))
  StringLit _ t -> k Nothing (Gen.App (C.StringLit (C.UnicodeLiteral t)))
  Name _ Nothing (Id _ _ ident) -> do
    lenv <- St.gets lexenv
    δ <- St.gets delta
    -- First look up in the lexical environment.
    case HM.lookup ident lenv of
      Nothing ->
        -- If not found in lenv, look up in the function environment δ.
        case HM.lookup ident δ of
          Nothing -> error ("withTranslatedExpression: Undefined identifier: " ++ show ident)
          Just (SomeHandle h) ->
            k Nothing $ Gen.App $
            C.JustValue (FunctionHandleRepr (handleArgTypes h) (handleReturnType h)) $
            Gen.App $ C.HandleLit h
      Just (GoVarReg _typeRep refReg) -> do
        regExp <- Gen.readReg refReg
        Gen.readReference regExp >>= k (Just refReg)
  UnaryExpr _ op operand -> do
    exprTypeRepr e $ \tp ->
      withTranslatedExpression operand $ \mAssignLoc innerExpr -> do
      translateUnaryExpression e tp (zeroValue tp) k op mAssignLoc innerExpr
  BinaryExpr _ op e1 e2 -> do
    withTranslatedExpression e1 $ \_ e1' ->
      withTranslatedExpression e2 $ \_ e2' ->
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
    withTranslatedExpression baseE $ \_ baseE' ->
      case getType toType of
        Right toType' -> translateTypeM toType' $ \typerepr ->
          translateConversion k typerepr baseE'
        Left err -> error ("withTranslatedExpression: Unexpected conversion type: " ++ show (toType, err))
        
  CallExpr _ f _t args Nothing ->
    withTranslatedExpression f $ \_ f' ->
    withTranslatedExpressions args $ \ctxRepr assignment -> do
    case Gen.exprType f' of
      MaybeRepr (FunctionHandleRepr argsRepr _retRepr)
        | Just Refl <- testEquality argsRepr ctxRepr ->
          case f' of
            Gen.App (C.JustValue _repr f'') -> Gen.call f'' assignment >>= k Nothing
            Gen.App (C.NothingValue _repr) ->
              error "withTranslatedExpression: attempt to call nil function"
            _ -> do
              f'' <- Gen.fromJustExpr f' $ Gen.App $ C.StringLit $ C.UnicodeLiteral $
                               T.pack $ "attempt to call nil function in function "
                               ++ show f' ++ " translated from " ++ show f
              Gen.call f'' assignment >>= k Nothing
      MaybeRepr (FunctionHandleRepr argsRepr _) ->
        error $ "withTranslatedExpression: function argument type mismatch. expected "
        ++ show argsRepr ++ ", got " ++ show ctxRepr
      _ -> error $ "withTranslatedExpression: expected optional function type, got "
           ++ show (Gen.exprType f')
           
  CallExpr rng _ _ _ (Just vararg) ->
    error $ "withTranslatedExpression: unexpected variadic argument at " ++ show rng
  _ -> error "Unsupported expression type"

withTranslatedExpressions :: (C.IsSyntaxExtension ext)
                          => [Expression SourceRange]
                          -> (forall args. CtxRepr args ->
                              Ctx.Assignment (Gen.Expr ext s) args -> GoGenerator ext s rctx a)
                          -> GoGenerator ext s rctx a
withTranslatedExpressions [] k = k Ctx.empty Ctx.empty
withTranslatedExpressions (e : es) k =
  withTranslatedExpressions es $ \ctxRepr assignment ->
  withTranslatedExpression e $ \_ e' ->
  k (ctxRepr Ctx.:> Gen.exprType e') (assignment Ctx.:> e')


translateConversion :: (C.IsSyntaxExtension ext) =>
                       (Maybe (Gen.Reg s (ReferenceType toTyp)) -> Gen.Expr ext s toTyp -> GoGenerator ext s rctx a)
                    -> TypeRepr toTyp
                    -> Gen.Expr ext s fromTyp
                    -> GoGenerator ext s rctx a
translateConversion k toType e =
  case (exprType e, toType) of
    (BoolRepr, BVRepr w) -> k Nothing (Gen.App (C.BoolToBV w e))
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
                         -> (Maybe (Gen.Reg s (ReferenceType BoolType)) -> Gen.Expr ext s BoolType -> a)
                         -> BinaryOp
                         -> Gen.Expr ext s BoolType
                         -> Gen.Expr ext s BoolType
                         -> a
translateBooleanBinaryOp =
  error "Boolean binary operators are not supported"

-- | Translate floating point arithmetic to Crucible
--
-- Note that the translation is to *real* valued arithmetic, as we
-- don't have models of IEEE floats.
translateFloatingOp :: Expression SourceRange
                    -> (forall typ . Maybe (Gen.Reg s (ReferenceType typ)) -> Gen.Expr ext s typ -> a)
                    -> BinaryOp
                    -> Gen.Expr ext s RealValType
                    -> Gen.Expr ext s RealValType
                    -> a
translateFloatingOp e k op e1 e2 =
  case op of
    Add -> k Nothing (Gen.App (C.RealAdd e1 e2))
    Subtract -> k Nothing (Gen.App (C.RealSub e1 e2))
    Multiply -> k Nothing (Gen.App (C.RealMul e1 e2))
    Equals -> k Nothing (Gen.App (C.RealEq e1 e2))
    NotEquals -> k Nothing (Gen.App (C.Not (Gen.App (C.RealEq e1 e2))))
    Less -> k Nothing (Gen.App (C.RealLt e1 e2))
    LessEq -> k Nothing (Gen.App (C.Not (Gen.App (C.RealLt e2 e1))))
    Greater -> k Nothing (Gen.App (C.RealLt e2 e1))
    GreaterEq -> k Nothing (Gen.App (C.Not (Gen.App (C.RealLt e1 e2))))
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
translateBitvectorBinaryOp :: (C.IsSyntaxExtension ext, 1 <= w)
                         => (forall typ . Maybe (Gen.Reg s (ReferenceType typ)) -> Gen.Expr ext s typ -> a)
                         -> BinaryOp
                         -> SignedOrUnsigned
                         -> NatRepr w
                         -> Gen.Expr ext s (BVType w)
                         -> Gen.Expr ext s (BVType w)
                         -> a
translateBitvectorBinaryOp k op sou w e1 e2 =
  case op of
    Add -> k Nothing (Gen.App (C.BVAdd w e1 e2))
    Subtract -> k Nothing (Gen.App (C.BVSub w e1 e2))
    Multiply -> k Nothing (Gen.App (C.BVMul w e1 e2))
    Divide | isSigned sou -> k Nothing (Gen.App (C.BVSdiv w e1 e2))
           | otherwise -> k Nothing (Gen.App (C.BVUdiv w e1 e2))
    Remainder | isSigned sou -> k Nothing (Gen.App (C.BVSrem w e1 e2))
              | otherwise -> k Nothing (Gen.App (C.BVUrem w e1 e2))
    BitwiseAnd -> k Nothing (Gen.App (C.BVAnd w e1 e2))
    BitwiseOr -> k Nothing (Gen.App (C.BVOr w e1 e2))
    BitwiseXOr -> k Nothing (Gen.App (C.BVXor w e1 e2))
    BitwiseNAnd -> k Nothing (Gen.App (C.BVNot w (Gen.App (C.BVAnd w e1 e2))))
    LeftShift -> k Nothing (Gen.App (C.BVShl w e1 e2))
    RightShift | isSigned sou -> k Nothing (Gen.App (C.BVAshr w e1 e2))
               | otherwise -> k Nothing (Gen.App (C.BVLshr w e1 e2))
    Equals -> k Nothing (Gen.App (C.BVEq w e1 e2))
    NotEquals -> k Nothing (Gen.App (C.Not (Gen.App (C.BVEq w e1 e2))))
    LessEq | isSigned sou -> k Nothing (Gen.App (C.BVSle w e1 e2))
           | otherwise -> k Nothing (Gen.App (C.BVUle w e1 e2))
    Less | isSigned sou -> k Nothing (Gen.App (C.BVSlt w e1 e2))
         | otherwise -> k Nothing (Gen.App (C.BVUlt w e1 e2))
    GreaterEq | isSigned sou -> k Nothing (Gen.App (C.Not (Gen.App (C.BVSlt w e1 e2))))
              | otherwise -> k Nothing (Gen.App (C.Not (Gen.App (C.BVUlt w e1 e2))))
    Greater | isSigned sou -> k Nothing (Gen.App (C.Not (Gen.App (C.BVSle w e1 e2))))
            | otherwise -> k Nothing (Gen.App (C.Not (Gen.App (C.BVUle w e1 e2))))
    LogicalAnd -> error "translateBitvectorBinaryOp: logical and of bitvectors is not supported"
    LogicalOr -> error "translateBitvectorBinaryOp: logical and of bitvectors is not supported"


translateUnaryExpression :: (C.IsSyntaxExtension ext) =>
                            Expression SourceRange
                         -- ^ The original expression
                         -> TypeRepr tp'
                         -- ^ The typerepr of the result
                         -> Gen.Expr ext s tp'
                         -- ^ The zero value for the result type
                         -> (Maybe (Gen.Reg s (ReferenceType tp')) -> Gen.Expr ext s tp' -> GoGenerator ext s rctx a)
                         -- ^ The continuation to call
                         -> UnaryOp
                         -- ^ The operator applied by this unary expression
                         -> Maybe (Gen.Reg s (ReferenceType tp))
                         -- ^ The original inner expression
                         -> Gen.Expr ext s tp
                         -- ^ The translated inner expression
                         -> GoGenerator ext s rctx a
translateUnaryExpression e resRepr zero k op mAssignLoc innerExpr =
  case (op, exprType innerExpr, resRepr) of
    (Plus, innerTp, _)
      | Just Refl <- testEquality innerTp resRepr -> k Nothing innerExpr
      | otherwise -> error ("translateUnaryExpression: mismatch in return type of addition: " ++ show e)
    (Minus, BVRepr w, BVRepr w')
      | Just Refl <- testEquality w w'
      , Just LeqProof <- isPosNat w ->
        k Nothing (Gen.App (C.BVSub w zero innerExpr))
    (Minus, _, _) -> error ("withTranslatedExpression: invalid argument to unary minus: " ++ show e)
    (Not, BoolRepr, BoolRepr) ->
      k Nothing (Gen.App (C.Not innerExpr))
    (Not, _, _) -> error ("withTranslatedExpression: invalid argument to not: " ++ show e)
    (Complement, BVRepr w, BVRepr w')
      | Just Refl <- testEquality w w'
      , Just LeqProof <- isPosNat w ->
        k Nothing (Gen.App (C.BVNot w innerExpr))
    (Address, innerTypeRepr, _)
      | Just Refl <- testEquality resRepr (ReferenceRepr innerTypeRepr)
      , Just loc <- mAssignLoc ->
        Gen.readReg loc >>= k Nothing
      | Nothing <- mAssignLoc -> error ("Address taken of non-assignable location: " ++ show e)
      | otherwise -> error ("Type mismatch while translating address of operation: " ++ show e)
    (Complement, _, _) -> error ("withTranslatedExpression: invalid argument to complement: " ++ show e)
    (Receive, _, _) -> error "withTranslatedExpression: unary Receive is not supported"
    (Deref, _, _) -> error "withTranslatedExpression: deref is not supported"

-- | This is a trivial wrapper around 'getType' and 'toTypeRepr' to
-- fix the Monad instance of 'getType' (inlining this without a type
-- annotation gives an ambiguous type variable error). Note that it
-- can potentially `fail` if the expression cannot be typed
-- (e.g. because of type or lexical mismatch), but, in practice, the
-- parser guarantees that expressions will be well typed.
exprTypeRepr :: Expression SourceRange
             -> (forall typ. TypeRepr typ -> GoGenerator ext s rctx a)
               -> GoGenerator ext s rctx a
exprTypeRepr e k = case getType e of
  Left err -> fail (show err)
  Right typ -> translateTypeM typ k

-- | Declares an identifier; ignores blank identifiers. A thin wrapper
-- around `declareVar` that doesn't return the register
declareIdent :: (C.IsSyntaxExtension ext) => Id a -> Gen.Expr ext s tp -> TypeRepr tp -> GoGenerator ext s rctx ()
declareIdent ident value typ = case ident of
  BlankId _ -> return ()
  Id _ _ name -> void $ declareVar name value typ

translateConstSpec :: ConstSpec SourceRange -> GoGenerator ext s rctx ()
translateConstSpec = undefined

-- | Translate a Go type to a Crucible type. This is where type semantics is encoded.
translateType :: forall ext a. (?machineWordWidth :: Int) => VarType
              -> (forall typ. TypeRepr typ -> a)
              -> a 
translateType typ = typeAsRepr (specializeType ?machineWordWidth typ)

translateTypeM :: forall ext s rctx a. VarType
               -> (forall typ. TypeRepr typ -> GoGenerator ext s rctx a)
               -> GoGenerator ext s rctx a
translateTypeM typ f = do w <- getMachineWordWidth
                          let ?machineWordWidth = w in translateType typ f

typeAsRepr :: forall ext a. VarType
           -> (forall typ. TypeRepr typ -> a)
           -> a
typeAsRepr typ lifter = injectType (toTypeRepr typ)
   where injectType :: SomeRepr -> a
         injectType (SomeRepr repr) = lifter repr

toTypeRepr :: VarType -> SomeRepr
toTypeRepr typ = case typ of
  Int (Just width) _ -> case someNat (fromIntegral width) of
    Just (Some w) | Just LeqProof <- isPosNat w -> SomeRepr (BVRepr w)
    _ -> error $ unwords ["invalid integer width",show width]
  Int Nothing _ -> error $ "Type translation: Unexpected integer type without width: expectin all integers to have width specified explicitly."
  Float _width -> SomeRepr RealValRepr
  Boolean -> SomeRepr BoolRepr
  Complex _width -> SomeRepr ComplexRealRepr
  Iota -> SomeRepr IntegerRepr
  Nil -> SomeRepr (MaybeRepr AnyRepr)
  -- String -> SomeRepr (VectorRepr $ BVRepr (knownNat :: NatRepr 8))
  String -> SomeRepr (StringRepr UnicodeRepr)
  Function _mrecv_ty param_tys Nothing ret_tys ->
    someReprCtx (toTypeRepr <$> param_tys) $ \paramsRepr ->
    someReprCtx (toTypeRepr <$> ret_tys) $ \retCtxRepr ->
    SomeRepr (MaybeRepr $ FunctionHandleRepr paramsRepr $ StructRepr retCtxRepr)
  Function _ _ (Just _) _ -> error "toTypeRepr: unexpected variadic parameter to function"
  -- TODO: use array length somehow?
  Array _len typ' -> typeAsRepr typ' $ \t -> SomeRepr (VectorRepr t)
  Struct _fields -> undefined
  Pointer _typ -> SomeRepr (MaybeRepr (ReferenceRepr AnyRepr))
  Interface _sig -> SomeRepr (MaybeRepr undefined)
  Map _keyType _valueType -> SomeRepr (MaybeRepr undefined)
  Slice typ' -> typeAsRepr typ' $ \_t -> SomeRepr (MaybeRepr (StructRepr undefined))
  Channel _ typ' -> toTypeRepr typ'
  BuiltIn _name -> undefined -- ^ built-in function
  Alias (TypeName _ _ _) -> undefined
  _ -> error $ "Unmatched pattern for " ++ show typ
  where
    real0 = Gen.App (C.RationalLit (realToFrac (0::Int)))

zeroValue :: TypeRepr a -> Gen.Expr ext s a
zeroValue ty = case ty of
  BVRepr w -> Gen.App $ C.BVLit w 0
  RealValRepr -> real0
  BoolRepr -> Gen.App $ C.BoolLit False
  ComplexRealRepr -> Gen.App $ C.Complex real0 real0
  StringRepr UnicodeRepr -> Gen.App $ C.StringLit $ C.UnicodeLiteral $ T.empty
  StringRepr repr ->
    error $ "zeroValue: unsupported string format. expected unicode, got " ++ show repr
  -- TODO: shouldn't have to differentiate between strings and arrays
  -- I guess.. Actually, the zero value of an array depends on its
  -- declared size which isn't part of its type information. So we may
  -- have to treat arrays as a special case to generate the correct
  -- initialization code. Oh wait, maybe it is part of the type..
  
  -- TODO: arrays should have length in their type?
  VectorRepr (BVRepr n) -> undefined
  MaybeRepr repr -> Gen.App $ C.NothingValue repr
  ReferenceRepr AnyRepr -> undefined
  _ -> error $ "zeroValue: no zero value for type " ++ show ty
  where
    real0 = Gen.App $ C.RationalLit $ realToFrac (0::Int)

someReprCtx :: [SomeRepr] -> (forall ctx. CtxRepr ctx -> a) -> a
someReprCtx [] k = k $ Ctx.empty
someReprCtx (SomeRepr repr : rs) k =
 someReprCtx rs $ \ctxRepr -> k $ ctxRepr Ctx.:> repr

failIfNotEqual :: forall k f m a (b :: k).
                  (MonadFail m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise = fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2
