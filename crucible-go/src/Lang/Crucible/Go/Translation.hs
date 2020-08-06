{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Go.Translation (translate) where

import           Control.Monad.Except
import           Control.Monad.Fail (MonadFail)
import           Control.Monad.Identity
import           Control.Monad.State

import           Data.Default.Class
import           Data.Functor.Product
import           Data.HashMap.Strict as HM hiding (foldl)
import           Data.Maybe (fromJust, fromMaybe, maybeToList)
import           Data.Text as T hiding (foldl, length, zip)
import qualified Data.Vector as V

import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC

import           Debug.Trace (trace)

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Generator as Gen
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Syntax

import           What4.FunctionName (functionNameFromText)
import           What4.ProgramLoc
import           What4.Utils.StringLiteral

import           Language.Go.AST
import           Language.Go.Rec
import           Language.Go.Types

import           Lang.Crucible.Go.Types

-- TODO: float constants may appear as int literals, and they are
-- presented as rationals when they are actually float
-- literals. Allowing coercion from bitvector to float solved the
-- first part, and I guess we can just parse the floats as rationals
-- and then convert to float... who knows if that will be actually
-- correct.

-- | Entry point.
translate :: Show a
          => PosNat -- ^ machine word width
          -> Node a tp -- ^ AST to translate
          -> IO (Either String (Translated tp))
translate w = evalTranslateM (def { machineWordWidth = w }) . translateM

translateM :: Show a => Node a tp -> TranslateM tp
translateM = para translate_alg

evalTranslateM :: TransState -> TranslateM a -> IO (Either String (Translated a))
evalTranslateM st (TranslateM m) = runExceptT $ evalStateT m st

translate_alg :: Show a
              => NodeF a (Product (Node a) TranslateM) tp
              -> TranslateM tp

translate_alg (MainNode nm (Pair main_node (TranslateM mainM)) imports) =
  -- trace ("number of imports: " ++ show (length imports)) $
  TranslateM $ do
  sng <- liftIO' newIONonceGenerator
  halloc <- liftIO' newHandleAllocator
  modify $ \ts -> ts { sng = Just sng, halloc = Just halloc }

  -- First translate the imports in the order in which they appear.
  imports' <- forM imports $ \(Pair import_node (TranslateM importM)) -> do
    -- Build namespace for the package and add it to the state.
    let name = packageName import_node
    -- modify $ \ts -> ts { retRepr = Some UnitRepr }
    ns <- mkPackageNamespace import_node
    modify $ \ts -> ts { pkgName = name
                       , namespaces = HM.insert name ns (namespaces ts) }
    -- Translate the package.
    -- trace ("translating package " ++ show name) $
      -- trace ("ns: " ++ show ns) $
    importM

  -- Build local namespace for the file.
  ns <- mkPackageNamespace main_node
  modify $ \ts -> ts { pkgName = nm
                     , namespaces = HM.insert nm ns (namespaces ts) }

  -- Translate the main package.
  main' <- mainM

  -- Build initializer CFG.
  ini <- mkInitializer $ main' : imports'

  -- Get stuff from the state.
  globs <- gets globals
  funs <- gets functions
  mainFun <- gets mainFunction

  -- Produce the final result.
  return $ TranslatedMain main' imports' ini mainFun globs funs halloc

translate_alg (PackageNode name path import_paths file_paths files inits) =
  -- trace ("translating package " ++ show name) $
  TranslateM $ do
  files' <- mapM runTranslated files
  modify $ \ts -> ts { retRepr = Some UnitRepr }
  inits' <- mapM runTranslated inits
  return $ TranslatedPackage name path import_paths file_paths files' $
    -- Build a single initializer generator action from all of the
    -- initializer statements.
    SomeGoGenerator UnitRepr $ forM_ inits' $ runTranslatedStmt UnitRepr

translate_alg (FileNode path name decls imports) =
  TranslateM $ TranslatedFile path name <$>
  mapM runTranslated decls <*> mapM runTranslated imports

-- TODO: maybe a bug here when there's a single ident on the LHS of a
-- short declaration. It should introduce a new variable shadowing the
-- old one (possibly with a different type).  Actually it may be a
-- more general problem related to nested scopes.. It's not that
-- locals always shadow globals, but that the current scope takes
-- priority over all outer scopes. So we could change gamma to be a
-- stack of scopes and have some notion of "inner-most lookup" vs
-- recursive lookup, or maybe we should just introduce new variables
-- always and live with the occasional inefficiency.
translate_alg (AssignStmt _ assign_tp op lhs rhs) =
  TranslateM $ do
  lhs' <- mapM runTranslated lhs
  rhs_gens <- mapM runTranslated rhs
  Some retRepr <- gets retRepr
  ts <- get
  return $ TranslatedStmt $ SomeGoGenerator retRepr $ do
    rhs' <- mapM (runTranslatedExpr retRepr) rhs_gens
    case assign_tp of
      Assign -> do
        lhs'' <- mapM (runTranslatedExpr retRepr) lhs'
        forM_ (zip lhs'' rhs') $ \(Some (GoExpr (Just loc) l), r) ->
                                  writeToLoc (exprType l) loc r
      -- Here I think we could indiscriminately introduce new
      -- variables for each name on the LHS (shadowing any existing
      -- variables with the same name) and the result would be
      -- correct, but it's more efficient to reuse existing locations.
      Define ->
        forM_ (zip3 (proj1 <$> lhs) lhs' rhs') $
        \(In (IdentExpr _x _tp qual name), l, r) ->
          case l of
            -- If bound, write to the existing location.
            TranslatedExpr gen -> do
              -- trace ("asdf") $ do
              Some (GoExpr (Just loc) l) <- runSomeGoGenerator retRepr gen
              writeToLoc (exprType l) loc r
            -- If unbound, declare new variable
            TranslatedUnbound _qual (Ident _k nm) -> do
              Some (GoExpr _loc r') <- return r
              declareVar nm r'
      AssignOperator ->
        fail "translate_alg AssignStmt: expected AssignOperator to be desugared"

translate_alg (BlockStmt _ block) =
  TranslateM $ do
  TranslatedBlock gen <- runTranslated block
  return $ TranslatedStmt gen

translate_alg (BranchStmt _ branch_tp label) =
  TranslateM $ fail "translate_alg BranchStmt: unsupported"

-- const, type, or var declaration (similar to assign)
translate_alg (DeclStmt _ decl) = TranslateM $ do
  TranslatedGenDecl specs <- runTranslated decl
  Some retRepr <- gets retRepr
  return $ TranslatedStmt $ SomeGoGenerator retRepr $ forM_ specs $ runSpec retRepr

translate_alg (DeferStmt _ call_expr) =
  TranslateM $ fail "translate_alg DeferStmt: unsupported"

translate_alg (EmptyStmt _) = TranslateM $ do
  Some retRepr <- gets retRepr
  return $ TranslatedStmt $ SomeGoGenerator retRepr $ return ()

translate_alg (ExprStmt _ expr) = TranslateM $ do
  TranslatedExpr somegen <- runTranslated expr
  Some retRepr <- gets retRepr
  return $ TranslatedStmt $ SomeGoGenerator retRepr $
    runSomeGoGenerator retRepr somegen >> return ()

-- TODO
translate_alg (ForStmt _ ini cond pos body) =
  TranslateM $ fail "translate_alg ForStmt: unsupported"

translate_alg (GoStmt _ call_expr) =
  TranslateM $ fail "translate_alg GoStmt: unsupported"

translate_alg (IfStmt _ ini cond body els) = TranslateM $ do
  ini_gen <- mapM runTranslated ini
  TranslatedExpr cond_gen <- runTranslated cond
  body_gen <- runTranslated body
  els_gen <- mapM runTranslated els
  Some retRepr <- gets retRepr
  return $ TranslatedStmt $ SomeGoGenerator retRepr $ do
    forM_ ini_gen $ runTranslatedStmt retRepr
    Some (GoExpr _loc cond') <- runSomeGoGenerator retRepr cond_gen
    asType' BoolRepr cond' $ \cond'' ->
      Gen.ifte_ cond'' (runTranslatedBlock retRepr body_gen) $ case els_gen of
      Nothing -> return ()
      Just (TranslatedStmt gen) -> runSomeGoGenerator retRepr gen

translate_alg (IncDecStmt _ expr is_incr) = TranslateM $
  fail "translate_alg IncDecStmt: should have been desugared to an assignment"

translate_alg (LabeledStmt _ label stmt) =
  TranslateM $ fail "translate_alg LabeledStmt: unsupported"
translate_alg (RangeStmt _ key value range body is_assign) =
  TranslateM $ fail "translate_alg RangeStmt: unsupported"

translate_alg (ReturnStmt _ exprs) = TranslateM $ do
  Some retRepr <- gets retRepr
  case exprs of
    [expr] -> do
      TranslatedExpr expr_gen <- runTranslated expr
      return $ TranslatedStmt $ SomeGoGenerator retRepr $ do
        Some (GoExpr _loc e) <- runSomeGoGenerator retRepr expr_gen
        asType' retRepr e Gen.returnFromFunction
    _ ->
      fail $ "translate_alg ReturnStmt: expected a single return value, got "
      ++ show (proj1 <$> exprs)

translate_alg (SelectStmt _ body) =
  TranslateM $ fail "translate_alg SelectStmt: unsupported"
translate_alg (SendStmt _ chan value) =
  TranslateM $ fail "translate_alg SendStmt: unsupported"
translate_alg (SwitchStmt _ ini tag body) =
  TranslateM $ fail "translate_alg SwitchStmt: unsupported"
translate_alg (TypeSwitchStmt _ ini assign body) =
  TranslateM $ fail "translate_alg TypeSwitchStmt: unsupported"
translate_alg (CaseClauseStmt _ cases body) =
  TranslateM $ fail "translate_alg CaseClauseStmt: unsupported"
translate_alg (CommClauseStmt _ send_or_recv body) =
  TranslateM $ fail "translate_alg CommClauseStmt: unsupported"

-- All constants/variables should already be declared.
translate_alg (InitializerStmt vars values) = TranslateM $
  trace ("initializing: " ++ show (proj1 <$> vars) ++ ", " ++ show (proj1 <$> values)) $
  do
  vars' <- mapM runTranslated vars
  values' <- mapM runTranslated values
  return $ TranslatedStmt $ SomeGoGenerator UnitRepr $
    forM_ (zip vars' values') $ \(var, value) -> do
      Some (GoExpr (Just loc) var') <- runTranslatedExpr UnitRepr var
      value' <- runTranslatedExpr UnitRepr value
      trace ("value: " ++ show value') $
        writeToLoc (exprType var') loc value'

-- | The default type of an untyped constant is bool, rune, int,
-- float64, complex128 or string respectively, depending on whether it
-- is a boolean, rune, integer, floating-point, complex, or string
-- constant. -- GO LANGUAGE SPEC
translate_alg (BasicLitExpr _ tp
               (BasicLit { basiclit_type = lit_ty
                         , basiclit_value = lit_value })) = TranslateM $ do
  Some retRepr <- gets retRepr
  PosNat w LeqProof <- gets machineWordWidth
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ case lit_ty of
    LiteralBool ->
      return $ Some $ GoExpr Nothing $ Gen.App $ C.BoolLit $ readBool lit_value
    LiteralInt -> return $ Some $ GoExpr Nothing $ Gen.App $
                  C.BVLit w $ read $ T.unpack lit_value
    LiteralFloat -> return $ Some $ GoExpr Nothing $ Gen.App $
                    C.DoubleLit $ read $ T.unpack lit_value
    LiteralComplex -> fail "translate_alg: complex literals not yet supported"
    LiteralImag -> fail "translate_alg: imaginary literals not yet supported"
    LiteralChar -> case fromJust $ intToPosNat 8 of
      PosNat w8 LeqProof ->
        return $ Some $ GoExpr Nothing $ Gen.App $ C.BVLit w8 $
                 -- This is probably wrong (need to parse the character code correctly)
                 read $ T.unpack lit_value
    LiteralString ->
      return $ Some $ GoExpr Nothing $ Gen.App $
      C.StringLit $ UnicodeLiteral lit_value

translate_alg (BasicConstExpr _x tp c) = TranslateM $ do
  Some retRepr <- gets retRepr
  w <- gets machineWordWidth
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ case mkBasicConst w c of
    Some e -> return $ Some $ GoExpr Nothing $ e

-- | Coerce "untyped" operands to the type of the other side.
translate_alg (BinaryExpr _ tp
               (Pair left_node (TranslateM leftM)) op
               (Pair right_node (TranslateM rightM))) = TranslateM $ do
  (TranslatedExpr left_gen, TranslatedExpr right_gen) <- pairM leftM rightM
  let (left_ty, right_ty) = (typeOf' left_node, typeOf' right_node)
  Some retRepr <- gets retRepr
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
    (left, right) <- pairM (runSomeGoGenerator retRepr left_gen)
                     (runSomeGoGenerator retRepr right_gen)
    case op of
      x | x `elem` [BPlus, BMinus, BMult, BDiv, BMod,
                    BAnd, BOr, BXor, BAndNot, BLAnd, BLOr] -> do
            (tp', Some (PairIx left' right')) <-
              unify_exprs left_ty right_ty left right
            Some . GoExpr Nothing <$> translateHomoBinop tp' op left' right'
      x | x `elem` [BEq, BLt, BGt, BNeq, BLeq, BGeq] -> do
            (tp', Some (PairIx left' right')) <-
              unify_exprs left_ty right_ty left right
            Some . GoExpr Nothing <$> translateComparison tp' op left' right'
      BShiftL -> fail "translate_alg BinaryExpr: BShiftL not yet supported"
      BShiftR -> fail "translate_alg BinaryExpr: BShiftR not yet supported"

translate_alg (CallExpr _ tp fun args) = TranslateM $ do
  Some retRepr <- gets retRepr
  translated_fun <- runTranslated fun
  translated_args <- mapM runTranslated args
  case translated_fun of
    TranslatedExpr fun_gen ->
      return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
        Some (GoExpr _loc fun') <- runSomeGoGenerator retRepr fun_gen
        args' <- mapM (runSomeGoGenerator retRepr . unTranslatedExpr) translated_args
        withAssignment args' $ \ctxRepr assignment ->
          case exprType fun' of
            MaybeRepr (FunctionHandleRepr argsRepr _retRepr) ->
              case fun' of
                Gen.App (C.JustValue _repr f) -> Some . GoExpr Nothing <$>
                  Gen.call f (coerceAssignment argsRepr assignment)
                Gen.App (C.NothingValue _repr) ->
                  fail "translate_alg CallExpr: attempt to call nil function"
                _ -> do
                  f <- Gen.fromJustExpr fun' $ Gen.App $ C.StringLit $
                    UnicodeLiteral $ T.pack $
                    "attempt to call nil function in function "
                    ++ show fun' ++ " translated from " ++ show (proj1 fun)
                  Some . GoExpr Nothing <$>
                    Gen.call f (coerceAssignment argsRepr assignment)
            _ -> fail $ "translate_alg CallExpr: expected function type, got "
                 ++ show (exprType fun')
    TranslatedUnbound qual ident ->
      translateBuiltin qual ident translated_args

translate_alg (CastExpr _ tp expr ty) =
  TranslateM $ fail "translate_alg CastExpr: unsupported"

-- TODO
translate_alg (CompositeLitExpr _ tp ty elements) =
  TranslateM $ fail "translate_alg CompositeLitExpr: unsupported"

-- | A translated IdentExpr is either:
-- 1) a GoExpr containing the location of the variable as well as its
-- value.
-- 2) a TranslatedUnbound value to indicate lookup failure.
-- Lookup failure isn't necessarily an error; there are a few places
-- where we might expect it to happen:
-- 1) the function appearing in a call expression is the name of a builtin.
-- 2) a variable on the LHS of an assign statement doesn't already exist.
translate_alg (IdentExpr _ tp qual ident@(Ident _kind name)) = TranslateM $ do
  Some retRepr <- gets retRepr
  case qual of
    -- No qualifier means local variable.
    Nothing ->
      return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
      gamma <- gets gamma
      case HM.lookup name gamma of
        Just (Some gr@(GoReg _repr reg)) -> do
          ref <- Gen.readReg reg
          e <- Gen.readRef ref
          return $ Some $ GoExpr (Just $ GoLocRef ref) e
        Nothing ->
          fail $ "translate_alg IdentExpr: unbound local " ++ show name
    Just q -> lookupGlobal q ident

-- TODO: should we split this into two forms for types and expressions?
translate_alg (EllipsisExpr _ tp ty) =
  TranslateM $ fail "translate_alg EllipsisExpr: unsupported"

translate_alg (FuncLitExpr _ tp params results body) =  
  TranslateM $ do
  Some retRepr <- gets retRepr
  -- body' <- runTranslated body
  C.AnyCFG g <- mkFunction Nothing Nothing params Nothing results (Just $ proj2 body)
  return $ TranslatedExpr $ SomeGoGenerator retRepr $
    return $ Some $ GoExpr Nothing $ Gen.App $ C.HandleLit $ C.cfgHandle g
  
-- TODO: I guess this probably will need to branch on the type. Only
-- support array/slice indexing for now?
translate_alg (IndexExpr _ tp expr index) =
  TranslateM $ fail "translate_alg IndexExpr: unsupported"
translate_alg (KeyValueExpr _ tp key value) =
  TranslateM $ fail "translate_alg KeyValueExpr: unsupported"

translate_alg (ParenExpr _ _tp (Pair _ expr)) = expr

translate_alg (SelectorExpr _ tp expr field) =
  TranslateM $ fail "translate_alg SelectorExpr: unsupported"

translate_alg (SliceExpr _ tp expr begin end cap is_3) = TranslateM $ do
  TranslatedExpr arr_gen <- runTranslated expr
  begin_gen <- mapM runTranslated begin
  end_gen <- mapM runTranslated end
  cap_gen <- mapM runTranslated cap
  Some retRepr <- gets retRepr
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
    Some (GoExpr arr_loc arr) <- runSomeGoGenerator retRepr arr_gen
    begin' <- mapM (runTranslatedExpr retRepr >=> goExprToNat) begin_gen
    end' <- mapM (runTranslatedExpr retRepr >=> goExprToNat) end_gen
    cap' <- mapM (runTranslatedExpr retRepr >=> goExprToNat) cap_gen
    -- If the array has a corresponding assignable location, use
    -- that. Otherwise, allocate a new reference cell for it.
    arr_ref <- case arr_loc of
      Just (GoLocRef ref) -> return ref
      Nothing -> Gen.newRef arr
    case exprType arr_ref of
      ReferenceRepr (VectorRepr _repr) -> do
        Some . GoExpr Nothing <$> sliceValue arr_ref begin' end' cap'
      repr ->
        fail $ "translate_alg SliceExpr: expected vector type, got " ++ show repr

-- Dereference a pointer. Still need to return the reference itself
-- for the assignable location in order to supprt *x = y syntax.
translate_alg (StarExpr _ tp operand) =
  TranslateM $ fail "translate_alg StarExpr: unsupported"

translate_alg (TypeAssertExpr _ tp expr asserted_ty) =
  TranslateM $ fail "translate_alg TypeAssertExpr: unsupported"

translate_alg (UnaryExpr _ tp op e) = TranslateM $ do
  Some retRepr <- gets retRepr
  TranslatedExpr e_gen <- runTranslated e
  let e_tp = typeOf' $ proj1 e
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
    Some (GoExpr loc e') <- runSomeGoGenerator retRepr e_gen
    case op of
      -- Not sure about this.
      UPlus -> case exprType e' of
        BVRepr w -> do
          zero <- zeroValue' e_tp $ BVRepr w
          return $ Some $ GoExpr Nothing $ Gen.App $ C.BVAdd w zero e'
        FloatRepr fi -> do
          zero <- zeroValue' e_tp $ FloatRepr fi
          return $ Some $ GoExpr Nothing $ Gen.App $ C.FloatAdd fi C.RNE zero e'
        ty ->
          fail $ "translate_alg UnaryExpr UPlus: unsupported type " ++ show ty
      UMinus -> case exprType e' of
        BVRepr w -> do
          zero <- zeroValue' e_tp $ BVRepr w
          return $ Some $ GoExpr Nothing $ Gen.App $ C.BVSub w zero e'
        FloatRepr fi -> return $ Some $ GoExpr Nothing $ Gen.App $ C.FloatNeg fi e'
        ty ->
          fail $ "translate_alg UnaryExpr UMinus: unsupported type " ++ show ty
      UNot -> case exprType e' of
        BoolRepr -> return $ Some $ GoExpr Nothing $ Gen.App $ C.Not e'
        ty ->
          fail $ "translate_alg UnaryExpr UNot: unsupported type " ++ show ty
      UBitwiseNot -> case exprType e' of
        BoolRepr -> return $ Some $ GoExpr Nothing $ Gen.App $ C.Not e'
        BVRepr w -> return $ Some $ GoExpr Nothing $ Gen.App $ C.BVNot w e'
      UStar -> fail "translate_alg UnaryExpr UStar: not yet supported"
      UAddress -> case loc of
        Just (GoLocRef ref) -> return $ Some $ GoExpr Nothing ref
        Nothing -> fail "translate_alg UnaryExpr UAddress: no location"
      UArrow -> fail "translate_alg UnaryExpr UArrow: not yet supported"

-- Hopefully this is sufficient (need to check if 'tp' emitted by
-- goblin is the actual type denoted by the name).
translate_alg (NamedTypeExpr _ tp (Ident _kind _name)) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (PointerTypeExpr _ tp _e) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (ArrayTypeExpr _ tp _len _elt) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (FuncTypeExpr _ tp _params _variadic _results) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (InterfaceTypeExpr _ tp _methods _is_incomplete) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (MapTypeExpr _ tp _key _value) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (StructTypeExpr _ tp _fields) =
  TranslateM $ TranslatedType <$> translateType tp
translate_alg (ChanTypeExpr _ tp _dir _ty) =
  TranslateM $ TranslatedType <$> translateType tp

translate_alg (TupleExpr _ tp es) = TranslateM $ do
  Some retRepr <- gets retRepr
  es_gen <- mapM runTranslated es
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
    es' <- mapM (\(TranslatedExpr gen) -> runSomeGoGenerator retRepr gen) es_gen
    withAssignment es' $ \ctxRepr assignment ->
      return $ Some $ GoExpr Nothing $ Gen.App $ C.MkStruct ctxRepr assignment

translate_alg (ProjExpr _ tp tuple i) = TranslateM $ do
  Some retRepr <- gets retRepr
  TranslatedExpr tuple_gen <- runTranslated tuple
  return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
    Some (GoExpr _loc tuple') <- runSomeGoGenerator retRepr tuple_gen
    case exprType tuple' of
      StructRepr ctxRepr ->
        withIndex ctxRepr i $ \ix repr ->
        return $ Some $ GoExpr Nothing $ Gen.App $ C.GetStruct tuple' ix repr
      repr ->
        fail $ "translate_alg ProjExpr: expected struct type, got" ++ show repr

-- -- | Generate the CFG for a function.
-- translate_alg (FuncDecl _ recv name params variadic results body) =
--   TranslateM $ TranslatedFuncDecl name <$>
--   mkFunction recv (Just name) params variadic results body

-- | Generate the CFG for a function.
translate_alg (FuncDecl _ recv name params variadic results body) =
  trace (show $ proj1 <$> body) $
  TranslateM $
  TranslatedFuncDecl name <$>
  mkFunction recv (Just name) params variadic results (proj2 <$> body)

translate_alg (GenDecl _ specs) =
  TranslateM $ TranslatedGenDecl <$> mapM runTranslated specs

translate_alg (TypeAliasDecl _ binds) =
  TranslateM $ return $ TranslatedGenDecl [] -- TODO: nothing?

translate_alg (Binding ident expr) =
  TranslateM $ TranslatedBinding ident <$> runTranslated expr

translate_alg (ImportSpec _ pkg_name path) =
  TranslateM $ return TranslatedImportSpec

translate_alg (ConstSpec _ names ty values) = TranslateM $
  TranslatedVarSpec names <$> mapM runTranslated ty <*> mapM runTranslated values
translate_alg (VarSpec _ names ty values) = TranslateM $
  TranslatedVarSpec names <$> mapM runTranslated ty <*> mapM runTranslated values

translate_alg (TypeSpec _ name ty) = TranslateM $ return TranslatedTypeSpec

translate_alg (FieldNode names ty _tag) = TranslateM $ do
  ty' <- runTranslated ty
  TranslatedField names <$> typeOfTranslatedExpr ty'

translate_alg (BlockNode stmts) = TranslateM $ do
  translated_stmts <- mapM runTranslated stmts
  Some retRepr <- gets retRepr
  return $ TranslatedBlock $ SomeGoGenerator retRepr $ do
    -- Save and restore the lexical environment around the block.
    gamma <- gets gamma
    -- seq_stmts retRepr translated_stmts
    forM_ translated_stmts $ runTranslatedStmt retRepr
    modify $ \s -> s { gamma = gamma }


-- -- | Chain a list of translated statements (each containing a
-- -- generator action polymorphic in 's') into a single generator
-- -- action. Checks that the return types match.
-- seq_stmts :: forall s ret.
--              TypeRepr ret
--           -> [Translated Stmt]
--           -> GoGenerator s ret ()
-- seq_stmts _ [] = return ()
-- seq_stmts retRepr (TranslatedStmt somegen : stmts) =
--   -- case somegen @s of
--   --   SomeGoGenerator retRepr' gen ->
--   --     case testEquality retRepr retRepr' of
--   --       Just Refl -> gen >> seq_stmts retRepr stmts
--   --       _ -> error ""
--   runSomeGo
--     case somegen of
--     SomeGoGenerator retRepr' gen ->
--       runSomeGoGenerator 
--         Just Refl -> gen >> seq_stmts retRepr stmts
--         _ -> error ""


----------------------------------------------------------------------
-- Translating types

-- TODO: maybe generalize to MonadFail and use implicit parameter for
-- machineWordWidth.
translateType :: Type -> TranslateM' (Some TypeRepr)
translateType NoType = return $ Some UnitRepr
translateType (ArrayType _len tp) = do
  Some repr <- translateType tp
  return $ Some $ ReferenceRepr $ VectorRepr repr
translateType (BasicType bkind) = case bkind of
  BasicInvalid -> fail "translateType: invalid type"
  BasicBool -> return $ Some BoolRepr
  BasicInt n -> do
    PosNat w LeqProof <- case n of
      Just w' -> return $ fromJust $ intToPosNat w'
      Nothing -> gets machineWordWidth
    return $ Some $ BVRepr w
  BasicUInt n -> do
    PosNat w LeqProof <- case n of
      Just w' -> return $ fromJust $ intToPosNat w'
      Nothing -> gets machineWordWidth
    return $ Some $ BVRepr w
  -- Not sure how to deal with uintptr. It's intended to be a type
  -- that can contain any pointer. Maybe an AnyType reference?
  BasicUIntptr -> fail "translateType: uintptr not supported"
  BasicFloat 32 -> return $ Some $ FloatRepr SingleFloatRepr
  BasicFloat 64 -> return $ Some $ FloatRepr DoubleFloatRepr
  BasicComplex 64 -> return $ Some $ StructRepr $
    Ctx.empty :> FloatRepr SingleFloatRepr :> FloatRepr SingleFloatRepr
  BasicComplex 128 -> return $ Some $ StructRepr $
    Ctx.empty :> FloatRepr DoubleFloatRepr :> FloatRepr DoubleFloatRepr
  BasicString -> return $ Some $ StringRepr UnicodeRepr
  BasicUnsafePointer -> fail "translateType: unsafe pointers not supported"
  BasicUntyped ukind -> case ukind of
    UntypedBool -> return $ Some BoolRepr
    UntypedInt -> do
      PosNat w LeqProof <- gets machineWordWidth
      return $ Some $ BVRepr w
    UntypedRune -> do
      PosNat w LeqProof <- return $ fromJust $ intToPosNat 8
      return $ Some $ BVRepr w
    UntypedFloat -> return $ Some $ FloatRepr SingleFloatRepr
    UntypedComplex -> return $ Some $ StructRepr $
      Ctx.empty :> FloatRepr SingleFloatRepr :> FloatRepr SingleFloatRepr
    UntypedString -> return $ Some $ StringRepr UnicodeRepr
    UntypedNil -> return $ Some UnitRepr
translateType (ChanType dir tp) = fail "translateType: ChanType not supported"
translateType (InterfaceType method) =
  fail "translateType: InterfaceType not supported"
translateType (MapType key value) = fail "translateType: MapType not supported"
translateType (NamedType tp) = trace ("NamedType: " ++ show tp) $ translateType tp
translateType (PointerType tp) = do
  Some repr <- translateType tp
  return $ Some $ MaybeRepr $ ReferenceRepr repr
translateType (FuncType recv params result variadic) = do
  Some params' <- someCtxRepr <$>
    mapM translateType ((snd <$> maybeToList recv) ++ params)
  Some result' <- translateType result
  return $ Some $ MaybeRepr $ FunctionHandleRepr params' result'
translateType (SliceType tp) = do
  Some repr <- translateType tp
  return $ Some $ MaybeRepr $ StructRepr $
    Empty :> ReferenceRepr (VectorRepr repr) :> NatRepr :> NatRepr :> NatRepr
translateType (StructType fields) = do
  Some ctxRepr <- someCtxRepr <$> mapM (translateType . typeOfNameType) fields
  return $ Some $ StructRepr ctxRepr
-- translateType (TupleType []) = return $ Some UnitRepr
translateType (TupleType elts) = translateType (StructType elts)

someCtxRepr :: [Some TypeRepr] -> Some CtxRepr
someCtxRepr [] = Some Ctx.empty
someCtxRepr (Some repr : reprs) = case someCtxRepr reprs of
  Some ctxRepr -> Some $ ctxRepr :> repr

typeOfTranslatedExpr :: MonadFail m => Translated Expr -> m (Some TypeRepr)
typeOfTranslatedExpr (TranslatedType repr) = return repr
typeOfTranslatedExpr (TranslatedExpr _gen) =
  fail "typeOfTranslatedExpr: expected TranslatedType, got TranslatedExpr"


----------------------------------------------------------------------
-- Helper functions

runTranslated :: forall f s a. Product f TranslateM a -> TranslateM' (Translated a)
runTranslated = runTranslateM . proj2

failIfNotEqual :: forall k f m a (b :: k).
                  (MonadFail m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise =
    fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2

runSomeGoGenerator :: TypeRepr ret -> SomeGoGenerator s a -> GoGenerator s ret a
runSomeGoGenerator retRepr (SomeGoGenerator repr gen) = do
  Refl <- failIfNotEqual retRepr repr
          "runSomeGoGenerator: checking return type"
  gen

runTranslatedStmt :: TypeRepr ret -> Translated Stmt -> GoGenerator s ret ()
runTranslatedStmt repr (TranslatedStmt gen) = runSomeGoGenerator repr gen

runTranslatedBlock :: TypeRepr ret -> Translated Block -> GoGenerator s ret ()
runTranslatedBlock repr (TranslatedBlock gen) = runSomeGoGenerator repr gen

unTranslatedExpr :: Translated Expr -> (forall s. SomeGoGenerator s (SomeGoExpr s))
unTranslatedExpr (TranslatedExpr gen) = gen

runTranslatedExpr :: TypeRepr ret -> Translated Expr
                  -> GoGenerator s ret (SomeGoExpr s)
runTranslatedExpr repr (TranslatedExpr gen) = runSomeGoGenerator repr gen

-- | Use this function to assert that an expression has a certain
-- type. Unit values may be coerced to Nothing values of a Maybe
-- type. Bit vector literals may be resized. Floats may be cast
-- (usually from float literals being double by default but allowed to
-- implicitly cast to single precision).
asTypeMaybe :: TypeRepr b -> Gen.Expr Go s a -> Maybe (Gen.Expr Go s b)
asTypeMaybe repr e =
  case testEquality (exprType e) repr of
    Just Refl -> Just e
    Nothing ->
      -- When the types are not equal, try to coerce the value.
      case (e, exprType e, repr) of
        -- Send unit to Nothing.
        (Gen.App C.EmptyApp, _repr, MaybeRepr repr') ->
          Just $ Gen.App $ C.NothingValue repr'
        -- Resize bitvector literals.
        (Gen.App (C.BVLit n i), _repr, BVRepr m) ->
          Just $ Gen.App $ C.BVLit m i
        -- Coerce floats (usually double to float 
        (_e, FloatRepr _fi, FloatRepr fi) ->
          Just $ Gen.App $ C.FloatCast fi C.RNE e
        _ -> Nothing

asType :: TypeRepr b -> Gen.Expr Go s a -> Gen.Expr Go s b
asType repr e =
  case asTypeMaybe repr e of
    Just e' -> e'
    Nothing -> error $ "asType fail: expression " ++ show e ++ " of type "
               ++ show (exprType e) ++ " incompatible with type " ++ show repr

-- | CPS version of asType
asType' :: TypeRepr b -> Gen.Expr Go s a -> (Gen.Expr Go s b -> c) -> c
asType' repr e k = k $ asType repr e

-- | asTypeMaybe lifted to assignments.
asTypesMaybe :: CtxRepr ctx' ->
                Assignment (Gen.Expr Go s) ctx ->
                Maybe (Assignment (Gen.Expr Go s) ctx')
asTypesMaybe Empty Empty = Just Empty
asTypesMaybe (reprs :> repr) (es :> e) =
  pure (:>) <*> asTypesMaybe reprs es <*> asTypeMaybe repr e
asTypesMaybe ctx assignment = Nothing

asTypes :: CtxRepr ctx' ->
           Assignment (Gen.Expr Go s) ctx ->
           Assignment (Gen.Expr Go s) ctx'
asTypes ctx assignment = case asTypesMaybe ctx assignment of
  Just assignment' -> assignment'
  Nothing ->
    error $ "asTypes: " ++ show assignment ++ " incompatible with " ++ show ctx

-- | CPS version of asTypes
asTypes' :: CtxRepr ctx' ->
            Assignment (Gen.Expr Go s) ctx ->
            (Assignment (Gen.Expr Go s) ctx' -> a) -> a
asTypes' ctxRepr assignment k = k $ asTypes ctxRepr assignment

coerceAssignment :: CtxRepr expectedCtx ->
                    Assignment (Gen.Expr Go s) ctx ->
                    Assignment (Gen.Expr Go s) expectedCtx
coerceAssignment expectedCtx assignment =
  case asTypesMaybe expectedCtx assignment of
    Just assignment' -> assignment'
    Nothing -> error $ "coerceAssignment: assignment " ++ show assignment ++
               " incompatible with ctx " ++ show expectedCtx

withAssignment :: [SomeGoExpr s]
               -> (forall args. CtxRepr args ->
                   Assignment (Gen.Expr Go s) args -> a)
               -> a
withAssignment [] k = k Empty Empty
withAssignment (Some (GoExpr _loc e) : es) k =
  withAssignment es $ \ctx assignment ->
  k (ctx :> exprType e) (assignment :> e)

unify_exprs :: MonadFail m => Type -> Type -> SomeGoExpr s -> SomeGoExpr s
            -> m (Type, SomeExprPair s)
unify_exprs t1 t2 (Some (GoExpr _loc1 e1)) (Some (GoExpr _loc2 e2)) =
  case (t1, t2) of
    (BasicType (BasicUntyped _ukind), _) ->
      return (t2, Some $ PairIx (asType (exprType e2) e1) e2)
    (_, BasicType (BasicUntyped _ukind)) ->
      return (t1, Some $ PairIx e1 $ asType (exprType e1) e2)
    _ ->
      if t1 == t2 then
        return (t1, Some $ PairIx e1 $ asType (exprType e1) e2)
      else
        fail $ "unify_types: incompatible types: " ++ show t1 ++ ", " ++ show t2

-- | Translate binops for which the argument types and return type are
-- all the same.
translateHomoBinop :: Type -> BinaryOp -> Gen.Expr Go s a -> Gen.Expr Go s a
                   -> GoGenerator s ret (Gen.Expr Go s a)
translateHomoBinop tp op left right = case op of
  BPlus -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVAdd w left right
    -- | Rounding uses IEEE 754 round-to-even rules but with an IEEE
    -- negative zero further simplified to an unsigned zero. -- SPEC
    FloatRepr fi -> return $ Gen.App $ C.FloatAdd fi C.RNE left right
    StringRepr si -> return $ Gen.App $ C.StringConcat si left right
    ty -> fail $ "translateHomoBinop BPlus: unsupported type " ++ show ty
  BMinus -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVSub w left right
    FloatRepr fi -> return $ Gen.App $ C.FloatSub fi C.RNE left right
    ty -> fail $ "translateHomoBinop BMinus: unsupported type " ++ show ty
  BMult -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVMul w left right
    FloatRepr fi -> return $ Gen.App $ C.FloatMul fi C.RNE left right
    ty -> fail $ "translateHomoBinop BMult: unsupported type " ++ show ty
  BDiv -> case exprType left of
    BVRepr w -> case tp of
      BasicType (BasicInt _w) -> return $ Gen.App $ C.BVSdiv w left right
      BasicType (BasicUInt _w) -> return $ Gen.App $ C.BVUdiv w left right
      _ -> fail $ "translateHomoBinop BDiv: unexpected type " ++ show tp
    FloatRepr fi -> return $ Gen.App $ C.FloatDiv fi C.RNE left right
    ty -> fail $ "translateHomoBinop BDiv: unsupported type " ++ show ty
  BAnd -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVAnd w left right
    BoolRepr -> return $ Gen.App $ C.And left right
    ty -> fail $ "translateHomoBinop BAnd: unsupported type " ++ show ty
  BOr -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVOr w left right
    BoolRepr -> return $ Gen.App $ C.Or left right
    ty -> fail $ "translateHomoBinop BOr: unsupported type " ++ show ty
  BXor -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVXor w left right
    BoolRepr -> return $ Gen.App $ C.BoolXor left right
    ty -> fail $ "translateHomoBinop BXor: unsupported type " ++ show ty
  BAndNot -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVAnd w left (Gen.App $ C.BVNot w right)
    BoolRepr -> return $ Gen.App $ C.And left (Gen.App $ C.Not right)
    ty -> fail $ "translateHomoBinop BAndNot: unsupported type " ++ show ty
  -- Short-circuit evaluation for logical AND and OR
  BLAnd -> case exprType left of
    BoolRepr -> Gen.ifte left (return right) $ return $ Gen.App $ C.BoolLit False
    ty -> fail $ "translateHomoBinop BLAnd: unsupported type " ++ show ty
  BLOr -> case exprType left of
    BoolRepr -> Gen.ifte left (return $ Gen.App $ C.BoolLit True) $ return right
    ty -> fail $ "translateHomoBinop BLOr: unsupported type " ++ show ty
  _ -> fail $ "translateHomoBinop: unexpected binop " ++ show op

-- | Translate comparison binops (argument types are the same and
-- result type is bool).
translateComparison :: Type -> BinaryOp -> Gen.Expr Go s a -> Gen.Expr Go s a
                    -> GoGenerator s ret (Gen.Expr Go s BoolType)
translateComparison tp op left right = Gen.App <$> case op of
  BEq -> case exprType left of
    BoolRepr -> return $ C.BoolEq left right
    BVRepr w -> return $ C.BVEq w left right
    FloatRepr _fi -> return $ C.FloatEq left right
    -- TODO: support other types given by the spec
    ty -> fail $ "translateComparison BEq: unsupported type " ++ show ty
  BLt -> case exprType left of
    BVRepr w -> return $ C.BVSlt w left right
    FloatRepr _fi -> return $ C.FloatLt left right
    ty -> fail $ "translateComparison BLt: unsupported type " ++ show ty
  BGt -> case exprType left of
    BVRepr w -> return $ C.Not $ Gen.App $ C.BVSle w left right
    FloatRepr _fi -> return $ C.FloatGt left right
    ty -> fail $ "translateComparison BGt: unsupported type " ++ show ty
  -- We could desugar neq before translation to avoid duplication here.
  BNeq -> case exprType left of
    BoolRepr -> return $ C.Not $ Gen.App $ C.BoolEq left right
    BVRepr w -> return $ C.Not $ Gen.App $ C.BVEq w left right
    FloatRepr _fi -> return $ C.Not $ Gen.App $ C.FloatEq left right
    -- TODO: support other types given by the spec
    ty -> fail $ "translateComparison BNeq: unsupported type " ++ show ty
  BLeq -> case exprType left of
    BVRepr w -> return $ C.BVSle w left right
    FloatRepr _fi -> return $ C.FloatLe left right
    ty -> fail $ "translateComparison BLeq: unsupported type " ++ show ty
  BGeq -> case exprType left of
    BVRepr w -> return $ C.Not $ Gen.App $ C.BVSlt w left right
    FloatRepr _fi -> return $ C.FloatGe left right
    ty -> fail $ "translateComparison BGeq: unsupported type " ++ show ty
  _ -> fail $ "translateComparison: unexpected binop " ++ show op

-- | Set up parameter and return variables for function declarations.
bindFields :: [Translated Field]
           -> (forall ctx. CtxRepr ctx ->
               (forall s ret. Assignment (Gen.Expr Go s) ctx ->
                GoGenerator s ret ()) -> a)
           -> a
bindFields [] k = k Ctx.empty $ const $ return ()
bindFields (TranslatedField [] (Some repr) : fields) k =
  bindFields fields $ \ctxRepr f ->
  k (ctxRepr :> repr) $ \(assignment :> _x) -> f assignment
bindFields (TranslatedField [Ident _kind name] (Some repr) : fields) k =
  bindFields fields $ \ctxRepr f ->
  k (ctxRepr :> repr) $ \(assignment :> x) ->
  -- Declare variable and initialize with value x.
  declareVar name x >> f assignment  
bindFields (TranslatedField names _repr : _fields) k =
  k Ctx.empty $ const $ fail $
  "bindFields: unexpected multiple names " ++ show names

-- | Declare variable with initial value.
declareVar :: Text -> Gen.Expr Go s tp -> GoGenerator s ret ()
declareVar name e = do
  ref <- Gen.newReference e
  reg <- Gen.newReg ref
  modify (\ts -> ts { gamma = HM.insert name
                      (Some $ GoReg (exprType e) reg) (gamma ts) })

writeToLoc :: TypeRepr tp -> GoLoc s tp -> SomeGoExpr s -> GoGenerator s ret ()
writeToLoc repr loc (Some (GoExpr _loc e)) = case loc of
  GoLocRef ref ->
    trace ("writing " ++ show e ++ " to reference " ++ show ref) $
    asType' repr e $ \e' -> Gen.writeRef ref e'
  GoLocGlobal glob ->
    trace ("writing " ++ show e ++ " to global " ++ show glob) $
    trace ("global type: " ++ show (Gen.globalType glob)) $
    asType' repr e $ \e' -> Gen.writeGlobal glob e'
  GoLocArray arr index -> fail "writeToLoc: arrays not yet supported"

bindResult :: [Translated Field]
           -> (forall r. TypeRepr r ->
               (forall s ret. Gen.Expr Go s r -> GoGenerator s ret ()) -> a)
           -> a
bindResult fields k = bindFields fields $ \ctxRepr f -> 
  case ctxRepr of
    Empty :> repr -> k repr $ \x -> f $ Ctx.empty :> x
    _ -> k (StructRepr ctxRepr) $ \x -> case x of
      Gen.App (C.MkStruct _repr assignment) -> f assignment
      _ -> fail "bindReturn: expected MkStruct constructor"

-- zeroValue :: MonadFail m => Type -> TypeRepr a -> m (Gen.Expr Go s a)
-- zeroValue tp repr = Gen.App <$> case repr of
--   UnitRepr -> return C.EmptyApp
--   BoolRepr -> return $ C.BoolLit False
--   BVRepr w -> return $ C.BVLit w 0
--   FloatRepr SingleFloatRepr -> return $ C.FloatLit 0.0
--   FloatRepr DoubleFloatRepr -> return $ C.DoubleLit 0.0
--   StringRepr UnicodeRepr -> return $ C.StringLit ""
--   MaybeRepr repr -> return $ C.NothingValue repr
--   StructRepr ctx ->
--     let tps = case tp of
--           StructType ts -> ts
--           TupleType ts -> ts in
--       C.MkStruct ctx <$> traverseWithIndex
--       (\ix x -> zeroValue (typeOfNameType $ tps !! indexVal ix) x) ctx
--   VectorRepr repr ->
--     let (tp', len) = case tp of
--           ArrayType n t -> (t, n)
--           SliceType t -> (t, 0) in
--       C.VectorLit repr . V.replicate len <$> zeroValue tp' repr
--   _ -> fail $ "zeroValue: unsupported type " ++ show repr

zeroValue :: Type -> TypeRepr a -> Maybe (Gen.Expr Go s a)
zeroValue tp repr = Gen.App <$> case repr of
  UnitRepr -> return C.EmptyApp
  BoolRepr -> return $ C.BoolLit False
  BVRepr w -> return $ C.BVLit w 0
  FloatRepr SingleFloatRepr -> return $ C.FloatLit 0.0
  FloatRepr DoubleFloatRepr -> return $ C.DoubleLit 0.0
  StringRepr UnicodeRepr -> return $ C.StringLit ""
  MaybeRepr repr -> return $ C.NothingValue repr
  StructRepr ctx ->
    let tps = case tp of
          StructType ts -> ts
          TupleType ts -> ts in
      C.MkStruct ctx <$> traverseWithIndex
      (\ix x -> zeroValue (typeOfNameType $ tps !! indexVal ix) x) ctx
  VectorRepr repr ->
    let (tp', len) = case tp of
          ArrayType n t -> (t, n)
          SliceType t -> (t, 0) in
      C.VectorLit repr . V.replicate len <$> zeroValue tp' repr
  _ -> Nothing

zeroValue' :: MonadFail m => Type -> TypeRepr a -> m (Gen.Expr Go s a)
zeroValue' tp repr =
  maybe (fail $ "zeroValue': no zero value for type " ++ show tp
         ++ " with repr " ++ show repr) return $ zeroValue tp repr

zeroValue'' :: Type -> TranslateM' AnyGoExpr
zeroValue'' tp = do
  Some repr <- translateType tp
  trace ("tp: " ++ show tp) $
    trace ("repr: " ++ show repr) $
    -- trace ("zero: " ++ show (zeroValue' @m @s tp repr)) $
    return $ AnyGoExpr $ Some $ GoExpr Nothing $ maybe (error "asdf") id $ zeroValue' tp repr
  -- AnyGoExpr <$> (Some . GoExpr Nothing <$> zeroValue' tp repr)

-- -- | Try to look up a global identifier, returning a TranslatedExpr if
-- -- successful. Otherwise return a TranslatedUnbound to signal that the
-- -- lookup failed.
-- lookupGlobal :: Ident -> Ident -> TranslateM' (Translated Expr)
-- lookupGlobal qual@(Ident _k pkgName) name@(Ident _k' nm) =
--   -- trace ("lookupGlobal: " ++ show qual ++ ", " ++ show name) $
--   do
--   Some retRepr <- gets retRepr
--   namespaces <- gets namespaces
--   -- trace ("namespaces: " ++ show namespaces) $
--   trace ("looking up: " ++ show qual ++ ", " ++ show name) $
--     trace ("ns: " ++ show (HM.lookup pkgName namespaces)) $ do
--     Namespace globals <- return $ fromJust $ HM.lookup pkgName namespaces
--     -- Try lookup in globals
--     case HM.lookup nm globals of
--       Just (AnyGoExpr e) ->
--         return $ TranslatedExpr $ SomeGoGenerator retRepr $ return e
--       Nothing ->
--         return $ TranslatedUnbound qual name

-- | Try to look up a global identifier, returning a TranslatedExpr if
-- successful. Otherwise return a TranslatedUnbound to signal that the
-- lookup failed.
lookupGlobal :: Ident -> Ident -> TranslateM' (Translated Expr)
lookupGlobal qual@(Ident _k pkgName) name@(Ident _k' nm) =
  do
  Some retRepr <- gets retRepr
  namespaces <- gets namespaces
  -- trace ("looking up: " ++ show qual ++ ", " ++ show name) $
  --   trace ("ns: " ++ show (HM.lookup pkgName namespaces)) $ do
  Namespace globals funcs <- maybe (fail "asdf") return $ HM.lookup pkgName namespaces
  -- Try lookup in globals
  case HM.lookup nm globals of
    Just (GoGlobal glob _zv) ->
      return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
      e <- Gen.readGlobal glob
      return $ Some $ GoExpr (Just $ GoLocGlobal glob) $ e
    Nothing ->
      -- Try lookup in funcs
      case HM.lookup nm funcs of
        Just (SomeHandle h) ->
          return $ TranslatedExpr $ SomeGoGenerator retRepr $
          return $ Some $ GoExpr Nothing $ Gen.App $
          C.JustValue (handleType h) $ Gen.App $ C.HandleLit h
        Nothing ->
          return $ TranslatedUnbound qual name

mkPackageNamespace :: Node a Package -> TranslateM' Namespace
mkPackageNamespace (In (PackageNode _name _path _imports _file_paths files _inits)) = do
  file_namespaces <- mapM mkFileNamespace files
  foldM (\x y -> return $ namespace_union x y) def file_namespaces

-- | Fold over the toplevel declarations in the file to produce
-- constant, variable, and function environments.
mkFileNamespace :: Node a File -> TranslateM' Namespace
mkFileNamespace (In (FileNode _path _name decls _imports)) = do
  Just ha <- gets halloc
  foldM (\ns decl -> case decl of
            In (FuncDecl _x recv (Ident _k nm)
                 params _variadic results _body) -> do
              Some paramsRepr <- someCtxRepr <$>
                mapM translateType (fieldType <$> maybeToList recv ++ params)
              Some retRepr <- translateType $ mkReturnType $ fieldType <$> results
              h <- liftIO' $
                mkHandle' ha (functionNameFromText nm) paramsRepr retRepr
              -- return $ insert_global nm
              --   (AnyGoExpr $ Some $ GoExpr Nothing $
              --    Gen.App $ C.JustValue (FunctionHandleRepr paramsRepr retRepr) $
              --    Gen.App $ C.HandleLit h) ns
              return $ insert_function nm (SomeHandle h) ns
            In (GenDecl _x specs) -> specsUpdNamespace specs ns
            _decl -> return ns)
    def decls

-- | Declare globals. The initializer will give them their initial
-- values later on.
specsUpdNamespace :: [Node a Spec] -> Namespace -> TranslateM' Namespace
specsUpdNamespace [] ns = return ns
specsUpdNamespace (spec : specs) ns = upd spec ns >>= specsUpdNamespace specs
  where
    upd :: Node a Spec -> Namespace -> TranslateM' Namespace
    upd (In (ConstSpec _x names tp values)) ns =
      foldM (f $ typeOf' <$> tp) ns $ zip names $
      -- The number of RHS values is either 0 or equal to the number
      -- of LHS names, so here we map Just over the values and append
      -- an infinite tail of Nothings to account for the case in which
      -- there are no values.
      (Just <$> values) ++ repeat Nothing
    upd (In (VarSpec _x names tp values)) ns =
      foldM (f $ typeOf' <$> tp) ns $ zip names $
      (Just <$> values) ++ repeat Nothing
    upd _spec ns = return ns

    f :: Maybe Type -> Namespace -> (Ident, Maybe (Node a Expr))
      -> TranslateM' Namespace
    f tp ns (Ident _k name, value) = do
      Just ha <- gets halloc
      tp' <- fromMaybe (case value of
                          Just v -> return $ typeOf' v
                          Nothing -> fail "specsUpdNamespace: expected value when type is missing") $ return <$> tp
      Some repr <- translateType tp'
      glob <- liftIO' $ Gen.freshGlobalVar ha name repr
      trace ("creating fresh global " ++ show glob) $
        trace ("name: " ++ show name) $
        trace ("tp: " ++ show tp) $
        trace ("repr: " ++ show repr) $ do
        let goglob = GoGlobal glob $ maybe (error "asdfg") id $ zeroValue tp' repr
      -- goglob <- GoGlobal glob <$> maybe (fail "asdf") return $ zeroValue tp' repr
      -- Record the global in list of all globals.
        addGlobal goglob
      -- Insert it into the namespace.
        return $ insert_global name goglob ns

indexedAssignment :: Assignment f ctx
                  -> Assignment (Product (Index ctx) f) ctx
indexedAssignment =
  runIdentity . traverseWithIndex (\ix x -> return $ Pair ix x)

indexedList :: Assignment f ctx -> [Some (Product (Index ctx) f)]
indexedList = toListFC Some . indexedAssignment

someIndexVal :: Assignment f ctx -> Int -> Some (Product (Index ctx) f)
someIndexVal assignment i = indexedList assignment !! i

withIndex :: Assignment f ctx
          -> Int
          -> (forall tp. Index ctx tp -> f tp -> a)
          -> a
withIndex assignment i k = case someIndexVal assignment i of
  Some (Pair ix x) -> k ix x

runSpec :: TypeRepr ret -> Translated Spec -> GoGenerator s ret ()
runSpec retRepr (TranslatedVarSpec names ty values) = do
  values' <- mapM (runTranslatedExpr retRepr) values
  forM_ (zip names values) $ \(Ident _k name, TranslatedExpr gen) -> do
    Some (GoExpr _loc value) <- runSomeGoGenerator retRepr gen
    case ty of
      Just (TranslatedType (Some repr)) -> declareVar name $ asType repr value
      Nothing -> declareVar name value
runSpec _repr _spec = return ()

translateBuiltin :: Ident -> Ident -> [Translated Expr] -> TranslateM' (Translated Expr)
translateBuiltin _qual ident@(Ident _k name) args = do
  Some retRepr <- gets retRepr
  case name of
    "panic" ->
      return $ TranslatedExpr $ SomeGoGenerator retRepr $ do
      args' <- mapM (runTranslatedExpr retRepr) args
      Gen.reportError $ Gen.App $ C.StringLit $ UnicodeLiteral $
        T.pack $ "panic: " ++ show args'
    -- TODO: len, make, new, etc.
    _nm ->
      fail $ "translateBuiltin: unknown identifier: " ++ show ident

localNamespace :: TranslateM' Namespace
localNamespace = gets $ \(TransState { namespaces = ns
                                     , pkgName = name }) ->
                          fromJust $ HM.lookup name ns

fieldsType :: [Node a Field] -> Type
fieldsType = TupleType . fmap (typeToNameType . fieldType)

-- | A slice is represented by a vector reference and three nats:
-- 1) begin of slice range
-- 2) end of slice range
-- 3) capacity
type SliceCtx tp =
  EmptyCtx ::> ReferenceType (VectorType tp) ::> NatType ::> NatType ::> NatType
type SliceType tp = StructType (SliceCtx tp)

sliceCtx :: TypeRepr tp -> CtxRepr (SliceCtx tp)
sliceCtx repr =
  Empty :> ReferenceRepr (VectorRepr repr) :> NatRepr :> NatRepr :> NatRepr

sliceType :: TypeRepr tp -> TypeRepr (SliceType tp)
sliceType repr = StructRepr $ sliceCtx repr

-- | Provide default values for begin, end, or capacity.
sliceValue :: Gen.Expr Go s (ReferenceType (VectorType tp))
           -> Maybe (Gen.Expr Go s NatType)
           -> Maybe (Gen.Expr Go s NatType)
           -> Maybe (Gen.Expr Go s NatType)
           -> GoGenerator s ret (Gen.Expr Go s (SliceType tp))
sliceValue vec begin end cap = do
  vec' <- Gen.readRef vec
  let begin' = fromMaybe (Gen.App $ C.NatLit 0) begin
      end' = fromMaybe (Gen.App $ C.VectorSize vec') end
      cap' = fromMaybe (Gen.App $ C.NatSub end' begin') cap
  case exprType vec of
    ReferenceRepr (VectorRepr repr) ->
      return $ Gen.App $ C.MkStruct (sliceCtx repr) $
      Ctx.empty :> vec :> begin' :> end' :> cap'

goExprToNat :: Some (GoExpr s) -> GoGenerator s ret (Gen.Expr Go s NatType)
goExprToNat (Some (GoExpr _loc e)) = case exprType e of
  BVRepr w -> return $ Gen.App $ C.BvToNat w e
  repr -> fail $ "toNat: expected bit vector, got " ++ show repr

-- | Helper for constructing function CFGs, used for both function
-- declarations and function literals.
mkFunction :: Maybe (Product (Node a) TranslateM  Field) -- ^ receiver type
           -> Maybe Ident -- ^ function name
           -> [Product (Node a) TranslateM Field] -- ^ params
           -> Maybe (Product (Node a) TranslateM Field) -- ^ variadic
           -> [Product (Node a) TranslateM Field] -- ^ results
           -> Maybe (TranslateM Block) -- ^ body
           -> TranslateM' (C.AnyCFG Go)
mkFunction recv name params variadic results body =
  -- trace ("translating function " ++ show name) $
  do
  fromMaybe (return ()) $
    fail "translate_alg FuncDecl: unexpected variadic parameter (should\
         \ have been desugared away)" <$> variadic
  params' <- mapM runTranslated $ maybeToList recv ++ params
  results' <- mapM runTranslated results
  -- Set return type in translator state.
  -- repr <- translateType $ mkReturnType $ (fieldType . proj1) <$> results
  -- modify $ \ts -> ts { retRepr = repr }
  globals <- ns_globals <$> localNamespace
  functions <- ns_funcs <$> localNamespace
  Just sng <- gets sng
  Just ha <- gets halloc
  pkgName <- gets pkgName
  bindFields params' $ \paramsRepr paramsGen ->
    bindResult results' $ \resultRepr resultGen -> do
    
    -- SomeHandle h <- case name of
    --   Just (Ident _k nm) -> return $ fromJust $ HM.lookup nm fenv
    --   -- If there is no function name, allocate a new anonymous handle
    --   Nothing -> SomeHandle <$>
    --     (liftIO' $ mkHandle' ha (functionNameFromText "@anon") paramsRepr resultRepr)

    SomeHandle h <- case name of
      Just (Ident _k nm) -> return $ fromJust $ HM.lookup nm functions
        -- AnyGoExpr (Some (GoExpr _loc (Gen.App (C.JustValue _repr (Gen.App (C.HandleLit h)))))) ->
          -- return $ SomeHandle h
      -- If there is no function name, allocate a new anonymous handle
      Nothing -> SomeHandle <$>
        (liftIO' $ mkHandle' ha (functionNameFromText "@anon") paramsRepr resultRepr)
        
    Refl <- failIfNotEqual paramsRepr (handleArgTypes h) $
            "translate_alg FuncDecl: checking argument types"
    Refl <- failIfNotEqual resultRepr (handleReturnType h) $
            "translate_alg FuncDecl: checking return type"
    (Gen.SomeCFG g, []) <- case body of
      Just body' -> do
        modify $ \ts -> ts { retRepr = Some resultRepr }
        TranslatedBlock body_gen <- runTranslateM body'
        liftIO' $ Gen.defineFunction InternalPos sng h
          (\assignment ->
             (def, do
               --  ("resultRepr: " ++ show resultRepr) $ do
                 paramsGen $ fmapFC Gen.AtomExpr assignment
                 zeroValue' (fieldsType $ proj1 <$> results) resultRepr >>= resultGen
                 runSomeGoGenerator resultRepr body_gen
                 -- Fail if no return.
                 Gen.reportError $
                   Gen.App (C.StringLit "missing return statement")))
      Nothing ->
        liftIO' $ Gen.defineFunction InternalPos sng h
        (\assignment -> (def :: GenState s, Gen.reportError $
                              Gen.App (C.StringLit "missing function body")))
    let g' = case toSSA g of C.SomeCFG g' -> C.AnyCFG g'
    addFunction ((\(Ident _k nm) -> (pkgName, functionNameFromText nm)) <$> name) g'
    if maybe "" identName name == "main" then
      modify $ \ts -> ts { mainFunction = Just g' }
      else return ()
    return g'

mkInitializer :: [Translated Package]
              -> TranslateM' (C.SomeCFG Go EmptyCtx UnitType)
mkInitializer pkgs = do
  Just sng <- gets sng
  Just ha <- gets halloc
  pkgName <- gets pkgName
  h <- liftIO' $ mkHandle' ha (functionNameFromText "@init") Ctx.empty UnitRepr
  (Gen.SomeCFG g, []) <- liftIO' $ Gen.defineFunction InternalPos sng h
    (\assignment -> (def, do
                        forM_ pkgs $ runSomeGoGenerator UnitRepr . packageInit
                        Gen.returnFromFunction $ Gen.App C.EmptyApp))
  -- return $ toSSA g
  case toSSA g of
    C.SomeCFG g' -> do
      addFunction Nothing $ C.AnyCFG g'
      return $ C.SomeCFG g'


mkBasicConst :: PosNat -> BasicConst -> Some (Gen.Expr Go s)
mkBasicConst n@(PosNat w LeqProof) c = case c of
  BasicConstBool b -> Some $ Gen.App $ C.BoolLit b
  BasicConstString str -> Some $ Gen.App $ C.StringLit $ UnicodeLiteral str
  BasicConstInt i -> Some $ Gen.App $ C.BVLit w i
  BasicConstFloat num denom -> case (mkBasicConst n num, mkBasicConst n denom) of
    (Some num', Some denom') -> asType' (BVRepr w) num' $ \num'' ->
      asType' (BVRepr w) denom' $ \denom'' ->
      Some $ Gen.App $ C.FloatDiv DoubleFloatRepr C.RNE
      (Gen.App $ C.FloatFromBV DoubleFloatRepr C.RNE num'')
      (Gen.App $ C.FloatFromBV DoubleFloatRepr C.RNE denom'')
  BasicConstComplex real imag ->
    error "mkBasicConst: complex numbers not yet supported"
