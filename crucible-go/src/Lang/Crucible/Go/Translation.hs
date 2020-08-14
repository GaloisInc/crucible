{-|
Module      : Lang.Crucible.Go.Translation
Description : Go translation module
Maintainer  : abagnall@galois.com
Stability   : experimental

The translator is a paramorphism on Go abstract syntax with state
monad carrier. The 'para' allows us to have access to the original AST
nodes during translation, and the state monad enables top-down data
flow via the state as well as general statefulness for accumulating
results.

The translation is entirely compositional: an AST node is translated
by first translating all of its children nodes and then combining them
in some way to produce the result. One downside of this is that it
seems to require more existential quantification of type variables
than would otherwise be necessary. Most notable is the 'ret' index on
generator actions. All generator actions within the body of a given
function have the same 'ret' index, but since they are constructed and
existentially packaged separately, their 'ret' indices must be
re-unified when combining them in sequence.

TYPE COERCION:
Wherever an expression appears in a context that expects a specific
type (e.g., an argument is expected to have the corresponding
parameter type declared by the function being called), the
'asTypeEither' function (or one of its variants) is used to perform
the check as well as possibly allowing some implicit coercions. This
is primarily to deal with the lack of precise type information on
"untyped constants" (which essentially means something like "softly
typed" or "not totally committed to a type yet"). Consider the
following example:

  var x float32 = 5.0

The literal '5.0' on the RHS is an "untyped float", which is
represented as a 64-bit float by default and must be rounded to fit in
a float32 variable. Similarly, consider the declaration of a slice
initialized with nil:

  var l []int32 = nil

The RHS is an "untyped nil", which can be assigned to pointers,
slices, maps, etc. When translating a nil expression in isolation, we
don't know what type it will eventually inhabit, so we just produce
the unit value. Since all nil-able types are encoded as Crucible Maybe
types, we simply allow the unit value to be coerced to the Nothing
value of any Maybe type. An alternative solution could be to perform
some pre-pass to infer the eventual types of all untyped constants (it
seems that Go's typechecker is already doing this for us for integers).

GLOBAL LOOKUP FAILURE IS NOT AN ERROR:
Built-in function names may be shadowed by user-defined symbols, so we
allow a lookup attempt before considering them as built-ins.
-}
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

import           Data.BitVector.Sized
import           Data.Default.Class
import           Data.Functor.Const
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
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

import           What4.FunctionName (functionNameFromText)
import           What4.ProgramLoc
import           What4.Utils.StringLiteral

import           Language.Go.AST
import           Language.Go.Rec
import           Language.Go.Types
import           Lang.Crucible.Go.Builtin
import           Lang.Crucible.Go.Encodings
import           Lang.Crucible.Go.TransUtil
import           Lang.Crucible.Go.Types

-- | Entry point.
translate :: Show a
          => PosNat -- ^ machine word width
          -> Node a tp -- ^ AST to translate
          -> IO (Either String (Translated tp))
translate w = evalTranslateM (def { machineWordWidth = w }) . translateM

translateM :: Show a => Node a tp -> TranslateM tp
translateM = para translate_alg

evalTranslateM :: TransState
               -> TranslateM a
               -> IO (Either String (Translated a))
evalTranslateM st (TranslateM m) = runExceptT $ evalStateT m st

-- | The translation algebra.
translate_alg :: Show a
              => NodeF a (Product (Node a) TranslateM) tp
              -> TranslateM tp

-- | Translate a top-level AST node, containing a "main" package along
-- with all of the packages it depends on (directly or transitively),
-- assumed to be ordered topologically so that it's safe to simply
-- translate them left-to-right.
translate_alg (MainNode nm (Pair main_node (TranslateM mainM)) imports) =
  TranslateM $ do
  sng <- liftIO' newIONonceGenerator
  halloc <- liftIO' newHandleAllocator
  modify $ \ts -> ts { sng = Just sng, halloc = Just halloc }

  -- First translate the imports in the order in which they appear.
  imports' <- forM imports $ \(Pair import_node (TranslateM importM)) -> do
    -- Build namespace for the package and add it to the state.
    let name = packageName import_node
    ns <- mkPackageNamespace import_node
    modify $ \ts -> ts { pkgName = name
                       , namespaces = HM.insert name ns (namespaces ts) }
    -- Translate the package.
    importM

  -- Build namespace for the main package.
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

-- | Translate a single package.
translate_alg (PackageNode name path import_paths file_paths files inits) =
  TranslateM $ do
  files' <- mapM runTranslated files
  modify $ \ts -> ts { retRepr = Some UnitRepr }
  inits' <- mapM runTranslated inits
  return $ TranslatedPackage name path import_paths file_paths files' $
    -- Build a single package initializer generator action from all of
    -- the file initializers.
    SomeGoGenerator UnitRepr $ forM_ inits' $ runTranslatedStmt UnitRepr

-- | Translate a single file.
translate_alg (FileNode path name decls imports) =
  TranslateM $ TranslatedFile path name <$>
  mapM runTranslated decls <*> mapM runTranslated imports


------------------------------------------------------------------------
-- Translating statements

-- | Translate an assign statement. NOTE: the current treatment of the
-- lexical environment is too coarse-grained to know when we can
-- safely reuse variables (in the case of short-declarations with
-- multiple idents in the LHS). We need a stack of nested local
-- scopes. Only when lookup succeeds in the innermost scope is it safe
-- to reuse the existing variable location. For now we just always
-- introduce new variables.
translate_alg (AssignStmt _ assign_tp op lhs rhs) = TranslateM $ do
  lhs_gens <- mapM runTranslated lhs
  rhs_gens <- mapM runTranslated rhs
  Some retRepr <- gets retRepr
  ts <- get
  return $ mkTranslatedStmt retRepr $ do
    rhs' <- forM rhs_gens $ runTranslatedExpr retRepr
    case assign_tp of
      Assign -> do
        lhs' <- forM lhs_gens $ runTranslatedExpr' retRepr
        -- forM_ (zip lhs' rhs') $ \(Some (GoExpr (Just loc) l), r) ->
        forM_ (zip lhs' rhs') $ \(l, r) ->
          case l of
            Left _ -> return ()
            Right (Some (GoExpr (Just loc) l')) ->
              writeToLoc (exprType l') loc r
      Define ->
        forM_ (zip (proj1 <$> lhs) rhs') $
        \(In (IdentExpr _x _tp qual name), r) -> do
          -- For now, always declare a new variable.
          Some (GoExpr _loc r') <- return r
          declareVar (identName name) r'
      AssignOperator ->
        fail "translate_alg AssignStmt: expected AssignOperator to be desugared"

translate_alg (BlockStmt _ block) = TranslateM $ do
  TranslatedBlock gen <- runTranslated block
  return $ TranslatedStmt gen

translate_alg (BranchStmt _ branch_tp label) = TranslateM $ do
  Some retRepr <- gets retRepr
  return $ mkTranslatedStmt retRepr $ do
    case label of
      Just label' -> case branch_tp of
        Break -> getBreakLabel label' >>= Gen.jump
        Continue -> getContinueLabel label' >>= Gen.jump
        Goto -> getLabel label' >>= Gen.jump
        Fallthrough -> fail "BranchStmt: Fallthrough not supported"
      Nothing -> case branch_tp of
        Break -> peekBreakLabel >>= Gen.jump
        Continue -> peekContinueLabel >>= Gen.jump
        Goto -> fail "BranchStmt: missing label in 'goto'"
        Fallthrough -> fail "BranchStmt: Fallthrough not supported"

-- const, type, or var declaration (similar to assign)
translate_alg (DeclStmt _ decl) = TranslateM $ do
  TranslatedGenDecl specs <- runTranslated decl
  Some retRepr <- gets retRepr
  return $ mkTranslatedStmt retRepr $ forM_ specs $ runSpec retRepr

translate_alg (DeferStmt _ call_expr) =
  TranslateM $ fail "translate_alg DeferStmt: unsupported"

translate_alg (EmptyStmt _) = TranslateM $ do
  Some retRepr <- gets retRepr
  return $ mkTranslatedStmt retRepr $ return ()

translate_alg (ExprStmt _ expr) = TranslateM $ do
  TranslatedExpr somegen <- runTranslated expr
  Some retRepr <- gets retRepr
  return $ mkTranslatedStmt retRepr $
    runSomeGoGenerator retRepr somegen >> return ()

translate_alg (ForStmt _ ini cond post body) = TranslateM $ do
  ini' <- mapM runTranslated ini
  cond' <- mapM runTranslated cond
  post' <- mapM runTranslated post
  TranslatedBlock body_gen <- runTranslated body
  Some retRepr <- gets retRepr
  return $ mkTranslatedStmt retRepr $ do
    forM_ ini' $ runTranslatedStmt retRepr
    loop_lbl <- Gen.newLabel
    post_lbl <- Gen.newLabel
    exit_lbl <- Gen.newLabel
    pushLoopLabels post_lbl exit_lbl
    -- Clear the current label since we have used it for this loop. If
    -- there happens to be an inner loop within the body of this one,
    -- we wouldn't want it to get the wrong idea and use our label.
    modify $ \gs -> gs { current_label = Nothing }
    let cond_gen = maybe (return $ mkSomeGoExpr' $ C.BoolLit True)
                   (runTranslatedExpr retRepr) cond'
    Gen.defineBlock loop_lbl $ do
      b <- runBool cond_gen
      Gen.whenCond b $ do
        runSomeGoGenerator retRepr body_gen
        Gen.jump post_lbl
      Gen.jump exit_lbl
    Gen.defineBlock post_lbl $ do
      maybe (return ()) (runTranslatedStmt retRepr) post'
      Gen.jump loop_lbl
    popLoopLabels
    Gen.continue exit_lbl $ Gen.jump loop_lbl

translate_alg (GoStmt _ call_expr) =
  TranslateM $ fail "translate_alg GoStmt: unsupported"

translate_alg (IfStmt _ ini cond body els) = TranslateM $ do
  ini_gen <- mapM runTranslated ini
  TranslatedExpr cond_gen <- runTranslated cond
  body_gen <- runTranslated body
  els_gen <- mapM runTranslated els
  Some retRepr <- gets retRepr
  return $ mkTranslatedStmt retRepr $ do
    forM_ ini_gen $ runTranslatedStmt retRepr
    Some (GoExpr _loc cond') <- runSomeGoGenerator retRepr cond_gen
    asType' BoolRepr cond' $ \cond'' ->
      Gen.ifte_ cond'' (runTranslatedBlock retRepr body_gen) $ case els_gen of
      Nothing -> return ()
      Just (TranslatedStmt gen) -> runSomeGoGenerator retRepr gen

translate_alg (IncDecStmt _ expr is_incr) = TranslateM $
  fail "translate_alg IncDecStmt: should have been desugared to an assignment"

translate_alg (LabeledStmt _ label stmt) = TranslateM $ do
  Some retRepr <- gets retRepr
  TranslatedStmt stmt_gen <- runTranslated stmt
  return $ mkTranslatedStmt retRepr $ do
    -- Set the current label ONLY WHEN the inner statement is a
    -- loop. It will be used and disposed of (reset to Nothing) when
    -- translating the loop.
    when (isLoop $ proj1 stmt) $
      modify $ \gs -> gs { current_label = Just label }
    lbl <- getLabel label
    exit_lbl <- Gen.newLabel
    Gen.defineBlock lbl $ do
      runSomeGoGenerator retRepr stmt_gen
      Gen.jump exit_lbl
    Gen.continue exit_lbl $ Gen.jump lbl

translate_alg (RangeStmt _ key value range body is_assign) = TranslateM $
  fail "translate_alg: RangeStmt not supported (should have been desugared\
       \ for slices and arrays)"


translate_alg (ReturnStmt _ exprs) = TranslateM $ do
  Some retRepr <- gets retRepr
  case exprs of
    [expr] -> do
      TranslatedExpr expr_gen <- runTranslated expr
      return $ mkTranslatedStmt retRepr $ do
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
translate_alg (InitializerStmt vars values) = TranslateM $ do
  vars' <- mapM runTranslated vars
  values' <- mapM runTranslated values
  return $ mkTranslatedStmt UnitRepr $
    forM_ (zip vars' values') $ \(var, value) -> do
      Some (GoExpr (Just loc) var') <- runTranslatedExpr UnitRepr var
      value' <- runTranslatedExpr UnitRepr value
      writeToLoc (exprType var') loc value'


------------------------------------------------------------------------
-- Translating value-level expressions

-- | The default type of an untyped constant is bool, rune, int,
-- float64, complex128 or string respectively, depending on whether it
-- is a boolean, rune, integer, floating-point, complex, or string
-- constant. -- GO LANGUAGE SPEC
translate_alg (BasicLitExpr _ tp
               (BasicLit { basiclit_type = lit_ty
                         , basiclit_value = lit_value })) = TranslateM $ do
  Some retRepr <- gets retRepr
  PosNat w LeqProof <- gets machineWordWidth
  return $ mkTranslatedExpr retRepr $ case lit_ty of
    LiteralBool -> return $ mkSomeGoExpr' $ C.BoolLit $ readBool lit_value
    LiteralInt -> return $ mkSomeGoExpr' $ C.BVLit w $ read $ T.unpack lit_value
    LiteralFloat ->
      return $ mkSomeGoExpr' $ C.DoubleLit $ read $ T.unpack lit_value
    LiteralComplex -> fail "translate_alg: complex literals not yet supported"
    LiteralImag -> fail "translate_alg: imaginary literals not yet supported"
    LiteralChar -> case fromJust $ intToPosNat 8 of
      PosNat w8 LeqProof ->
        -- This is probably wrong (need to parse the character code correctly)
        return $ mkSomeGoExpr' $ C.BVLit w8 $ read $ T.unpack lit_value
    LiteralString ->
      return $ mkSomeGoExpr' $ C.StringLit $ UnicodeLiteral lit_value

translate_alg (BasicConstExpr _x tp c) = TranslateM $ do
  Some retRepr <- gets retRepr
  w <- fromMaybe (gets machineWordWidth) $ return <$> typeWidth tp
  return $ mkTranslatedExpr retRepr $
    case mkBasicConst w c of Some e -> return $ mkSomeGoExpr e

-- | Coerce "untyped" operands to the type of the other side. It may
-- be possible to simplify this by just coercing values more-or-less
-- indiscriminately (bitvectors may truncate to match the size of the
-- smaller operand, 32-bit floats may promote to 64-bit, etc.), since
-- at least one of the operands will be "typed" (untyped constants are
-- fully evaluated by this point).
translate_alg (BinaryExpr _ tp left op right) = TranslateM $ do
  (left', right') <- pairM (runTranslated left) (runTranslated right)
  let (left_ty, right_ty) = (typeOf' $ proj1 left, typeOf' $ proj1 right)
  Some retRepr <- gets retRepr
  return $ mkTranslatedExpr retRepr $ do
    (l, r) <- pairM (runTranslatedExpr retRepr left')
              (runTranslatedExpr retRepr right')
    case op of
      x | x `elem` [BPlus, BMinus, BMult, BDiv, BMod, BAnd, BOr,
                    BXor, BAndNot, BLAnd, BLOr, BShiftL, BShiftR] -> do
            (tp', Some (PairIx l' r')) <- unify_exprs left_ty right_ty l r
            Some . GoExpr Nothing <$> translateHomoBinop tp' op l' r'
      x | x `elem` [BEq, BLt, BGt, BNeq, BLeq, BGeq] -> do
            (tp', Some (PairIx l' r')) <- unify_exprs left_ty right_ty l r
            Some . GoExpr Nothing <$> translateComparison tp' op l' r'
      -- BShiftL -> fail "translate_alg BinaryExpr: BShiftL not yet supported"
      -- BShiftR -> fail "translate_alg BinaryExpr: BShiftR not yet supported"

translate_alg (CallExpr _ tp _ellipsis fun args) = TranslateM $ do
  Some retRepr <- gets retRepr
  translated_fun <- runTranslated fun
  translated_args <- mapM runTranslated args
  case translated_fun of
    TranslatedExpr fun_gen ->
      return $ mkTranslatedExpr retRepr $ do
        Some (GoExpr _loc fun') <- runSomeGoGenerator retRepr fun_gen
        args' <- forM translated_args $
                 runSomeGoGenerator retRepr . unTranslatedExpr
        withAssignment args' $ \ctxRepr assignment ->
          case exprType fun' of
            MaybeRepr (FunctionHandleRepr argsRepr _retRepr) ->
              case fun' of
                Gen.App (C.JustValue _repr f) -> Some . GoExpr Nothing <$>
                  Gen.call f (coerceAssignment argsRepr assignment)
                Gen.App (C.NothingValue _repr) ->
                  fail "translate_alg CallExpr: attempt to call nil function"
                _ -> do
                  maybeElim' fun' $ \f -> Some . GoExpr Nothing <$>
                    Gen.call f (coerceAssignment argsRepr assignment)
            _ -> fail $ "translate_alg CallExpr: expected function type, got "
                 ++ show (exprType fun')
    TranslatedUnbound qual ident ->
      translateBuiltin qual ident args

-- TODO
translate_alg (CastExpr _ tp expr ty) =
  TranslateM $ fail "translate_alg CastExpr: unsupported"

-- | For both arrays and slices we must construct a new array, and in
-- the case of a slice literal also allocate a reference for it and
-- embed it in a slice. For arrays, generate a zero-value array of the
-- specified length and then iterate over the provided elements to
-- overwrite zeroes. For slices, do the same but use the number of
-- provided elements as the size.
translate_alg (CompositeLitExpr _ tp _ty elements) = TranslateM $ do
  Some retRepr <- gets retRepr
  Some repr <- translateType tp
  element_gens <- mapM runTranslated elements
  tryAsSliceRepr repr
    (\sliceRepr -> do
        return $ mkTranslatedExpr retRepr $ do
          zero <- zeroVector (length elements) (elementType tp) $
                  sliceElementRepr sliceRepr
          elements' <- forM element_gens $ runTranslatedExpr retRepr
          vec <- writeVectorElements zero elements'
          arr <- Gen.newRef vec
          ptr <- newRefPointer arr
          slice <- sliceValue' ptr 0 (length elements - 1) $ length elements
          return $ mkSomeGoExpr slice) $
    tryAsArrayRepr repr
    (\arrRepr ->
        return $ mkTranslatedExpr retRepr $ do
          -- Create initial array with all zero elements.
          zero <- zeroVector (arrayTypeLen tp) (elementType tp) $
                  arrayElementRepr arrRepr
          elements' <- forM element_gens $ runTranslatedExpr retRepr
          -- Iterate over elements' to overwrite some or all of the array.
          vec <- writeVectorElements zero elements'
          arr <- Gen.newRef vec
          return $ mkSomeGoExpr arr) $
    fail $ "translate_alg CompositeLitExpr: expected array or slice type, got "
    ++ show repr

-- | A translated IdentExpr is either:
-- 1) a GoExpr containing the location of the variable as well as its
-- value.
-- 2) a TranslatedUnbound value to indicate global lookup failure.
-- Lookup failure isn't necessarily an error (any well-typed program
-- will not contain erroneous lookups); we expected uses of built-in
-- function identifiers to result in lookup failures.
translate_alg (IdentExpr _ tp qual ident@(Ident _kind name)) = TranslateM $ do
  Some retRepr <- gets retRepr
  case qual of
    -- No qualifier means local variable.
    Nothing ->
      return $ mkTranslatedExpr retRepr $ do
      gamma <- gets gamma
      case HM.lookup name gamma of
        Just (Some gr@(GoReg _repr reg)) -> do
          ref <- Gen.readReg reg
          e <- Gen.readRef ref
          return $ Some $ GoExpr (Just $ GoLocRef ref) e
        Nothing ->
          -- | Local lookup failure.
          -- return $ mkSomeGoExpr' C.EmptyApp
          fail $ "translate_alg IdentExpr: unbound local " ++ show name
    Just q -> lookupGlobal q ident

translate_alg (FuncLitExpr _ tp params results body) =  
  TranslateM $ do
  Some retRepr <- gets retRepr
  C.AnyCFG g <- mkFunction Nothing Nothing params Nothing results $
                Just body
  return $ mkTranslatedExpr retRepr $
    return $ mkSomeGoExpr' $ C.HandleLit $ C.cfgHandle g

-- | Only support array/slice indexing for now.
translate_alg (IndexExpr _ tp expr index) = TranslateM $ do
  TranslatedExpr expr_gen <- runTranslated expr
  TranslatedExpr index_gen <- runTranslated index
  Some retRepr <- gets retRepr
  return $ mkTranslatedExpr retRepr $ do
    Some (GoExpr loc e) <- runSomeGoGenerator retRepr expr_gen
    Some (GoExpr _loc ix) <- runSomeGoGenerator retRepr index_gen
    let natIx = case exprType ix of
          BVRepr w -> Gen.App $ C.BvToNat w ix
    tryAsArray e
      (\repr arr ->
          Some . GoExpr (Just $ GoLocPointer $ mkArrayOffsetPointer arr natIx)
            <$> arrayGetSafe repr natIx arr
      ) $
      tryAsSlice e
      (\repr slice -> do
          arr <- readPointer =<< sliceArray slice
          begin <- sliceBegin slice
          let ix' = Gen.App $ C.NatAdd begin natIx
          Some . GoExpr (Just $ GoLocPointer $ mkArrayOffsetPointer arr ix')
            <$> arrayGetSafe repr ix' arr
      ) $
      tryAsString e
      (\si str -> do
          fail $ "translate_alg IndexExpr: string indexing not yet supported"
      ) $
      fail $ "translate_alg IndexExpr: unexpected LHS: " ++ show (proj1 expr)

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
  return $ mkTranslatedExpr retRepr $ do
    Some (GoExpr loc e) <- runSomeGoGenerator retRepr arr_gen
    begin' <- mapM (runTranslatedExpr retRepr >=> goExprToNat) begin_gen
    end' <- mapM (runTranslatedExpr retRepr >=> goExprToNat) end_gen
    cap' <- mapM (runTranslatedExpr retRepr >=> goExprToNat) cap_gen
    -- If slice, reslice.
    tryAsSlice e (\repr slice -> Some . GoExpr Nothing <$>
                                 reslice slice begin' end' cap') $
      -- Else it should be an array.
      case exprType e of
        ReferenceRepr (VectorRepr repr) -> do
          -- If the array has a corresponding assignable location, use
          -- that. Otherwise, allocate a new reference cell for it.
          ptr <- case loc of
            Just loc' -> mkLocPointer loc'
            Nothing -> mkRefPointer <$> Gen.newRef e
          Some . GoExpr Nothing <$> sliceValue ptr begin' end' cap'
        _repr -> fail "translate_alg SliceExpr: expected array or slice"

translate_alg (StarExpr _ tp operand) = TranslateM $ do
  TranslatedExpr operand_gen <- runTranslated operand
  Some retRepr <- gets retRepr
  return $ mkTranslatedExpr retRepr $ do
    Some (GoExpr _loc e) <- runSomeGoGenerator retRepr operand_gen
    -- Check for nil constant explicitly here since we don't
    -- necessarily know what the type should be.
    case e of
      Gen.App C.EmptyApp ->
        fail "translate_alg StarExpr: dereference nil constant"
      _e -> asPointer e $ \ e' -> do
        result <- readPointer e'
        return $ Some $ GoExpr (Just $ GoLocPointer e') result

translate_alg (TypeAssertExpr _ tp expr asserted_ty) =
  TranslateM $ fail "translate_alg TypeAssertExpr: unsupported"

translate_alg (UnaryExpr _ tp op e) = TranslateM $ do
  Some retRepr <- gets retRepr
  TranslatedExpr e_gen <- runTranslated e
  let e_tp = typeOf' $ proj1 e
  return $ mkTranslatedExpr retRepr $ do
    Some (GoExpr loc e') <- runSomeGoGenerator retRepr e_gen
    case op of
      UPlus -> case exprType e' of
        BVRepr w -> do
          zero <- zeroValue' e_tp $ BVRepr w
          return $ mkSomeGoExpr' $ C.BVAdd w zero e'
        FloatRepr fi -> do
          zero <- zeroValue' e_tp $ FloatRepr fi
          return $ mkSomeGoExpr' $ C.FloatAdd fi C.RNE zero e'
        ty ->
          fail $ "translate_alg UnaryExpr UPlus: unsupported type " ++ show ty
      UMinus -> case exprType e' of
        BVRepr w -> do
          zero <- zeroValue' e_tp $ BVRepr w
          return $ mkSomeGoExpr' $ C.BVSub w zero e'
        FloatRepr fi -> return $ mkSomeGoExpr' $ C.FloatNeg fi e'
        ty ->
          fail $ "translate_alg UnaryExpr UMinus: unsupported type " ++ show ty
      UNot -> case exprType e' of
        BoolRepr -> return $ mkSomeGoExpr' $ C.Not e'
        ty ->
          fail $ "translate_alg UnaryExpr UNot: unsupported type " ++ show ty
      UBitwiseNot -> case exprType e' of
        BoolRepr -> return $ mkSomeGoExpr' $ C.Not e'
        BVRepr w -> return $ mkSomeGoExpr' $ C.BVNot w e'
      UStar -> fail "translate_alg UnaryExpr UStar: not yet supported"
      UAddress -> case loc of
        Just loc' -> mkSomeGoExpr <$> mkLocPointer loc'
        Nothing -> fail "translate_alg UnaryExpr UAddress: no location"
      UArrow -> fail "translate_alg UnaryExpr UArrow: not yet supported"

translate_alg (TupleExpr _ tp es) = TranslateM $ do
  Some retRepr <- gets retRepr
  es_gen <- mapM runTranslated es
  return $ mkTranslatedExpr retRepr $ do
    es' <- forM es_gen $ \(TranslatedExpr gen) -> runSomeGoGenerator retRepr gen
    withAssignment es' $ \ctxRepr assignment ->
      return $ mkSomeGoExpr' $ C.MkStruct ctxRepr assignment

translate_alg (ProjExpr _ tp tuple i) = TranslateM $ do
  Some retRepr <- gets retRepr
  TranslatedExpr tuple_gen <- runTranslated tuple
  return $ mkTranslatedExpr retRepr $ do
    Some (GoExpr _loc tuple') <- runSomeGoGenerator retRepr tuple_gen
    case exprType tuple' of
      StructRepr ctxRepr ->
        withIndex ctxRepr i $ \ix repr ->
        return $ mkSomeGoExpr' $ C.GetStruct tuple' ix repr
      repr ->
        fail $ "translate_alg ProjExpr: expected struct type, got" ++ show repr

translate_alg (NilExpr _x _tp) = TranslateM $ do
  Some retRepr <- gets retRepr
  return $ mkTranslatedExpr retRepr $ return $ mkSomeGoExpr' C.EmptyApp
                
------------------------------------------------------------------------
-- Translating type expressions

-- | Type expressions come decorated with their semantic types which
-- we translate to TypeReprs.
translate_alg (EllipsisExpr _ tp _ty) =
  TranslateM $ TranslatedType <$> translateType tp
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

------------------------------------------------------------------------
-- Translating declarations, specifications, misc.

-- | Generate the CFG for a function.
translate_alg (FuncDecl _ recv name params variadic results body) =
  -- trace ("translating function " ++ show name) $
  TranslateM $ TranslatedFuncDecl name <$>
  mkFunction recv (Just name) params variadic results body

translate_alg (GenDecl _ specs) =
  TranslateM $ TranslatedGenDecl <$> mapM runTranslated specs

translate_alg (TypeAliasDecl _ binds) =
  TranslateM $ return $ TranslatedGenDecl []

translate_alg (Binding ident expr) =
  TranslateM $ TranslatedBinding ident <$> runTranslated expr

translate_alg (ImportSpec _ pkg_name path) =
  TranslateM $ return TranslatedImportSpec

translate_alg (ConstSpec _ names ty values) = TranslateM $
  TranslatedVarSpec names <$>
  mapM runTranslated ty <*> mapM runTranslated values

translate_alg (VarSpec _ names ty values) = TranslateM $
  TranslatedVarSpec names <$>
  mapM runTranslated ty <*> mapM runTranslated values

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
    forM_ translated_stmts $ runTranslatedStmt retRepr
    modify $ \s -> s { gamma = gamma }


------------------------------------------------------------------------
-- Translating semantic types

-- Maybe generalize to MonadFail and use implicit parameter for
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
  -- that can contain any pointer. Maybe an AnyType pointer?
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
translateType (NamedType tp) = translateType tp
translateType (PointerType tp) = do
  Some repr <- translateType tp
  return $ Some $ PointerRepr repr
translateType (FuncType recv params result variadic) = do
  Some params' <- someCtxRepr <$>
    mapM translateType ((snd <$> maybeToList recv) ++ params)
  Some result' <- translateType result
  return $ Some $ MaybeRepr $ FunctionHandleRepr params' result'
translateType (SliceType tp) = do
  Some repr <- translateType tp
  return $ Some $ SliceRepr repr

translateType (StructType fields) = do
  Some ctxRepr <- someCtxRepr <$> mapM (translateType . typeOfNameType) fields
  return $ Some $ StructRepr ctxRepr
translateType (TupleType elts) = translateType (StructType elts)

someCtxRepr :: [Some TypeRepr] -> Some CtxRepr
someCtxRepr [] = Some Ctx.empty
someCtxRepr (Some repr : reprs) = case someCtxRepr reprs of
  Some ctxRepr -> Some $ ctxRepr :> repr

typeOfTranslatedExpr :: MonadFail m => Translated Expr -> m (Some TypeRepr)
typeOfTranslatedExpr (TranslatedType repr) = return repr
typeOfTranslatedExpr (TranslatedExpr _gen) =
  fail "typeOfTranslatedExpr: expected TranslatedType, got TranslatedExpr"


------------------------------------------------------------------------
-- Helper functions

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
  BMod -> case exprType left of
    BVRepr w -> case tp of
      BasicType (BasicInt _w) -> return $ Gen.App $ C.BVSrem w left right
      BasicType (BasicUInt _w) -> return $ Gen.App $ C.BVUrem w left right
      _ -> fail $ "translateHomoBinop BDiv: unexpected type " ++ show tp
    ty -> fail $ "translateHomoBinop BDiv: unsupported type " ++ show ty
  BAnd -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVAnd w left right
    ty -> fail $ "translateHomoBinop BAnd: unsupported type " ++ show ty
  BOr -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVOr w left right
    ty -> fail $ "translateHomoBinop BOr: unsupported type " ++ show ty
  BXor -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVXor w left right
    BoolRepr -> return $ Gen.App $ C.BoolXor left right
    ty -> fail $ "translateHomoBinop BXor: unsupported type " ++ show ty
  BAndNot -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVAnd w left (Gen.App $ C.BVNot w right)
    ty -> fail $ "translateHomoBinop BAndNot: unsupported type " ++ show ty
  -- Short-circuit evaluation for logical AND and OR
  BLAnd -> case exprType left of
    BoolRepr ->
      Gen.ifte left (return right) $ return $ Gen.App $ C.BoolLit False
    ty -> fail $ "translateHomoBinop BLAnd: unsupported type " ++ show ty
  BLOr -> case exprType left of
    BoolRepr ->
      Gen.ifte left (return $ Gen.App $ C.BoolLit True) $ return right
    ty -> fail $ "translateHomoBinop BLOr: unsupported type " ++ show ty
  BShiftL -> case exprType left of
    BVRepr w -> return $ Gen.App $ C.BVShl w left right
    ty -> fail $ "translateHomoBinop BShiftL: unsupported type " ++ show ty
  BShiftR -> case exprType left of
    -- TODO: not sure if this is correct
    BVRepr w -> return $ Gen.App $ C.BVLshr w left right
    ty -> fail $ "translateHomoBinop BShiftL: unsupported type " ++ show ty
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
    StringRepr si -> return $ C.BaseIsEq (BaseStringRepr si) left right
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
  BLeq -> case exprType left of
    BVRepr w -> return $ C.BVSle w left right
    FloatRepr _fi -> return $ C.FloatLe left right
    ty -> fail $ "translateComparison BLeq: unsupported type " ++ show ty
  BGeq -> case exprType left of
    BVRepr w -> return $ C.Not $ Gen.App $ C.BVSlt w left right
    FloatRepr _fi -> return $ C.FloatGe left right
    ty -> fail $ "translateComparison BGeq: unsupported type " ++ show ty
  BNeq -> fail "translateComparison: BNeq should have been desugared"
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
writeToLoc repr loc (Some (GoExpr _loc e)) =
  asType' repr e $ \e' -> case loc of
  GoLocRef ref -> Gen.writeRef ref e'
  GoLocGlobal glob -> Gen.writeGlobal glob e'
  GoLocArray arr index -> fail "writeToLoc: arrays not yet supported"
  GoLocPointer ptr -> writePointer ptr e'

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

zeroValue'' :: Type -> TranslateM' AnyGoExpr
zeroValue'' tp = do
  Some repr <- translateType tp
  return $ AnyGoExpr $ Some $ GoExpr Nothing $
    maybe (error "zeroValue'': no zero value") id $ zeroValue' tp repr

-- | Try to look up a global identifier, returning a TranslatedExpr if
-- successful. Otherwise return a TranslatedUnbound to signal that the
-- lookup failed.
lookupGlobal :: Ident -> Ident -> TranslateM' (Translated Expr)
lookupGlobal qual@(Ident _k pkgName) name@(Ident _k' nm) =
  do
  Some retRepr <- gets retRepr
  namespaces <- gets namespaces
  Namespace globals funcs <-
    maybe (fail $ "lookupGlobal: unknown package" ++ show pkgName)
    return $ HM.lookup pkgName namespaces
  -- Try lookup in globals
  case HM.lookup nm globals of
    Just (GoGlobal glob _zv) ->
      return $ mkTranslatedExpr retRepr $ do
      e <- Gen.readGlobal glob
      return $ Some $ GoExpr (Just $ GoLocGlobal glob) $ e
    Nothing ->
      -- Try lookup in funcs
      case HM.lookup nm funcs of
        Just (SomeHandle h) ->
          return $ mkTranslatedExpr retRepr $
          return $ mkSomeGoExpr' $
          C.JustValue (handleType h) $ Gen.App $ C.HandleLit h
        Nothing ->
          return $ TranslatedUnbound qual name

mkPackageNamespace :: Node a Package -> TranslateM' Namespace
mkPackageNamespace (In (PackageNode _name _path _imports
                         _file_paths files _inits)) = do
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
              Some retRepr <- translateType $ mkReturnType $
                              fieldType <$> results
              h <- liftIO' $
                mkHandle' ha (functionNameFromText nm) paramsRepr retRepr
              return $ insert_function nm (SomeHandle h) ns
            In (GenDecl _x specs) -> specsUpdNamespace specs ns
            _decl -> return ns)
    def decls

-- | Iterate through a list of specs to update a Namespace
-- value. Declare globals along the way. The initializer will give
-- them their initial values later on.
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
      tp' <- fromMaybe
             (case value of
                 Just v -> return $ typeOf' v
                 Nothing -> fail "specsUpdNamespace: expected value when\
                                 \type is missing") $ return <$> tp
      Some repr <- translateType tp'
      glob <- liftIO' $ Gen.freshGlobalVar ha name repr
      let goglob = GoGlobal glob $
            maybe (error "specsUpdNamespace: no zero value") id $
            zeroValue tp' repr
      -- Record the global in list of all globals.
      addGlobal goglob
      -- Insert it into the namespace.
      return $ insert_global name goglob ns

runSpec :: TypeRepr ret -> Translated Spec -> GoGenerator s ret ()
runSpec retRepr (TranslatedVarSpec names ty values) = do
  values' <- forM values $ runTranslatedExpr retRepr
  forM_ (zip names values) $ \(Ident _k name, TranslatedExpr gen) -> do
    Some (GoExpr _loc value) <- runSomeGoGenerator retRepr gen
    case ty of
      Just (TranslatedType (Some repr)) ->
        declareVar name $ asType repr value
      Nothing -> declareVar name value
runSpec _repr _spec = return ()

localNamespace :: TranslateM' Namespace
localNamespace = gets $ \(TransState { namespaces = ns
                                     , pkgName = name }) ->
                          fromJust $ HM.lookup name ns

fieldsType :: [Node a Field] -> Type
fieldsType = TupleType . fmap (typeToNameType . fieldType)

reslice :: Gen.Expr Go s (SliceType tp)
        -> Maybe (Gen.Expr Go s NatType)
        -> Maybe (Gen.Expr Go s NatType)
        -> Maybe (Gen.Expr Go s NatType)
        -> GoGenerator s ret (Gen.Expr Go s (SliceType tp))
reslice slice begin end cap =
  fail "reslice not yet implemented" -- TODO

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
           -> Maybe (Product (Node a) TranslateM Block) -- ^ body
           -> TranslateM' (C.AnyCFG Go)
mkFunction recv name params variadic results body =
  do
  fromMaybe (return ()) $
    fail "translate_alg FuncDecl: unexpected variadic parameter (should\
         \ have been desugared away)" <$> variadic
  params' <- mapM runTranslated $ maybeToList recv ++ params
  results' <- mapM runTranslated results
  globals <- ns_globals <$> localNamespace
  functions <- ns_funcs <$> localNamespace
  Just sng <- gets sng
  Just ha <- gets halloc
  pkgName <- gets pkgName
  bindFields params' $ \paramsRepr paramsGen ->
    bindResult results' $ \resultRepr resultGen -> do
    SomeHandle h <- case name of
      Just (Ident _k nm) -> return $ fromJust $ HM.lookup nm functions
      -- If there is no function name, allocate a new anonymous handle
      Nothing -> SomeHandle <$>
        (liftIO' $ mkHandle' ha (functionNameFromText "@anon")
          paramsRepr resultRepr)
    Refl <- failIfNotEqual paramsRepr (handleArgTypes h) $
            "translate_alg FuncDecl: checking argument types"
    Refl <- failIfNotEqual resultRepr (handleReturnType h) $
            "translate_alg FuncDecl: checking return type"
    (Gen.SomeCFG g, []) <- case body of
      Just (Pair body_node body') -> do
        modify $ \ts -> ts { retRepr = Some resultRepr }
        TranslatedBlock body_gen <- runTranslateM body'
        liftIO' $ Gen.defineFunction InternalPos sng h
          (\assignment ->
             (def, do
                 paramsGen $ fmapFC Gen.AtomExpr assignment
                 zeroValue' (fieldsType $ proj1 <$> results)
                   resultRepr >>= resultGen
                 buildLabelMap body_node -- build label map
                 runSomeGoGenerator resultRepr body_gen
                 -- Fail if no return.
                 Gen.reportError $
                   Gen.App (C.StringLit "missing return statement")))
      Nothing ->
        liftIO' $ Gen.defineFunction InternalPos sng h
        (\assignment -> (def :: GenState s, Gen.reportError $
                              Gen.App (C.StringLit "missing function body")))
    let g' = case toSSA g of C.SomeCFG g' -> C.AnyCFG g'
    addFunction ((\(Ident _k nm) ->
                    (pkgName, functionNameFromText nm)) <$> name) g'
    if maybe "" identName name == "main" then
      modify $ \ts -> ts { mainFunction = Just g' }
      else return ()
    return g'

-- | Construct a single CFG for initializing all translated packages.
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
  case toSSA g of
    C.SomeCFG g' -> do
      addFunction Nothing $ C.AnyCFG g'
      return $ C.SomeCFG g'

runBool :: GoGenerator s ret (SomeGoExpr s)
        -> GoGenerator s ret (Gen.Expr Go s BoolType)
runBool gen = do
  Some (GoExpr _loc b) <- gen
  return $ asType BoolRepr b

pushLoopLabels :: Gen.Label s -> Gen.Label s -> GoGenerator s ret ()
pushLoopLabels continue_lbl break_lbl =
  modify $ \gs ->
  let loop_label_map' = case current_label gs of
        Just (Ident _k label) ->
          HM.insert label (continue_lbl, break_lbl) $ loop_label_map gs
        Nothing -> loop_label_map gs in
    gs { loop_labels = (continue_lbl, break_lbl) : loop_labels gs
       , loop_label_map = loop_label_map' }
  

popLoopLabels :: GoGenerator s ret (Gen.Label s, Gen.Label s)
popLoopLabels = do
  lbls <- gets loop_labels
  case lbls of
    [] -> fail "popLoopLabels: empty label stack"
    ls : lbls' -> do
      modify $ \gs -> gs { loop_labels = lbls' }
      return ls

peekLoopLabels :: GoGenerator s ret (Gen.Label s, Gen.Label s)
peekLoopLabels = do
  lbls <- gets loop_labels
  case lbls of
    [] -> fail "peekLoopLabels: empty label stack"
    (continue_lbl, break_lbl) : _lbls ->
      return (continue_lbl, break_lbl)

peekContinueLabel :: GoGenerator s ret (Gen.Label s)
peekContinueLabel = fst <$> peekLoopLabels

peekBreakLabel :: GoGenerator s ret (Gen.Label s)
peekBreakLabel = snd <$> peekLoopLabels

buildLabelMap :: Node a Block -> GoGenerator s ret ()
buildLabelMap = cataM' alg
  where
    alg :: NodeF a (Const ()) tp -> GoGenerator s ret ()
    alg (LabeledStmt _x (Ident _k label) (Const map)) = do
      lbl <- Gen.newLabel
      -- trace ("allocating label for " ++ show label ++ ": " ++ show lbl) $
      modify $ \gs -> gs { label_map = HM.insert label lbl $ label_map gs }
    alg _node = return ()

getLabel :: Ident -> GoGenerator s ret (Gen.Label s)
getLabel (Ident _k label) = do
  lbl_map <- gets label_map
  case HM.lookup label lbl_map of
    Just lbl -> return lbl
    Nothing -> fail $ "getLabel: unbound label " ++ show label

getLoopLabels :: Ident -> GoGenerator s ret (Gen.Label s, Gen.Label s)
getLoopLabels (Ident _k label) = do
  lbl_map <- gets loop_label_map
  case HM.lookup label lbl_map of
    Just (continue_lbl, break_lbl) -> return (continue_lbl, break_lbl)
    Nothing -> -- trace (show lbl_map) $
      fail $ "getLoopLabels: unbound label " ++ show label

getContinueLabel :: Ident -> GoGenerator s ret (Gen.Label s)
getContinueLabel = (fst <$>) . getLoopLabels

getBreakLabel :: Ident -> GoGenerator s ret (Gen.Label s)
getBreakLabel = (snd <$>) . getLoopLabels
