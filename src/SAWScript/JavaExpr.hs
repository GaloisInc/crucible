{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns   #-}
module SAWScript.JavaExpr
  ( -- * Typechecking configuration.
    GlobalBindings(..)
  , MethodInfo(..)
  , TCConfig(..)
  , mkGlobalTCConfig
    -- * Typechecking type expressions.
  -- , tcType
    -- * Java Expressions
  , JavaExprF(..)
  , JavaExpr
  , thisJavaExpr
  , ppJavaExpr
  , jssTypeOfJavaExpr
  , isRefJavaExpr
  -- , tcJavaExpr
  -- , tcValueOfExpr
    -- * Logic expressions
  , LogicExpr(..)
  , typeOfLogicExpr
  , logicExprVarNames
  , logicExprJavaExprs
  , globalEval
  -- , tcLogicExpr
    -- * Mixed expressions
  , MixedExpr(..)
  -- , tcMixedExpr
  -- * Java types
  -- , ppASTJavaType
  -- , jssTypeOfASTJavaType
  -- * Actual type
  , JavaActualType(..)
  , isActualRef
  , jssTypeOfActual
  , logicTypeOfActual
  , isActualSubtype
  , ppActualType
  -- , tcActualType
  , MethodLocation (..)
  -- , BehaviorDecl (..)
  ) where

-- Imports {{{2

import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.Error (Error(..))
import Control.Monad.Trans
import Data.Int
import Data.List (intercalate)
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.Leijen

import Verinf.Symbolic
import qualified Verifier.Java.Codebase as JSS

import Verifier.SAW.Evaluator
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.TIMonad
import SAWScript.Options
import SAWScript.Utils

data MethodLocation
   = PC Integer
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

{-
data BehaviorDecl e
  = VarDecl Pos e e
    -- | Local binding within a method spec.
  -- | MethodLet Pos String Expr
  | MayAlias Pos [e]
    -- | Assert a given precondition is true when method is called.
  | AssertPred Pos e
  | AssertImp Pos e e
  | EnsureImp Pos e e
  | Modify Pos [e]
  | Return Pos e
  -- | MethodIf Pos Expr BehaviorDecl
  -- | MethodIfElse Pos Expr BehaviorDecl BehaviorDecl
  | Block [BehaviorDecl e]
  deriving (Show)
-}

-- Typecheck DagType {{{1

{-
-- | Convert expression type from AST into WidthExpr
tcheckExprWidth :: AST.ExprWidth -> WidthExpr
tcheckExprWidth = fn
  where fn (AST.WidthConst _ i  ) = constantWidth (Wx i)
        fn (AST.WidthVar   _ nm ) = varWidth nm
        fn (AST.WidthAdd   _ u v) = addWidth (fn u) (fn v)

-- | Convert expression type from AST into DagType.
-- Uses Executor monad for parsing record types.
tcType :: OpCache -> AST.ExprType -> DagType
tcType _ (AST.BitType       _)   = SymBool
tcType _ (AST.BitvectorType _ w) = SymInt (tcheckExprWidth w)
tcType oc (AST.Array _ w tp)     = SymArray (tcheckExprWidth w) (tcType oc tp)
tcType oc (AST.Record _ fields)  = SymRec def sub
  where names = [ nm | (_,nm,_) <- fields ]
        typeMap = Map.fromList [ (nm, tcType oc tp) | (_,nm,tp) <- fields ]
        def = getStructuralRecord oc (Set.fromList names)
        sub = emptySubst { shapeSubst = typeMap }
tcType _ (AST.ShapeVar _ v)        = SymShapeVar v

tcT :: AST.ExprType -> SawTI DagType
tcT tp = (\oc -> tcType oc tp) <$> gets (opCache . globalBindings)
-}

-- Typechecking configuration {{{1

-- | Context for resolving top level expressions.
data GlobalBindings s = GlobalBindings {
         codeBase      :: JSS.Codebase
       , gbOpts        :: Options
       , constBindings :: Map String (Value, SharedTerm s)
       }

data MethodInfo = MethodInfo {
         miClass :: JSS.Class
       , miMethod :: JSS.Method
       , miPC :: JSS.PC
       , miJavaExprType :: JavaExpr -> Maybe JSS.Type
       }

-- | Context for resolving expressions at the top level or within a method.
data TCConfig s = TCC {
         globalBindings :: GlobalBindings s
       , localBindings  :: Map String (MixedExpr s)
       , methodInfo     :: Maybe MethodInfo
       }

mkGlobalTCConfig :: GlobalBindings s -> Map String (LogicExpr s) -> (TCConfig s)
mkGlobalTCConfig globalBindings lb = do
  TCC { globalBindings
      , localBindings = Map.map LE lb
      , methodInfo = Nothing
      }

-- JavaExpr {{{1

data JavaExprF v
  = Local String JSS.LocalVariableIndex JSS.Type
  | InstanceField v JSS.FieldId
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable JavaExprF where
  fequal (Local _ i _)(Local _ j _) = i == j
  fequal (InstanceField xr xf) (InstanceField yr yf) = xf == yf && (xr == yr)
  fequal _ _ = False

instance CC.OrdFoldable JavaExprF where
  Local _ i _ `fcompare` Local _ i' _ = i `compare` i'
  Local _ _ _ `fcompare` _           = LT
  _           `fcompare` Local _ _ _ = GT
  InstanceField r1 f1 `fcompare` InstanceField r2 f2 =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r

instance CC.ShowFoldable JavaExprF where
  fshow (Local nm _ _) = nm
  fshow (InstanceField r f) = show r ++ "." ++ JSS.fieldIdName f

-- | Typechecked JavaExpr
type JavaExpr = CC.Term JavaExprF

instance Error JavaExpr where
  noMsg = error "noMsg called with TC.JavaExpr"

thisJavaExpr :: JSS.Class -> JavaExpr
thisJavaExpr cl = CC.Term (Local "this" 0 (JSS.ClassType (JSS.className cl)))

-- | Pretty print a Java expression.
ppJavaExpr :: JavaExpr -> String
ppJavaExpr (CC.Term exprF) =
  case exprF of
    Local nm _ _ -> nm
    InstanceField r f -> ppJavaExpr r ++ "." ++ JSS.fieldIdName f

-- | Returns JSS Type of JavaExpr
jssTypeOfJavaExpr :: JavaExpr -> JSS.Type
jssTypeOfJavaExpr (CC.Term exprF) =
  case exprF of
    Local _ _ tp      -> tp
    InstanceField _ f -> JSS.fieldIdType f

-- | Returns true if expression is a Boolean.
isRefJavaExpr :: JavaExpr -> Bool
isRefJavaExpr = JSS.isRefType . jssTypeOfJavaExpr

{-
tcJavaExpr :: AST.Expr -> TCConfig -> IO JavaExpr
tcJavaExpr e cfg = runTI cfg (tcJE e)

-- | Typecheck expression with form valueOf(args), returning java expression
-- inside args.
tcValueOfExpr :: AST.Expr -> TCConfig -> IO JavaExpr
tcValueOfExpr ast cfg = do
  expr <- runTI cfg (tcE ast)
  case expr of
    LE (JavaValue je _ _) -> return je
    _ -> error "internal: tcValueOfExpr given illegal expression"
-}

-- LogicExpr {{{1

-- | A type-checked expression which appears insider a global let binding,
-- method declaration, or rule term.
{-
data LogicExpr s
   = Apply Op [LogicExpr s]
   | IntLit Integer WidthExpr
   | Cns Value (SharedTerm s)
     -- | Refers to the logical value of a Java expression.  For scalars,
     -- this is the value of the scalar with the number of bits equal to
     -- the stack width.  For arrays, this is the value of the array.
     -- Other reference types are unsupported.
   | JavaValue JavaExpr JavaActualType (SharedTerm s)
   | Var String (SharedTerm s)
   deriving (Show)
-}

type LogicExpr s = SharedTerm s

-- | Return type of a typed expression.
typeOfLogicExpr :: LogicExpr s -> SharedTerm s
typeOfLogicExpr = undefined -- FIXME
{-
typeOfLogicExpr (Apply     op _) = opResultType op
typeOfLogicExpr (IntLit    _ tp) = SymInt tp
typeOfLogicExpr (Cns       _ tp) = tp
typeOfLogicExpr (JavaValue _ _ tp) = tp
typeOfLogicExpr (Var       _ tp) = tp
-}

-- | Return java expressions in logic expression.
logicExprJavaExprs :: LogicExpr s -> Set JavaExpr
logicExprJavaExprs = undefined --FIXME
  {- flip impl Set.empty
  where impl (Apply _ args) s = foldr impl s args
        impl (JavaValue e _ _) s = Set.insert e s
        impl _ s = s
        -}

-- | Returns names of variables appearing in typedExpr.
logicExprVarNames :: LogicExpr s -> Set String
logicExprVarNames = undefined --FIXME
  {- flip impl Set.empty
  where impl (Apply _ args) s = foldr impl s args
        impl (Var nm _) s = Set.insert nm s
        impl _ s = s -}

-- | Evaluate a ground typed expression to a constant value.
globalEval :: (String -> m r)
           -> TermSemantics m r
           -> LogicExpr s
           -> m r
globalEval varFn ts expr = eval expr
  where --TODO: flag error if op is undefined.
        eval = undefined -- FIXME
        {-
        eval (Apply op args) = tsApplyOp ts op (V.map eval (V.fromList args))
        eval (IntLit i (widthConstant -> Just w)) = 
          tsIntConstant ts w i
        eval (IntLit _ w) =
          error $ "internal: globalEval given non-constant width expression "
                    ++ ppWidthExpr w "."
        eval (Cns c tp) = tsConstant ts c tp -- FIXME
        eval (JavaValue _nm _ _tp) =
          error "internal: globalEval called with Java expression."
        eval (Var nm _tp) = varFn nm
        -}

-- | Internal utility for flipping arguments to binary logic expressions.
flipBinOpArgs :: LogicExpr s -> LogicExpr s
flipBinOpArgs e = undefined -- FIXME
{-
flipBinOpArgs (Apply o [a, b]) = Apply o [b, a]
flipBinOpArgs e = error $ "internal: flipBinOpArgs: received: " ++ show e
-}

-- | Typecheck a logic expression.
{-
tcLogicExpr :: AST.Expr -> TCConfig -> IO LogicExpr
tcLogicExpr e cfg = runTI cfg (tcLE e)
-}

-- MixedExpr {{{1

-- | A logic or Java expression.
data MixedExpr s
  = LE (LogicExpr s)
  | JE JavaExpr
  deriving (Show)

-- | Typecheck term as a mixed expression.
-- Guarantees that if a Java expression is returned, the actual type has
-- been defined.
{-
tcMixedExpr :: AST.Expr -> TCConfig -> IO MixedExpr
tcMixedExpr ast cfg = runTI cfg $ do
  me <- tcE ast
  case me of
    JE je -> getActualType (AST.exprPos ast) je >> return ()
    _ -> return ()
  return me
-}

-- Typechecking Java types {{{1

{-
jssTypeOfASTJavaType :: AST.JavaType -> JSS.Type
jssTypeOfASTJavaType tp =
  case tp of
    AST.BoolType _   -> JSS.BooleanType
    AST.ByteType _   -> JSS.ByteType
    AST.CharType _   -> JSS.CharType
    AST.DoubleType _ -> JSS.DoubleType
    AST.FloatType _  -> JSS.FloatType
    AST.IntType _    -> JSS.IntType
    AST.LongType _   -> JSS.LongType
    AST.ShortType _  -> JSS.ShortType
    AST.ArrayType eltTp _ -> JSS.ArrayType (jssTypeOfASTJavaType eltTp)
    AST.RefType _ names   -> JSS.ClassType (intercalate "/" names)

ppASTJavaType :: AST.JavaType -> Doc
ppASTJavaType tp =
  case tp of
    AST.BoolType _      -> text "boolean"
    AST.ByteType _      -> text "byte"
    AST.CharType _      -> text "char"
    AST.DoubleType _    -> text "double"
    AST.FloatType _     -> text "float"
    AST.IntType _       -> text "int"
    AST.LongType _      -> text "long"
    AST.ShortType _     -> text "short"
    AST.RefType _ nm    -> text (intercalate "." nm)
    AST.ArrayType etp l -> ppASTJavaType etp <> brackets (int l)
-}

-- | Identifies concrete type of a Java expression.
data JavaActualType
  = ClassInstance JSS.Class
  | ArrayInstance Int JSS.Type
  | PrimitiveType JSS.Type
  deriving (Show)

instance Eq JavaActualType where
  ClassInstance c1 == ClassInstance c2 = JSS.className c1 == JSS.className c2
  ArrayInstance l1 tp1 == ArrayInstance l2 tp2 = l1 == l2 && tp1 == tp2
  PrimitiveType tp1 == PrimitiveType tp2 = tp1 == tp2
  _ == _ = False

-- | Returns true if this represents a reference.
isActualRef :: JavaActualType -> Bool
isActualRef ClassInstance{} = True
isActualRef ArrayInstance{} = True
isActualRef PrimitiveType{} = False

-- | Returns Java symbolic simulator type that actual type represents.
jssTypeOfActual :: JavaActualType -> JSS.Type
jssTypeOfActual (ClassInstance x) = JSS.ClassType (JSS.className x)
jssTypeOfActual (ArrayInstance _ tp) = JSS.ArrayType tp
jssTypeOfActual (PrimitiveType tp) = tp

-- | Returns logical type of actual type if it is an array or primitive type.
logicTypeOfActual :: JSS.Type -> Maybe (SharedTerm s)
logicTypeOfActual = undefined -- FIXME
{-
logicTypeOfActual (ClassInstance _) = Nothing
logicTypeOfActual (ArrayInstance l tp) = Just $
  SymArray (constantWidth (Wx l)) 
           (SymInt (constantWidth (Wx (JSS.stackWidth tp))))
logicTypeOfActual (PrimitiveType tp) = Just $
  SymInt (constantWidth (Wx (JSS.stackWidth tp)))
-}

-- @isActualSubtype cb x y@ returns True if @x@ is a subtype of @y@.
isActualSubtype :: JSS.Codebase -> JavaActualType -> JavaActualType -> IO Bool
isActualSubtype cb (ArrayInstance lx ex) (ArrayInstance ly ey)
  | lx == ly = JSS.isSubtype cb ex ey
  | otherwise = return False
isActualSubtype cb x y 
  = JSS.isSubtype cb (jssTypeOfActual x) (jssTypeOfActual y)

ppActualType :: JavaActualType -> String
ppActualType (ClassInstance x) = JSS.slashesToDots (JSS.className x)
ppActualType (ArrayInstance l tp) = show tp ++ "[" ++ show l ++ "]"
ppActualType (PrimitiveType tp) = show tp

-- | Convert AST.JavaType into JavaActualType.
{-
tcActualType :: AST.JavaType -> TCConfig -> IO JavaActualType
tcActualType (AST.ArrayType eltTp l) cfg = do
  let pos = AST.javaTypePos eltTp
  unless (0 <= l && toInteger l < toInteger (maxBound :: Int32)) $ do
    let msg  = "Array length " ++ show l ++ " is invalid."
    throwIOExecException pos (ftext msg) ""
  let res = jssTypeOfASTJavaType eltTp
  runTI cfg $ checkIsSupportedType pos (JSS.ArrayType res)
  return $ ArrayInstance (fromIntegral l) res
tcActualType (AST.RefType pos names) cfg = do
  let cb = codeBase (globalBindings cfg)
   in ClassInstance <$> lookupClass cb pos (intercalate "/" names)
tcActualType tp cfg = do
  let pos = AST.javaTypePos tp
  let res = jssTypeOfASTJavaType tp
  runTI cfg $ checkIsSupportedType pos res
  return $ PrimitiveType res
-}
-- SawTI {{{1

type SawTI s = TI IO (TCConfig s)

{-
debugTI :: String -> SawTI s ()
debugTI msg = do os <- gets (gbOpts . globalBindings)
                 liftIO $ debugVerbose os $ putStrLn msg
-}

getMethodInfo :: SawTI s MethodInfo
getMethodInfo = do
  maybeMI <- gets methodInfo
  case maybeMI of
    Nothing -> error $ 
      "internal: getMethodInfo called when parsing outside a method declaration"
    Just p -> return p

-- | Check argument count matches expected length
checkArgCount :: Pos -> String -> [a] -> Int -> SawTI s ()
checkArgCount pos nm (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    typeErr pos $ ftext $ "Incorrect number of arguments to \'" ++ nm ++ "\'.  "
                        ++ show expectedCnt ++ " arguments were expected, but "
                        ++ show foundOpCnt ++ " arguments were found."

-- Core expression typechecking {{{1

-- | Typecheck expression as a Java expression.
{-
tcJE :: AST.Expr -> SawTI JavaExpr
tcJE astExpr = do
  r <- tcE astExpr
  case r of
    JE e -> return e
    LE _ -> 
     let msg = ftext $ "Encountered a logical expression where a Java expression was expected."
      in typeErr (AST.exprPos astExpr) msg
-}

{-
checkedGetIntType :: Pos -> JSS.Type -> SawTI DagType
checkedGetIntType pos javaType = do
  when (JSS.isRefType javaType) $ do
    let msg = "Encountered a Java expression denoting a reference where a logical expression is expected."
    typeErr pos (ftext msg)
  when (JSS.isFloatType javaType) $ do
    let msg = "Encountered a Java expression denoting a floating point value where a logical expression is expected."
    typeErr pos (ftext msg)
  return $ SymInt (constantWidth (Wx (JSS.stackWidth javaType)))
-}

{-
getActualType :: Pos -> JavaExpr -> SawTI s JavaActualType
getActualType p je = do
  mmi <- gets methodInfo
  case mmi of
    Nothing ->
      let msg = "The Java value \'" ++ ppJavaExpr je ++ "\' appears in a global context."
          res = "Java values may not be references outside method declarations."
       in typeErrWithR p (ftext msg) res
    Just mi -> do
      case miJavaExprType mi je of
        Nothing -> 
          let msg = "The Java value \'" ++ ppJavaExpr je ++ "\' has not been declared."
              res = "Please explicitly declare Java expressions before referring to them."
           in typeErrWithR p (ftext msg) res
        Just at -> return at
-}

-- | Typecheck expression as a logic expression.
{-
tcLE :: AST.Expr -> SawTI LogicExpr
tcLE ast = do
  r <- tcE ast
  case r of
    LE e -> return e
    JE e -> do
      -- Check that type of e is defined.
      at <- getActualType (AST.exprPos ast) e
      let javaType = jssTypeOfJavaExpr e
      dagType <- checkedGetIntType (AST.exprPos ast) javaType
      return $ JavaValue e at dagType
-}

-- | Verify that type is supported by SAWScript.
checkIsSupportedType :: Pos -> JSS.Type -> SawTI s ()
checkIsSupportedType pos tp =
  case tp of
    JSS.DoubleType -> throwFloatUnsupported
    JSS.FloatType  -> throwFloatUnsupported
    JSS.ArrayType eltType -> do
      when (JSS.isFloatType eltType) $ throwFloatUnsupported
      when (JSS.isRefType eltType) $ do
        let msg = "SAWScript does not support arrays of references."
         in typeErr pos (ftext msg)
    _ -> return ()
 where throwFloatUnsupported =
         let msg = "SAWScript does not support floating point types."
          in typeErr pos (ftext msg)

-- | Create a Java expression representing a local variable.
mkLocalVariable :: Pos -> JSS.LocalVariableTableEntry -> SawTI s JavaExpr
mkLocalVariable pos e = do
  let tp = JSS.localType e
  checkIsSupportedType pos tp
  return $ CC.Term $ Local (JSS.localName e) (JSS.localIdx e) tp

-- | Convert AST expression into expression.
{-
tcE :: AST.Expr -> SawTI MixedExpr
tcE (AST.ConstantInt p _) = typeErrWithR p msg rec
  where msg = ftext ("The use of constant literal requires a type-annotation")
        rec = "Please provide the bit-size of the constant with a type-annotation"
tcE (AST.ApplyExpr p nm _)
  | nm `elem` ["split", "trunc", "signedExt"] = typeErrWithR p msg rec
  where msg = ftext ("Use of operator '" ++ nm ++ "' requires a type-annotation.")
        rec = "Please provide an annotation for the surrounding expression."
tcE (AST.Var pos name) = do
  globals <- gets (constBindings . globalBindings)
  locals  <- gets localBindings
  mmi <- gets methodInfo
  let lookupLocal next = 
       case name `Map.lookup` locals of
         Just res -> return res
         Nothing -> next
      lookupGlobal next =
        case name `Map.lookup` globals of
          Just (c,tp) -> return $ LE (Cns c tp)
          Nothing -> next
      lookupJava next =
        case mmi of
          Nothing -> next
          Just MethodInfo { miMethod = m, miPC = pc } ->
            case JSS.lookupLocalVariableByName m pc name of
              Nothing -> next
              Just lte -> JE <$> mkLocalVariable pos lte
      throwUnknown = typeErr pos $ ftext $ "Unknown variable " ++ show name ++ "."
   in lookupLocal $ lookupJava $ lookupGlobal throwUnknown

tcE (AST.ConstantBool _ b) = return $ LE (Cns (mkCBool b) SymBool)
tcE (AST.MkArray p [])
  = typeErrWithR p (ftext ("Use of empty array-comprehensions requires a type-annotation")) "Please provide the type of the empty-array value"
tcE (AST.MkArray p (es@(_:_))) = do
  es' <- mapM tcLE es
  let go []                 = error "internal: impossible happened in tcE-non-empty-mkArray"
      go [(_, x)]           = return x
      go ((i, x):rs@((j, y):_))
        | x == y = go rs 
        | otherwise = mismatch p ("array elements " ++ show i ++ " and " ++ show j) x y
  t   <- go $ zip [(1::Int)..] $ map typeOfLogicExpr es'
  oc <- gets (opCache . globalBindings)
  return $ LE $ Apply (mkArrayOp oc (length es') t) es'
tcE (AST.GetArray pos arrayAst idxAst) = do
  array <- tcLE arrayAst
  idx <- tcLE idxAst
  case (typeOfLogicExpr array, typeOfLogicExpr idx) of
    (SymArray wl eltType, SymInt wi) ->
       return $ LE $ Apply (getArrayValueOp wl wi eltType) [array, idx]
    (arrayType, idxType) ->
      typeErr pos $ ftext $ "Unexpected types " ++ ppType arrayType ++ " and "
                              ++ ppType idxType ++ " to array access."
tcE (AST.TypeExpr pos (AST.ConstantInt posCnst i) astTp) = do
  tp <- tcT astTp
  let nonGround =
        typeErr pos $   text "The type" <+> text (ppType tp)
          <+> ftext "bound to literals must be a ground type."
  case tp of
    SymInt we@(widthConstant -> Just (Wx w)) -> do
      warnRanges posCnst tp i w
      return $ LE $ IntLit i we
    -- TODO: Support symbolic length integers.
    SymInt _      -> nonGround
    SymShapeVar _ -> nonGround
    _             -> typeErr pos $   text "Incompatible type" <+> text (ppType tp)
                                 <+> ftext "assigned to integer literal."
tcE (AST.TypeExpr _ (AST.ApplyExpr appPos "trunc" astArgs) astResType) = do
  args <- mapM tcLE astArgs
  checkArgCount appPos "trunc" args 1
  resType <- tcT astResType
  let argType = typeOfLogicExpr (head args)
  case (argType, resType) of
    (SymInt (widthConstant -> Just l),
     SymInt (widthConstant -> Just l')) | l' <= l -> do
        oc <- gets (opCache . globalBindings)
        return $ LE $ Apply (truncOp oc (constantWidth l) l') args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'trunc\'."
                                ++ " SAWScript currently requires that the argument is "
                                ++ "a ground type, and an explicit result type is given."
tcE (AST.TypeExpr _ (AST.ApplyExpr appPos "split" astArgs) astResType) = do
  args <- mapM tcLE astArgs
  checkArgCount appPos "split" args 1
  resType <- tcT astResType
  let argType = typeOfLogicExpr (head args)
  case (argType, resType) of
    (  SymInt (widthConstant -> Just wl)
     , SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)))
      | wl == l * w -> do
        oc <- gets (opCache . globalBindings)
        return $ LE $ Apply (splitOp oc l w) args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'split\'."
                                ++ " SAWScript currently requires that the argument is "
                                ++ "a ground type, and an explicit result type is given."
tcE (AST.TypeExpr p (AST.MkArray _ []) astResType) = do
  resType <- tcT astResType
  case resType of
    SymArray we _
      | Just (Wx 0) <- widthConstant we -> do
         oc <- gets (opCache . globalBindings)
         return $ LE $ Apply (mkArrayOp oc 0 resType) []
    _  -> unexpected p "Empty-array comprehension" "empty-array type" resType
tcE (AST.MkRecord _ flds) = do
   flds' <- mapM tcLE [e | (_, _, e) <- flds]
   let names = [nm | (_, nm, _) <- flds]
   oc <- gets (opCache . globalBindings)
   let def = getStructuralRecord oc (Set.fromList names)
   let fldTps = map typeOfLogicExpr flds'
   let sub = emptySubst { shapeSubst = Map.fromList $ names `zip` fldTps }
   return $ LE $ Apply (mkOp (recDefCtor def) sub) flds'
tcE (AST.TypeExpr p astExpr astResType) = do
  r <- tcE astExpr
  et <- case r of
          LE e -> return (typeOfLogicExpr e)
          JE e -> checkedGetIntType p (jssTypeOfJavaExpr e)
  resType <- tcT astResType
  when (et /= resType) $ mismatch p "type-annotation" et resType
  return r
tcE (AST.ApplyExpr p "valueOf" [jr]) = do
  sje <- tcJE jr
  unless (isRefJavaExpr sje) $ do
    let msg = "The Java value \'" ++ show sje ++ "\' does not denote a reference."
        res = "Only expressions refering to Java reference value may appear inside 'valueOf'."
     in typeErrWithR p (ftext msg) res
  at <- getActualType p sje
  case at of
    ArrayInstance l tp -> do
      let arrayTp = jssArrayDagType l tp
      return $ LE $ undefined -- JavaValue sje at arrayTp -- FIXME
    _  ->
      let msg = "The expression " ++ show sje ++ " does not refer to an array."
       in typeErrWithR p (ftext msg) ""

tcE (AST.ApplyExpr pos "valueOf" _) =
  let msg = ftext "Unexpected number of arguments to \"valueOf\"."
   in throwIOExecException pos msg ""
tcE (AST.ApplyExpr appPos "join" astArgs) = do
  args <- mapM tcLE astArgs
  checkArgCount appPos "join" args 1
  let argType = typeOfLogicExpr (head args)
  case argType of
    SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)) -> do
         oc <- gets (opCache . globalBindings)
         return $ LE $ Apply (joinOp oc l w) args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'join\'."
                                ++ " SAWScript currently requires that the argument is ground"
                                ++ " array of integers. "
tcE (AST.ApplyExpr pos nm astArgs) = do
  opBindings <- gets (opBindings . globalBindings)
  case Map.lookup nm opBindings of
    Nothing -> typeErrWithR pos (ftext ("Unknown operator '" ++ nm ++ "'.")) "Please check that the operator is correct."
    Just opDef -> do
      args <- mapM tcLE astArgs
      let defArgTypes = opDefArgTypes opDef
      checkArgCount pos nm args (V.length defArgTypes)
      let defTypes = V.toList defArgTypes
      let argTypes = map typeOfLogicExpr args
      case matchSubst (defTypes `zip` argTypes) of
        Nothing  -> do
          --debugTI $ show defTypes
          --debugTI $ show argTypes
          mismatchArgs pos ("in call to '" ++ nm ++ "'") argTypes defTypes
        Just sub -> do
          --debugTI $ "Making expression with operator " ++ opDefName opDef ++ " and substitution " ++  show sub
          return $ LE $ Apply (mkOp opDef sub) args
tcE (AST.NotExpr      p l)   = lift1Bool     p "not" bNotOp        l
tcE (AST.BitComplExpr p l)   = lift1Word     p "~"   iNotOp        l
tcE (AST.NegExpr      p l)   = lift1Word     p "-"   negOp         l
tcE (AST.MulExpr      p l r) = lift2WordEq   p "*"   (const mulOp)         l r
tcE (AST.SDivExpr     p l r) = lift2WordEq   p "/s"  (const signedDivOp)   l r
tcE (AST.SRemExpr     p l r) = lift2WordEq   p "%s"  (const signedRemOp)   l r
tcE (AST.PlusExpr     p l r) = lift2WordEq   p "+"   (const addOp)         l r
tcE (AST.SubExpr      p l r) = lift2WordEq   p "-"   (const subOp)         l r
tcE (AST.ShlExpr      p l r) = lift2Word     p "<<"  shlOp         l r
tcE (AST.SShrExpr     p l r) = lift2Word     p ">>s" shrOp         l r
tcE (AST.UShrExpr     p l r) = lift2Word     p ">>u" ushrOp        l r
tcE (AST.BitAndExpr   p l r) = lift2WordEq   p "&"   (const iAndOp)        l r
tcE (AST.BitOrExpr    p l r) = lift2WordEq   p "|"   (const iOrOp)         l r
tcE (AST.BitXorExpr   p l r) = lift2WordEq   p "^"   (const iXorOp)        l r
tcE (AST.AppendExpr   p l r) = lift2Word     p "#"   appendIntOp   l r
tcE (AST.EqExpr       p l r) = LE <$> lift2ShapeCmp p "=="  eqOp          l r
tcE (AST.IneqExpr     p l r) = (\e -> LE (Apply bNotOp [e])) <$> lift2ShapeCmp p "!="  eqOp l r
tcE (AST.SGeqExpr     p l r) = (LE . flipBinOpArgs) <$> lift2WordCmp  p ">=s" signedLeqOp   l r
tcE (AST.SLeqExpr     p l r) = LE                   <$> lift2WordCmp  p "<=s" signedLeqOp   l r
tcE (AST.SGtExpr      p l r) = (LE . flipBinOpArgs) <$> lift2WordCmp  p ">s"  signedLtOp    l r
tcE (AST.SLtExpr      p l r) = LE                   <$> lift2WordCmp  p "<s"  signedLtOp    l r
tcE (AST.UGeqExpr     p l r) = (LE . flipBinOpArgs) <$> lift2WordCmp  p ">=u" unsignedLeqOp l r
tcE (AST.ULeqExpr     p l r) = LE                   <$> lift2WordCmp  p "<=u" unsignedLeqOp l r
tcE (AST.UGtExpr      p l r) = (LE . flipBinOpArgs) <$> lift2WordCmp  p ">u"  unsignedLtOp  l r
tcE (AST.ULtExpr      p l r) = LE                   <$> lift2WordCmp  p "<u"  unsignedLtOp  l r
tcE (AST.AndExpr      p l r) = lift2Bool     p "&&"  bAndOp        l r
tcE (AST.OrExpr       p l r) = lift2Bool     p "||"  bOrOp         l r
tcE (AST.ImpExpr      p l r) = lift2Bool     p "==>" bImpliesOp    l r
tcE (AST.IteExpr      p t l r) = do
        --TODO: See if this can be fixed to support reference expressions.
        [t', l', r'] <- mapM tcLE [t, l, r]
        let [tt, lt, rt] = map typeOfLogicExpr [t', l', r']
        unless (tt == SymBool) $
          mismatch p "test expression of if-then-else" tt SymBool
        unless (lt == rt) $
          mismatch p "branches of if-then-else expression" lt rt
        return $ LE $ Apply (iteOp lt) [t', l', r']
tcE (AST.DerefField p e fName) = do
   me <- tcE e
   case me of
     JE lhs -> do
       cb <- gets (codeBase . globalBindings)
       f <- liftIO $ findField cb p (jssTypeOfJavaExpr lhs) fName
       checkIsSupportedType p (JSS.fieldIdType f)
       return $ JE $ CC.Term $ InstanceField lhs f
     LE e' ->
       --TODO: Simplify this method and move code to VerInf.
       case typeOfLogicExpr e' of
         rt@(SymRec recDef recSubst) -> do
           let fops = recDefFieldOps recDef
           case V.find (\op -> opDefName op == fName) fops of
             Nothing -> unexpected p "record field selection" ("record containing field " ++ show fName) rt
             Just fop -> return $ LE $ Apply (mkOp fop recSubst) [e']
         rt  -> unexpected p "record field selection" ("record containing field " ++ show fName) rt
tcE (AST.ThisExpr pos) = do
  MethodInfo { miClass = cl, miMethod = method } <- getMethodInfo
  when (JSS.methodIsStatic method) $
    typeErr pos (ftext "\'this\' is not defined on static methods.")
  return $ JE (thisJavaExpr cl)
tcE (AST.ArgExpr pos i) = do
  mi <- getMethodInfo
  let method = miMethod mi
  let params = V.fromList (JSS.methodParameterTypes method)
  -- N.B. We allow local specifications to refer to arguments.  They are
  -- essentially treated as free variables in the formula.  We may want to
  -- allow arbitrary names to be used in this way.
  -- when (miPC mi /= 0) $ do
  --  typeErr pos (ftext "Arguments are not defined at intermediate breakpoints.")
  -- Check that arg index is valid.
  unless (0 <= i && i < V.length params) $
    typeErr pos (ftext "Invalid argument index for method.")
  let tp = params V.! i
  checkIsSupportedType pos tp
  let idx = JSS.localIndexOfParameter method i
  return $ JE $ CC.Term $ (Local ("args[" ++ show i ++ "]") idx tp)
tcE (AST.LocalExpr pos idx) = do
  MethodInfo { miMethod = method, miPC = pc } <- getMethodInfo
  -- TODO: When pc == 0, throw a type error here as local variables only
  -- supported at intermediate breakpoints.
  when (pc == 0) $ do
    typeErr pos (ftext "Local variables are not defined at PC 0.")
  --TODO: Fix this method.
  case JSS.lookupLocalVariableByIdx method pc (fromInteger idx) of
    Nothing -> typeErr pos (ftext $ "Local variable " ++ show idx ++ " not found")
    -- TODO: check that the type exists
    Just e -> JE <$> mkLocalVariable pos e

lift1Bool :: Pos -> String -> Op -> AST.Expr -> SawTI MixedExpr
lift1Bool p nm o l = do
  l' <- tcLE l
  let lt = typeOfLogicExpr l'
  case lt of
    SymBool -> return $ LE (Apply o [l'])
    _       -> mismatch p ("argument to operator '" ++ nm ++ "'")  lt SymBool

lift1Word :: Pos -> String -> (WidthExpr -> Op) -> AST.Expr -> SawTI MixedExpr
lift1Word p nm opMaker l = do
  l' <- tcLE l
  let lt = typeOfLogicExpr l'
  case lt of
    SymInt wl -> return $ LE $ Apply (opMaker wl) [l']
    _         -> unexpected p ("Argument to operator '" ++ nm ++ "'") "word" lt

lift2Bool :: Pos -> String -> Op -> AST.Expr -> AST.Expr -> SawTI MixedExpr
lift2Bool p nm o l r = do
  l' <- tcLE l
  r' <- tcLE r
  let lt = typeOfLogicExpr l'
      rt = typeOfLogicExpr r'
  case (lt, rt) of
    (SymBool, SymBool) -> return $ LE $ Apply o [l', r']
    (SymBool, _      ) -> mismatch p ("second argument to operator '" ++ nm ++ "'") rt SymBool
    (_      , _      ) -> mismatch p ("first argument to operator '"  ++ nm ++ "'") lt SymBool

lift2Word :: Pos -> String -> (WidthExpr -> WidthExpr -> Op)
          -> AST.Expr -> AST.Expr -> SawTI MixedExpr
lift2Word = lift2WordGen False

lift2WordEq :: Pos -> String -> (WidthExpr -> WidthExpr -> Op)
            -> AST.Expr -> AST.Expr -> SawTI MixedExpr
lift2WordEq = lift2WordGen True

-- The bool argument says if the args should be of the same type
lift2WordGen :: Bool
             -> Pos
             -> String
             -> (WidthExpr -> WidthExpr -> Op)
             -> AST.Expr -> AST.Expr -> SawTI MixedExpr
lift2WordGen checkEq p nm opMaker l r = do
  l' <- tcLE l
  r' <- tcLE r
  let lt = typeOfLogicExpr l'
      rt = typeOfLogicExpr r'
  case (lt, rt) of
    (SymInt wl, SymInt wr) ->
      if not checkEq || wl == wr
        then return $ LE $ Apply (opMaker wl wr) [l', r']
        else mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt
    (SymInt _,  _)         -> unexpected p ("Second argument to operator '" ++ nm ++ "'") "word" rt
    (_       ,  _)         -> unexpected p ("First argument to operator '"  ++ nm ++ "'") "word" lt

lift2ShapeCmp :: Pos -> String -> (DagType -> Op)
              -> AST.Expr -> AST.Expr -> SawTI LogicExpr
lift2ShapeCmp p nm opMaker l r = do
  l' <- tcLE l
  r' <- tcLE r
  let lt = typeOfLogicExpr l'
      rt = typeOfLogicExpr r'
  unless (lt == rt) $ do
    mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt
  return $ Apply (opMaker lt) [l', r']

lift2WordCmp :: Pos -> String -> (WidthExpr -> Op) 
             -> AST.Expr -> AST.Expr -> SawTI LogicExpr
lift2WordCmp p nm opMaker l r = do
  l' <- tcLE l
  r' <- tcLE r
  let lt = typeOfLogicExpr l'
      rt = typeOfLogicExpr r'
  case (lt, rt) of
    (SymInt wl, SymInt wr) -> do
      unless (wl == wr) $
        mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt
      return $ Apply (opMaker wl) [l', r']
    (SymInt _,  _)         -> unexpected p ("Second argument to operator '" ++ nm ++ "'") "word" rt
    (_       ,  _)         -> unexpected p ("First argument to operator '"  ++ nm ++ "'") "word" lt
-}

{-
-- Only warn if the constant is beyond range for both signed/unsigned versions
-- This is less precise than it can be, but less annoying too..
warnRanges :: Pos -> DagType -> Integer -> Int -> SawTI ()
warnRanges pos tp i w'
  | violatesBoth = typeWarn pos $  ftext ("Constant \"" ++ show i ++ " : " ++ ppType tp ++ "\" will be subject to modular reduction.")
                                <$$> complain srange "a signed"    (if j >= 2^(w-1) then j - (2^w) else j)
                                <$$> complain urange "an unsigned" j
  | True         = return ()
  where violatesBoth = not (inRange srange || inRange urange)
        w :: Integer
        w = fromIntegral w'
        j :: Integer
        j = i `mod` (2^w)
        srange, urange :: (Integer, Integer)
        srange = (-(2^(w-1)), (2^(w-1))-1)
        urange = (0, 2^w-1)
        inRange (a, b) = i >= a && i <= b
        complain (a, b) ctx i' =    ftext ("In " ++ ctx ++ " context, range will be: [" ++ show a ++ ", " ++ show b ++ "]")
                                 <$$> ftext ("And the constant will assume the value " ++ show i')

-}
