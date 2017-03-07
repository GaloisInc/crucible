{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

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
import Data.Maybe ( catMaybes, maybeToList )
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
translateFunction :: forall h. Id SourceRange -- ^ Function name
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
                                            graphGenerator body (StructRepr retctx)))
     case toSSA g of
       C.SomeCFG gs -> return $ C.AnyCFG gs

-- | Bind the list of return values to both the function return type
-- in the crucible CFG and, if the return values are named, to
-- crucible registers mapped to the names. Like many functions here,
-- uses, continuation-passing style to construct heterogeneous lists
-- and work with type-level literals.
bindReturns :: ReturnList SourceRange
            -> (forall ctx. CtxRepr ctx -> (forall s ret rctx. Gen.Generator h s (TransState rctx) ret (Maybe (VariableAssignment s ctx))) -> a)
            -> a
bindReturns rlist f =
  let goNamed :: [NamedParameter SourceRange]
              -> (forall ctx. CtxRepr ctx -> (forall s ret rctx. Gen.Generator h s (TransState rctx) ret (VariableAssignment s ctx)) -> a)
              -> a
      goNamed [] k = k Ctx.empty (return Ctx.empty)
      goNamed (np@(NamedParameter _ (Id _ _ rname) _):ps) k =
        translateType {- TODO Abstract this: implicit parameter or generator state -}
           32 (fromRight $ getType np) (\t zv ->
                    goNamed ps (\ctx gen -> k (ctx Ctx.%> t)
                                 (do assign <- gen
                                     reg <- declareVar rname zv t
                                     return (assign Ctx.%> GoVarOpen reg))
                               ))
      goAnon :: [Type SourceRange] -> (forall ctx. CtxRepr ctx -> a) -> a
      goAnon [] k = k Ctx.empty
      goAnon (t:ts) k = case getType t of
        Right vt -> translateType 32 vt $ \t _ ->
          goAnon ts (\ctx -> k (ctx Ctx.%> t))
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
bindParams :: ParameterList SourceRange
           -> (forall ctx. CtxRepr ctx
               -> (forall s ret. Ctx.Assignment (Gen.Atom s) ctx -> Gen.Generator h s (TransState rctx) ret ())
               -> a)
           -> a
bindParams plist f =
  let go :: [NamedParameter SourceRange]
         -> (forall ctx. CtxRepr ctx
             -> (forall s ret. Ctx.Assignment (Gen.Atom s) ctx -> Gen.Generator h s (TransState rctx) ret ())
             -> a)
         -> a
      go []     k = k Ctx.empty (\_ -> return ())
      go (np@(NamedParameter _ (Id _ _ pname) _):ps) k =
        translateType {- TODO Abstract this: implicit parameter or generator state -}
        32 (fromRight $ getType np) $ \t zv -> go ps (\ctx f' -> k (ctx Ctx.%> t) 
                                                       (\a -> do f' (Ctx.init a)
                                                                 void $ declareVar pname (Gen.AtomExpr (Ctx.last a)) t))
  in case plist of
    NamedParameterList _ params mspread -> go (params ++ maybeToList mspread) f
    AnonymousParameterList _ _ _ -> error "Unexpected anonymous parameter list in a function definition"

-- | State of translation: the user state part of the Generator monad used here.
data TransState ctx s = TransState
  {lexenv :: !(HashMap Text (GoVarReg s)) -- ^ A mapping from variable names to registers
  ,enclosingLabels :: !(LabelStack s) -- ^ Labels lexically enclosing current source location
  ,returnSlots :: !(Maybe (VariableAssignment s ctx))
   -- ^ The list of registers that represent the components of the
   -- return value. Crucible functions can only have one return value,
   -- while Go functions can have multiple. To deal with that we
   -- multiplex return values in a struct that would store references
   -- to return values. The struct is going to be created from the
   -- variable assignment in this component of the user state.
  }

instance Default (TransState ctx s) where
  def = TransState {lexenv = HM.empty
                   ,enclosingLabels = LabelStack []
                   ,returnSlots = Nothing
                   }


newtype LabelStack s = LabelStack [Gen.Label s]

declareVar :: Text -> Gen.Expr s tp -> TypeRepr tp -> Gen.Generator h s (TransState rctx) ret (Gen.Reg s (ReferenceType tp))
declareVar name value t = do ref <- Gen.newReference value
                             reg <- Gen.newReg ref
                             St.modify' (\ts -> ts {lexenv = HM.insert name (GoVarReg t reg) (lexenv ts)})
                             return reg

graphGenerator :: [Statement SourceRange] -> TypeRepr ret -> Gen.Generator h s (TransState rctx) ret (Gen.Expr s ret)
graphGenerator body retTypeRepr =
  do rets <- catMaybes <$> mapM (\s -> translateStatement s retTypeRepr) body
     -- The following is going to be a fallthrough block that would
     -- never be reachable if all the exit paths in the function graph
     -- end with a return statement.
     Gen.reportError $ Gen.App (C.TextLit "Expected a return statement, but found none.")
  -- do Just Refl <- return $ testEquality retTypeRepr $ BVRepr (knownNat :: NatRepr 32)
  --    return $ App (C.BVLit (knownNat :: NatRepr 32) 12)

-- | Translates individual statements. This is where Go statement
-- semantics is encoded.
--
-- Note that only the returned expressions are returned from this
-- function.  The rest of the expressions are translated into
-- assignments that are handled internally by the 'Gen.Generator'
-- Monad.
translateStatement :: Statement SourceRange
                   -> TypeRepr ret
                   -> Gen.Generator h s (TransState rctx) ret (Maybe (Gen.Expr s ret))
translateStatement s retTypeRepr = case s of
  DeclStmt _ (VarDecl _ varspecs)     -> mapM_ translateVarSpec varspecs >> return Nothing
  DeclStmt _ (ConstDecl _ constspecs) -> mapM_ translateConstSpec constspecs >> return Nothing
  DeclStmt _ (TypeDecl _ _) ->
    -- type declarations are only reflected in type analysis results
    -- and type translations; they are not executable
    return Nothing
  ExpressionStmt _ expr -> withTranslatedExpression expr (const (return ())) >> return Nothing
    -- The number of expressions (|e|) in `lhs` and `rhs` should
    -- either be the same, or |rhs| = 1. Assigning multi-valued
    -- right-hand sides (|rhs|=1 and |lhs| > 1) is not currently
    -- supported.
    --
    -- Does this case have to handle assignments to named return variables?
  AssignStmt _ lhs Assignment rhs
    | F.length lhs == F.length rhs -> mapM_ translateAssignment (NE.zip lhs rhs) >> return Nothing
  EmptyStmt _ -> return Nothing
  _ -> error $ "Unsupported Go statement " ++ show s

fromRight :: Either a b -> b
fromRight (Right x) = x

translateAssignment :: (Expression SourceRange, Expression SourceRange)
                    -> Gen.Generator h s (TransState rctx) ret ()
translateAssignment (lhs, rhs) =
  withTranslatedExpression rhs $ \rhs'@(Gen.App rhsApp) ->
    case lhs of
      Name _ (Id _ _ ident) -> do
        lenv <- St.gets lexenv
        case HM.lookup ident lenv of
          Nothing -> error ("translateAssignment: Undefined identifier: " ++ show ident)
          Just (GoVarReg typeRep refReg)
            | Just Refl <- testEquality typeRep (C.appType rhsApp) -> do
                regExp <- Gen.readReg refReg
                Gen.writeReference regExp rhs'
            | otherwise -> error ("translateAssignment: type mismatch between lhs and rhs: " ++ show (lhs, rhs))
      _ -> error ("translateAssignment: unsupported LHS: " ++ show lhs)

translateVarSpec :: VarSpec SourceRange -> Gen.Generator h s (TransState rctx) ret ()
translateVarSpec s = case s of
  -- the rules for matching multiple variables and expressions are the
  -- same as for normal assignment expressions, with the addition of
  -- an empty list of initial values. We don't support multi-valued
  -- right-hand-sides yet.
  TypedVarSpec _ identifiers typ initialValues ->
    translateType 32 (fromRight $ getType typ) $
    \typeRepr zeroVal ->
      if null initialValues then
        -- declare variables with zero values;
        mapM_ (\ident -> declareIdent ident zeroVal typeRepr ) $ NE.toList identifiers
      else if NE.length identifiers /= length initialValues then error "The number of variable declared doesn't match the number of initial values provided. This is either a syntax error or a destructuring assignment. The latter is not supported."
           else void $ zipWithM bindExpr (NE.toList identifiers) initialValues
  UntypedVarSpec _ identifiers initialValues -> error "Untyped variable declarations will be supported in V4"
  where
    bindExpr ident value = do
      withTranslatedExpression value $ \expr@(Gen.App app) ->
        declareIdent ident expr (C.appType app)

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
                         -> (forall typ . Gen.Expr s typ -> Gen.Generator h s (TransState rctx) ret ())
                         -> Gen.Generator h s (TransState rctx) ret ()
withTranslatedExpression e k = case e of
  IntLit _ i ->
    case toTypeRepr `liftM` getType e of
      Right (ReprAndValue (BVRepr repr) _zero) -> k (Gen.App (C.BVLit repr i))
      _ -> error ("withTranslatedExpression: impossible literal type: " ++ show e)
  FloatLit _ d -> k (Gen.App (C.RationalLit (realToFrac d)))
  StringLit _ t -> k (Gen.App (C.TextLit t))
  Name _ (Id _ _ ident) -> do
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
    withTranslatedExpression e1 $ \e1'@(Gen.App a1) ->
      withTranslatedExpression e2 $ \e2'@(Gen.App a2) ->
        case (C.appType a1, C.appType a2) of
          (BVRepr w1, BVRepr w2)
            | Just Refl <- testEquality w1 w2
            , Just LeqProof <- isPosNat w1 ->
              case (getType e1, getType e2) of
                (Right (Int _ isSigned1), Right (Int _ isSigned2))
                  | isSigned1 && isSigned2 -> translateBitvectorBinaryOp k op Signed w1 e1' e2'
                  | not isSigned1 && not isSigned2 -> translateBitvectorBinaryOp k op Unsigned w1 e1' e2'
                _ -> error ("withTranslatedExpression: mixed signedness in binary operator: " ++ show (op, e1, e2))
          (BoolRepr, BoolRepr) -> translateBooleanBinaryOp e k op e1' e2'
          _ -> error ("withTranslatedExpression: unsupported operation: " ++ show (op, e1, e2))
  Conversion _ toType e ->
    withTranslatedExpression e $ \e' ->
      case getType toType of
        Right toType' -> translateConversion k (toTypeRepr toType') e'
        Left err -> error ("withTranslatedType: Unexpected conversion type: " ++ show (toType, err))
  _ -> error "Unsuported expression type"

translateConversion :: (forall toTyp . Gen.Expr s toTyp -> Gen.Generator h s (TransState rctx) ret ())
                    -> ReprAndValue
                    -> Gen.Expr s fromTyp
                    -> Gen.Generator h s (TransState rctx) ret ()
translateConversion k toType e@(Gen.App app) =
  case (C.appType app, toType) of
    (BoolRepr, ReprAndValue (BVRepr w) _) -> k (Gen.App (C.BoolToBV w e))
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
                         -> (Gen.Expr s tp -> a)
                         -> UnaryOp
                         -> Gen.Expr s tp
                         -> a
translateUnaryExpression e k op innerExpr@(Gen.App cexpr) =
  case (op, C.appType cexpr, exprTypeRepr e) of
    (Plus, _, _) -> k innerExpr
    (Minus, BVRepr w, Right (ReprAndValue (BVRepr w') zero))
      | Just Refl <- testEquality w w'
      , Just LeqProof <- isPosNat w ->
        k (Gen.App (C.BVSub w zero innerExpr))
    (Minus, _, _) -> error ("withTranslatedExpression: invalid argument to unary minus: " ++ show e)
    (Not, BoolRepr, Right (ReprAndValue BoolRepr _zero)) ->
      k (Gen.App (C.Not innerExpr))
    (Not, _, _) -> error ("withTranslatedExpression: invalid argument to not: " ++ show e)
    (Complement, BVRepr w, Right (ReprAndValue (BVRepr w') _zero))
      | Just Refl <- testEquality w w'
      , Just LeqProof <- isPosNat w ->
        k (Gen.App (C.BVNot w innerExpr))
    (Complement, _, _) -> error ("withTranslatedExpression: invalid argument to complement: " ++ show e)
    (Receive, _, _) -> error "withTranslatedExpression: unary Receive is not supported"
    (Address, _, _) -> error "withTranslatedExpression: addressof is not supported"
    (Deref, _, _) -> error "withTranslatedExpression: deref is not supported"

-- | This is a trivial wrapper around 'getType' and 'toTypeRepr' to
-- fix the Monad instance of 'getType' (inlining this without a type
-- annotation gives an ambiguous type variable error).
exprTypeRepr :: Expression SourceRange -> Either (SourceRange, String) ReprAndValue
exprTypeRepr e = toTypeRepr `liftM` getType e

-- | Declares an identifier; ignores blank identifiers. A thin wrapper
-- around `declareVar` that doesn't return the register
declareIdent :: Id a -> Gen.Expr s tp -> TypeRepr tp -> Gen.Generator h s (TransState rctx) ret ()
declareIdent ident value typ = case ident of
  BlankId _ -> return ()
  Id _ _ name -> void $ declareVar name value typ

translateConstSpec :: ConstSpec SourceRange -> Gen.Generator h s (TransState rctx) ret ()
translateConstSpec = undefined

-- | Translate a Go type to a Crucible type. This is where type semantics is encoded.
translateType :: forall a. Int {-Target architecture word size-}
              -> SemanticType
              -> (forall typ. TypeRepr typ -> (forall s. Gen.Expr s typ) -> a)
              -> a
translateType wordSize typ = typeAsRepr (instantiateWordSize wordSize typ)

instantiateWordSize :: Int -> SemanticType -> SemanticType
instantiateWordSize wordSize typ = case typ of
  Int Nothing signed -> Int (Just wordSize) signed
  _                  -> typ

typeAsRepr :: forall a. SemanticType
           -> (forall typ. TypeRepr typ -> (forall s. Gen.Expr s typ) -> a)
           -> a
typeAsRepr typ lifter = injectType (toTypeRepr typ)
   where injectType :: ReprAndValue -> a
         injectType (ReprAndValue repr zv) = lifter repr zv


-- | Compute the Crucible 'TypeRepr' and zero initializer value for a
-- given Go AST type
toTypeRepr :: SemanticType -> ReprAndValue
toTypeRepr typ = case typ of
  Int (Just width) _ -> case someNat (fromIntegral width) of
    Just (Some w) | Just LeqProof <- isPosNat w -> ReprAndValue (BVRepr w) (Gen.App (C.BVLit w 0))
    _ -> error $ unwords ["invalid integer width",show width]
  Float _width -> ReprAndValue RealValRepr (Gen.App (C.RationalLit (realToFrac (0::Int))))
  Boolean -> ReprAndValue BoolRepr (Gen.App (C.BoolLit False))
  Complex _width -> undefined
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

-- | The 'TypeRepr' and the zero initializer value for a given type
data ReprAndValue = forall typ. ReprAndValue (TypeRepr typ) (forall s. Gen.Expr s typ)
