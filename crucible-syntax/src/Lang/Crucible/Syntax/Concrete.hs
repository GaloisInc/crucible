{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Syntax.Concrete
  ( -- * Errors
    ExprErr(..)
  -- * Parsing and Results
  , ACFG(..)
  , top
  , cfgs
  -- * Rules for pretty-printing language syntax
  , printExpr
  )
where

import Prelude hiding (fail)

--import Data.Ratio
import Data.Semigroup (Semigroup(..))

import Control.Lens hiding (cons, backwards)
import Control.Applicative
import Control.Monad.Identity hiding (fail)
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.State.Class
import Control.Monad.State.Strict
import Control.Monad.Except hiding (fail)
import Control.Monad.Error.Class ()
import Control.Monad.Writer.Strict hiding ((<>))
import Control.Monad.Writer.Class ()

import Lang.Crucible.Types

import Data.Constraint (Dict(..))
import Data.Foldable
import Data.Functor
import qualified Data.Functor.Product as Functor
import Data.Maybe
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
import Data.Parameterized.Nonce ( NonceGenerator, Nonce
                                , freshNonce )
import qualified Data.Parameterized.Context as Ctx
import Data.List (elemIndex, nub, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V

import Lang.Crucible.Syntax.ExprParse hiding (SyntaxError)
import qualified Lang.Crucible.Syntax.ExprParse as SP

import What4.ProgramLoc
import What4.FunctionName
import What4.Symbol
import What4.Utils.MonadST

import Lang.Crucible.Syntax.SExpr (Syntax, pattern L, pattern A, toText, PrintRules(..), PrintStyle(..), syntaxPos, withPosFrom, showAtom)
import Lang.Crucible.Syntax.Atoms hiding (atom)

import Lang.Crucible.CFG.Reg hiding (globalName)
import Lang.Crucible.CFG.Expr

import Lang.Crucible.FunctionHandle

import Numeric.Natural ()


liftSyntaxParse :: (MonadError (ExprErr s) m, MonadST h m)
                  => SyntaxParse Atomic h a -> AST s -> m a
liftSyntaxParse p ast =
  liftST (syntaxParseST p ast) >>= \case
    Left e -> throwError (SyntaxParseError e)
    Right v -> return v

type AST s = Syntax Atomic



printExpr :: AST s -> Text
printExpr = toText (PrintRules rules)
  where rules (Kw Defun) = Just (Special 3)
        rules (Kw DefBlock) = Just (Special 1)
        rules (Kw Start) = Just (Special 1)
        rules (Kw Registers) = Just (Special 0)
        rules _ = Nothing

data E s t where
  EAtom  :: !(Atom s t) -> E s t
  EReg   :: !Position -> !(Reg s t) -> E s t
  EGlob  :: Closed t => !Position -> !(GlobalVar t) -> E s t
  EDeref :: !Position -> !(E s (ReferenceType t)) -> E s t
  EApp   :: !(App () (E s) t) -> E s t

data SomeExpr :: * -> * where
  SomeE :: TypeRepr t -> E s t -> SomeExpr s
  SomeOverloaded :: AST s -> Keyword -> [SomeExpr s] -> SomeExpr s
  SomeIntLiteral :: AST s -> Integer -> SomeExpr s

data SomeBVExpr :: * -> * where
  SomeBVExpr :: (1 <= w) => NatRepr w -> E s (BVType w) -> SomeBVExpr s

data ExprErr s where
  TrivialErr :: Position -> ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s
  DuplicateAtom :: Position -> AtomName -> ExprErr s
  DuplicateLabel :: Position -> LabelName -> ExprErr s
  DuplicateTypeArg :: Position -> TyVarName -> ExprErr s
  EmptyBlock :: Position -> ExprErr s
  NotGlobal :: Position -> AST s -> ExprErr s
  InvalidRegister :: Position -> AST s -> ExprErr s
  SyntaxParseError :: SP.SyntaxError Atomic -> ExprErr s

deriving instance Show (ExprErr s)

instance Semigroup (ExprErr s) where
  (<>) = mappend

instance Monoid (ExprErr s) where
  mempty = TrivialErr (OtherPos "mempty")
  mappend = Errs



kw :: MonadSyntax Atomic m => Keyword -> m ()
kw k = describe ("the keyword " <> showAtom (Kw k)) (atom (Kw k))

int :: MonadSyntax Atomic m => m Integer
int = sideCondition "integer literal" numeric atomic
  where numeric (Int i) = Just i
        numeric _ = Nothing


labelName :: MonadSyntax Atomic m => m LabelName
labelName = sideCondition "label name" lbl atomic
  where lbl (Lbl l) = Just l
        lbl _ = Nothing

regName :: MonadSyntax Atomic m => m RegName
regName = sideCondition "register name" reg atomic
  where reg (Rg rn) = Just rn
        reg _ = Nothing

globalName :: MonadSyntax Atomic m => m GlobalName
globalName = sideCondition "name of global variable" glob atomic
  where glob (Gl x) = Just x
        glob _ = Nothing


rational :: MonadSyntax Atomic m => m Rational
rational = sideCondition "rational number literal" numeric atomic
  where numeric (Rat r) = Just r
        numeric _ = Nothing


string :: MonadSyntax Atomic m => m Text
string = sideCondition "string literal" stringy atomic
  where stringy (StrLit t) = Just t
        stringy _ = Nothing

atomName :: MonadSyntax Atomic m => m AtomName
atomName = sideCondition "Crucible atom literal" isCAtom atomic
  where isCAtom (At a) = Just a
        isCAtom _ = Nothing

typeVarName :: MonadSyntax Atomic m => m TyVarName
typeVarName = sideCondition "type variable" isTV atomic
  where isTV (TyV x) = Just x
        isTV _ = Nothing

bool :: MonadSyntax Atomic m => m  Bool
bool = sideCondition "Boolean literal" isBool atomic
  where isBool (Bool b) = Just b
        isBool _ = Nothing

funName :: MonadSyntax Atomic m => m  FunctionName
funName = functionNameFromText <$> sideCondition "function name literal" isFn atomic
  where isFn (Fn (FunName n)) = Just n
        isFn _ = Nothing

toCtx :: forall f . [Some f] -> Some (Ctx.Assignment f)
toCtx fs = toCtx' (reverse fs)
  where toCtx' :: [Some f] -> Some (Ctx.Assignment f)
        toCtx' [] = Some Ctx.empty
        toCtx' (Some x : (toCtx' -> Some xs)) =
          Some $ Ctx.extend xs x

unary :: MonadSyntax Atomic m => Keyword -> m a -> m a
unary k p = followedBy (kw k) (commit *> cons p emptyList) <&> fst

binary :: MonadSyntax Atomic m => Keyword -> m a -> m b -> m (a, b)
binary k p1 p2 = followedBy (kw k) (commit *> cons p1 (cons p2 emptyList)) <&> \(x, (y, ())) -> (x, y)


mkFunRepr :: [Some TypeRepr] -> Some TypeRepr -> Some TypeRepr
mkFunRepr (toCtx -> Some doms) (Some ran) = Some $ FunctionHandleRepr doms ran

repUntilLast :: MonadSyntax Atomic m => m a -> m ([a], a)
repUntilLast sp = describe "zero or more followed by one" $ repUntilLast' sp
  where repUntilLast' p =
          (cons p emptyList <&> \(x, ()) -> ([], x)) <|>
          (cons p (repUntilLast' p) <&> \(x, (xs, lst)) -> (x:xs, lst))

isBaseType :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) => m (Some BaseTypeRepr)
isBaseType =
  describe "base type" $
  do Some tp <- isType
     case asBaseType tp of
       NotBaseType -> empty
       AsBaseType bt -> return (Some bt)

data PosNat =
  forall w. (1 <= w) => PosNat (NatRepr w)

posNat :: MonadSyntax Atomic m => m PosNat
posNat =
   do i <- sideCondition "positive nat literal" checkPosNat int
      maybe empty return $ do Some x <- someNat i
                              LeqProof <- isPosNat x
                              return $ PosNat x
  where checkPosNat i | i > 0 = Just i
        checkPosNat _ = Nothing

natRepr :: MonadSyntax Atomic m => m (Some NatRepr)
natRepr =
   do i <- sideCondition "nat literal" checkNonneg int
      case someNat i of
        Just sx -> return sx
        Nothing -> empty

  where checkNonneg i | i >= 0 = Just i
        checkNonneg _ = Nothing

isType :: forall h s m . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) => m (Some TypeRepr)
isType =
  describe "type" $ call
    (variable <|> atomicType <|> vector <|> ref <|> bv <|> fun <|> maybeT <|> variant)

  where
    atomicType =
      later $ describe "atomic type" $
        asum [ kw AnyT         $> Some AnyRepr
             , kw UnitT        $> Some UnitRepr
             , kw BoolT        $> Some BoolRepr
             , kw NatT         $> Some NatRepr
             , kw IntegerT     $> Some IntegerRepr
             , kw RealT        $> Some RealValRepr
             , kw ComplexRealT $> Some ComplexRealRepr
             , kw CharT        $> Some CharRepr
             , kw StringT      $> Some StringRepr
             ]
    vector = unary VectorT isType <&> \(Some t) -> Some (VectorRepr t)
    ref    = unary RefT isType <&> \(Some t) -> Some (ReferenceRepr t)
    bv :: MonadSyntax Atomic m => m  (Some TypeRepr)
    bv     = do (Some len) <- unary BitvectorT (sideCondition "natural number" someNat int)
                describe "positive number" $
                  case testLeq (knownNat :: NatRepr 1) len of
                    Nothing -> empty
                    Just LeqProof -> return $ Some $ BVRepr len

    fun :: m (Some TypeRepr)
    fun = cons (kw FunT) (repUntilLast isType) <&> \((), (args, ret)) -> mkFunRepr args ret

    maybeT = unary MaybeT isType <&> \(Some t) -> Some (MaybeRepr t)

    variant :: m (Some TypeRepr)
    variant = cons (kw VariantT) (rep isType) <&> \((), toCtx -> Some tys) -> Some (VariantRepr tys)

    variable :: m (Some TypeRepr)
    variable =
      describe "known type variable" $
      do x <- typeVarName
         ctx <- use stxTypeArgs
         case elemIndex x ctx of
           Just ix ->
             later $
             describe "type variable index" $
             case someNat $ toInteger ix of
               Nothing -> empty
               Just (Some ixRepr) -> return $ Some $ VarRepr ixRepr
           Nothing -> empty



someExprType :: SomeExpr s -> Maybe (Some TypeRepr)
someExprType (SomeE tpr _) = Just (Some tpr)
someExprType _ = Nothing


findJointType :: Maybe (Some TypeRepr) -> [SomeExpr s] -> Maybe (Some TypeRepr)
findJointType = foldr (\y x -> f x (someExprType y))
 where
 f Nothing y    = y
 f x@(Just _) _ = x

evalOverloaded :: forall m s t. MonadSyntax Atomic m => AST s -> TypeRepr t -> Keyword -> [SomeExpr s] -> m (E s t)
evalOverloaded ast tpr k = withFocus ast .
  case (k, tpr) of
    (Plus, NatRepr)     -> nary NatAdd    (NatLit 0)
    (Plus, IntegerRepr) -> nary IntAdd    (IntLit 0)
    (Plus, RealValRepr) -> nary RealAdd   (RationalLit 0)
    (Plus, BVRepr w)    -> nary (BVAdd w) (BVLit w 0)

    (Times, NatRepr)     -> nary NatMul    (NatLit 1)
    (Times, IntegerRepr) -> nary IntMul    (IntLit 1)
    (Times, RealValRepr) -> nary RealMul   (RationalLit 1)
    (Times, BVRepr w)    -> nary (BVMul w) (BVLit w 1)

    (Minus, NatRepr)     -> bin NatSub
    (Minus, IntegerRepr) -> bin IntSub
    (Minus, RealValRepr) -> bin RealSub
    (Minus, BVRepr w)    -> bin (BVSub w)

    (Div, NatRepr)       -> bin NatDiv
    (Div, IntegerRepr)   -> bin IntDiv
    (Div, RealValRepr)   -> bin RealDiv
    (Div, BVRepr w)      -> bin (BVUdiv w)

    (Mod, NatRepr)       -> bin NatMod
    (Mod, IntegerRepr)   -> bin IntMod
    (Mod, RealValRepr)   -> bin RealMod
    (Mod, BVRepr w)      -> bin (BVUrem w)

    (Negate, IntegerRepr) -> u IntNeg
    (Negate, RealValRepr) -> u RealNeg
    (Negate, BVRepr w)    -> u (BVNeg w)

    (Abs, IntegerRepr)   -> u IntAbs

    _ -> \_ -> later $ describe ("operation at type " <> T.pack (show tpr)) $ empty
 where
 u :: (E s t -> App () (E s) t) -> [SomeExpr s] -> m (E s t)
 u f [x] = EApp . f <$> evalSomeExpr tpr x
 u _ _ = later $ describe "one argument" $ empty

 bin :: (E s t -> E s t -> App () (E s) t) -> [SomeExpr s] -> m (E s t)
 bin f [x,y] = EApp <$> (f <$> evalSomeExpr tpr x <*> evalSomeExpr tpr y)
 bin _ _ = later $ describe "two arguments" $ empty

 nary :: (E s t -> E s t -> App () (E s) t) -> App () (E s) t -> [SomeExpr s] -> m (E s t)
 nary _ z []     = return $ EApp z
 nary _ _ [x]    = evalSomeExpr tpr x
 nary f _ (x:xs) = go f <$> evalSomeExpr tpr x <*> mapM (evalSomeExpr tpr) xs

 go f x (y:ys) = go f (EApp $ f x y) ys
 go _ x []     = x


evalSomeExpr :: MonadSyntax Atomic m => TypeRepr t -> SomeExpr s -> m (E s t)
evalSomeExpr tpr (SomeE tpr' e)
  | Just Refl <- testEquality tpr tpr' = return e
  | otherwise = later $ describe ("matching types (" <> T.pack (show tpr)
                                  <> " /= " <> T.pack (show tpr') <> ")") empty
evalSomeExpr tpr (SomeOverloaded ast k args) = evalOverloaded ast tpr k args
evalSomeExpr tpr (SomeIntLiteral ast i) = evalIntLiteral ast tpr i

applyOverloaded ::
  MonadSyntax Atomic m => AST s -> Keyword -> Maybe (Some TypeRepr) -> [SomeExpr s] -> m (SomeExpr s)
applyOverloaded ast k mtp args =
  case findJointType mtp args of
    Nothing -> return $ SomeOverloaded ast k args
    Just (Some tp) -> SomeE tp <$> evalOverloaded ast tp k args

evalIntLiteral :: MonadSyntax Atomic m => AST s -> TypeRepr tpr -> Integer -> m (E s tpr)
evalIntLiteral _ NatRepr i | i >= 0 = return $ EApp $ NatLit (fromInteger i)
evalIntLiteral _ IntegerRepr i = return $ EApp $ IntLit i
evalIntLiteral _ RealValRepr i = return $ EApp $ RationalLit (fromInteger i)
evalIntLiteral ast tpr _i =
  withFocus ast $ later $ describe ("literal " <> T.pack (show tpr) <> " value") empty

forceSynth :: MonadSyntax Atomic m => SomeExpr s -> m (Pair TypeRepr (E s))
forceSynth (SomeE tp e) = return $ Pair tp e
forceSynth (SomeOverloaded ast _ _) =
  withFocus ast $ later (describe "unambiguous expression (add type annotation to disambiguate)" empty)
forceSynth (SomeIntLiteral ast _) =
  withFocus ast $ later (describe "unambiguous numeric literal (add type annotation to disambiguate)" empty)

synth :: forall m h s.
  (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) => m (Pair TypeRepr (E s))
synth = forceSynth =<< synth'

synth' :: forall m h s.
  (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) => m (SomeExpr s)
synth' = synthExpr Nothing




synthExpr :: forall m h s . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
       => Maybe (Some TypeRepr) -> m (SomeExpr s)
synthExpr typeHint =
  describe "expression" $
    call (the <|> crucibleAtom <|> regRef <|> globRef <|> deref <|>
     bvExpr <|>
     naryBool And_ And True <|> naryBool Or_ Or False <|> naryBool Xor_ BoolXor False <|>
     unaryArith Negate <|> unaryArith Abs <|>
     naryArith Plus <|> binaryArith Minus <|> naryArith Times <|> binaryArith Div <|> binaryArith Mod <|>
     unitCon <|> boolLit <|> stringLit <|> funNameLit <|>
     notExpr <|> equalp <|> lessThan <|> lessThanEq <|>
     toAny <|> fromAny <|> stringAppend <|> showExpr <|>
     just <|> nothing <|> fromJust_ <|> injection <|> projection <|>
     vecLit <|> vecCons <|> vecRep <|> vecLen <|> vecEmptyP <|> vecGet <|> vecSet <|>
     ite <|>  intLit <|> rationalLit <|> intp <|>
     unaryBV BVNonzero_ BVNonzero <|> compareBV BVCarry_ BVCarry <|>
     compareBV BVSCarry_ BVSCarry <|> compareBV BVSBorrow_ BVSBorrow <|>
     compareBV Slt BVSlt <|> compareBV Sle BVSle <|>
     inst)

     -- Syntactic constructs still to add (see issue #74)

     -- BvToInteger, SbvToInteger, BvToNat
     -- MkStruct, GetStruct, SetStruct
     -- NatToInteger, IntegerToReal
     -- RealRound, RealFloor, RealCeil
     -- IntegerToBV, RealToNat

     -- EmptyWordMap, InsertWordMap, LookupWordMap, LookupWordMapWithDefault
     -- EmptyStringMap, LookupStringMapEntry, InsertStringMapEntry
     -- SymArrayLookup, SymArrayUpdate
     -- Complex, RealPart, ImagPart
     -- IsConcrete
     -- Closure
     -- All the floating-point operations
     -- What to do about RollRecursive, UnrollRecursive?
     -- AddSideCondition????
     -- BVUndef ????

  where
    the :: m (SomeExpr s)
    the = do describe "type-annotated expression" $
               kw The `followedBy`
                 (depCons isType $
                  \(Some t) ->
                    do (e, ()) <- cons (check t) emptyList
                       return $ SomeE t e)

    okAtom theAtoms x =
      case Map.lookup x theAtoms of
        Nothing -> Nothing
        Just (Pair t anAtom) -> Just $ SomeE t (EAtom anAtom)

    regRef :: m (SomeExpr s)
    regRef =
      do Pair t r <- regRef'
         loc <- position
         return (SomeE t (EReg loc r))

    deref :: m (SomeExpr s)
    deref =
      do let newhint = case typeHint of
                         Just (Some t) -> Just (Some (ReferenceRepr t))
                         _ -> Nothing
         unary Deref (forceSynth =<< synthExpr newhint) >>= \case
           Pair (ReferenceRepr t') e ->
             do loc <- position
                return (SomeE t' (EDeref loc e))
           Pair notRef _ -> later $ describe ("reference type (provided a "<> T.pack (show notRef) <>")") empty

    globRef :: m (SomeExpr s)
    globRef =
      do GlobalInfo t g <- globRef'
         loc <- position
         return (SomeE t (EGlob loc g))

    crucibleAtom :: m (SomeExpr s)
    crucibleAtom =
      do theAtoms <- use stxAtoms
         sideCondition "known atom" (okAtom theAtoms) atomName

    unitCon = describe "unit constructor" (emptyList $> SomeE UnitRepr (EApp EmptyApp))

    boolLit = bool <&> SomeE BoolRepr . EApp . BoolLit

    stringLit = string <&> SomeE StringRepr . EApp . TextLit

    intLit =
      do ast <- anything
         case typeHint of
           Just (Some tpr) -> SomeE tpr <$> (evalIntLiteral ast tpr =<< int)
           Nothing         -> SomeIntLiteral ast <$> int

    rationalLit = rational <&> SomeE RealValRepr . EApp . RationalLit

    naryBool k f u =
      do ((), args) <- cons (kw k) (rep (check BoolRepr))
         case args of
           [] -> return $ SomeE BoolRepr $ EApp (BoolLit u)
           (x:xs) -> go x xs

      where
      go x [] = return $ SomeE BoolRepr x
      go x (y:ys) = go (EApp $ f x y) ys

    bvExpr :: m (SomeExpr s)
    bvExpr =
      do let nathint = case typeHint of Just (Some (BVRepr w)) -> NatHint w; _ -> NoHint
         SomeBVExpr w x <- synthBV nathint
         return $ SomeE (BVRepr w) x

    intp =
      do e <- unary Integerp (check RealValRepr)
         return $ SomeE BoolRepr $ EApp $ RealIsInteger e

    funNameLit =
      do fn <- funName
         fh <- use $ stxFunctions . at fn
         describe "known function name" $
           case fh of
             Nothing -> empty
             Just (FunctionHeader _ funArgs ret handle _) ->
               return $ SomeE (FunctionHandleRepr (argTypes funArgs) ret) (EApp $ HandleLit handle)
             Just (PolyFunctionHeader _ _ funArgs ret handle _) ->
               return $ SomeE (PolyFnRepr (argTypes funArgs) ret) (EApp $ PolyHandleLit handle)

    notExpr =
      do e <- describe "negation expression" $ unary Not_ (check BoolRepr)
         return $ SomeE BoolRepr $ EApp $ Not e

    matchingExprs ::
      Maybe (Some TypeRepr) -> SomeExpr s -> SomeExpr s ->
      (forall tp. TypeRepr tp -> E s tp -> E s tp -> m a) ->
      m a
    matchingExprs h e1 e2 k =
      case findJointType h [e1,e2] of
        Just (Some tp) ->
          do e1' <- evalSomeExpr tp e1
             e2' <- evalSomeExpr tp e2
             k tp e1' e2'
        Nothing ->
          later $ describe ("type annotation required to disambiguate types") empty

    equalp :: m (SomeExpr s)
    equalp =
      do (e1, e2) <- describe "equality test" $ binary Equalp synth' synth'
         matchingExprs Nothing e1 e2 $ \tp e1' e2' ->
          case tp of
            ReferenceRepr rtp ->
              return $ SomeE BoolRepr $ EApp $ ReferenceEq rtp e1' e2'
            (asBaseType -> AsBaseType bt) ->
              return $ SomeE BoolRepr $ EApp $ BaseIsEq bt e1' e2'
            _ ->
              later $ describe ("a base type or reference type (got " <> T.pack (show tp) <> ")") empty

    compareBV ::
      Keyword ->
      (forall w. (1 <= w) => NatRepr w -> E s (BVType w) -> E s (BVType w) -> App () (E s) BoolType) ->
      m (SomeExpr s)
    compareBV k f =
      do (e1, e2) <- describe "bitvector compaprison" $ binary k synth' synth'
         matchingExprs Nothing e1 e2 $ \tp e1' e2' ->
           case tp of
             BVRepr w ->
               return $ SomeE BoolRepr $ EApp $ f w e1' e2'
             _ ->
               later $ describe ("a bitvector type (got " <> T.pack (show tp) <> ")") empty

    lessThan :: m (SomeExpr s)
    lessThan =
      do (e1, e2) <- describe "less-than test" $ binary Lt synth' synth'
         matchingExprs Nothing e1 e2 $ \tp e1' e2' ->
           case tp of
             NatRepr     -> return $ SomeE BoolRepr $ EApp $ NatLt e1' e2'
             IntegerRepr -> return $ SomeE BoolRepr $ EApp $ IntLt e1' e2'
             RealValRepr -> return $ SomeE BoolRepr $ EApp $ RealLt e1' e2'
             BVRepr w    -> return $ SomeE BoolRepr $ EApp $ BVUlt w e1' e2'
             other ->
               describe ("valid comparison type (got " <> T.pack (show other) <> ")") empty

    lessThanEq :: m (SomeExpr s)
    lessThanEq =
      do (e1, e2) <- describe "less-than-or-equal test" $ binary Le synth' synth'
         matchingExprs Nothing e1 e2 $ \tp e1' e2' ->
           case tp of
             NatRepr     -> return $ SomeE BoolRepr $ EApp $ NatLe e1' e2'
             IntegerRepr -> return $ SomeE BoolRepr $ EApp $ IntLe e1' e2'
             RealValRepr -> return $ SomeE BoolRepr $ EApp $ RealLe e1' e2'
             BVRepr w    -> return $ SomeE BoolRepr $ EApp $ BVUle w e1' e2'
             other ->
               describe ("valid comparison type (got " <> T.pack (show other) <> ")") empty

    naryArith :: Keyword -> m (SomeExpr s)
    naryArith k =
      do ast <- anything
         args <- followedBy (kw k) (commit *> (rep (synthExpr typeHint)))
         applyOverloaded ast k typeHint args

    binaryArith :: Keyword -> m (SomeExpr s)
    binaryArith k =
      do ast <- anything
         (x, y) <- binary k (synthExpr typeHint) (synthExpr typeHint)
         applyOverloaded ast k typeHint [x,y]

    unaryArith :: Keyword -> m (SomeExpr s)
    unaryArith k =
      do ast <- anything
         x <- unary k (synthExpr typeHint)
         applyOverloaded ast k typeHint [x]

    unaryBV ::
      Keyword ->
      (forall w. (1 <= w) => NatRepr w -> E s (BVType w) -> App () (E s) BoolType) ->
      m (SomeExpr s)
    unaryBV k f =
      do Pair t x <- unary k synth
         case t of
           BVRepr w -> return $ SomeE BoolRepr $ EApp $ f w x
           _ -> later $ describe "bitvector argument" empty

    inst :: m (SomeExpr s)
    inst =
      followedBy (kw Inst) $
      depConsCond synth $ \ (Pair t e) ->
      case t of
        PolyFnRepr args ret ->
          do commit
             Some typeArgs <- typeArguments
             return $ Right $
               SomeE (FunctionHandleRepr (instantiate typeArgs args) (instantiate typeArgs ret)) $
               EApp $ PolyInstantiate t e typeArgs
        other ->
          return $ Left $ "polymorphic function, got " <> T.pack (show other)

    just :: m (SomeExpr s)
    just =
      do let newhint = case typeHint of
                         Just (Some (MaybeRepr t)) -> Just (Some t)
                         _ -> Nothing
         Pair t x <- unary Just_ (forceSynth =<< synthExpr newhint)
         return $ SomeE (MaybeRepr t) $ EApp $ JustValue t x

    nothing :: m (SomeExpr s)
    nothing =
      do Some t <- unary Nothing_ isType
         return $ SomeE (MaybeRepr t) $ EApp $ NothingValue t
      <|>
      kw Nothing_ *>
      case typeHint of
        Just (Some (MaybeRepr t)) ->
          return $ SomeE (MaybeRepr t) $ EApp $ NothingValue t
        Just (Some t) ->
          later $ describe ("value of type " <> T.pack (show t)) empty
        Nothing ->
          later $ describe ("unambiguous nothing value") empty

    fromJust_ :: m (SomeExpr s)
    fromJust_ =
      do let newhint = case typeHint of
                         Just (Some t) -> Just (Some (MaybeRepr t))
                         _ -> Nothing
         describe "coercion from Maybe (fromJust-expression)" $
           followedBy (kw FromJust) $
           depCons (forceSynth =<< synthExpr newhint) $ \(Pair t e) ->
             case t of
               MaybeRepr elemT ->
                 depCons (check StringRepr) $ \str ->
                   do emptyList
                      return $ SomeE elemT $ EApp $ FromJustValue elemT e str
               _ -> later $ describe "maybe expression" nothing

    projection :: m (SomeExpr s)
    projection =
      do (n, Pair t e) <- describe "projection from variant type" $ binary Proj int synth
         case t of
           VariantRepr ts ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = MaybeRepr (ts^.ixF' idx)
                    return $ SomeE ty $ EApp $ ProjectVariant ts idx e
           _ -> describe ("expecting variant type (got " <> T.pack (show t) <> ")") empty

    injection :: m (SomeExpr s)
    injection =
      do (n, e) <- describe "injection into variant type" $ binary Inj int anything
         case typeHint of
           Just (Some (VariantRepr ts)) ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = view (ixF' idx) ts
                    out <- withProgressStep Rest $ withProgressStep Rest $ withProgressStep SP.First $
                             parse e (check ty)
                    return $ SomeE (VariantRepr ts) $ EApp $ InjectVariant ts idx out
           Just (Some t) ->
             describe ("context expecting variant type (got " <> T.pack (show t) <> ")") empty
           Nothing ->
             describe ("expected unambiguous variant") empty

    ite :: m (SomeExpr s)
    ite =
      do (c, (et, (ef, ()))) <-
           followedBy (kw If) $
           cons (check BoolRepr) $
           cons (synthExpr typeHint) $
           cons (synthExpr typeHint) $
           emptyList
         matchingExprs typeHint et ef $ \tp t f ->
           case asBaseType tp of
             NotBaseType ->
               let msg = T.concat [ "conditional where branches have base type (got "
                                  , T.pack (show tp)
                                  ]
               in later $ describe msg empty
             AsBaseType bty ->
               return $ SomeE tp $ EApp $ BaseIte bty c t f

    toAny =
      do Pair tp e <- unary ToAny synth
         return $ SomeE AnyRepr (EApp (PackAny tp e))
    fromAny =
      (binary FromAny isType (check AnyRepr)) <&>
        \(Some ty, e) -> SomeE (MaybeRepr ty) (EApp (UnpackAny ty e))

    stringAppend =
      do (s1,s2) <-
           binary StringAppend (check StringRepr) (check StringRepr)
         return $ SomeE StringRepr $ EApp $ AppendString s1 s2

    vecRep =
      do let newhint = case typeHint of
                         Just (Some (VectorRepr t)) -> Just (Some t)
                         _ -> Nothing
         (n, Pair t e) <-
           binary VectorReplicate_ (check NatRepr) (forceSynth =<< synthExpr newhint)
         return $ SomeE (VectorRepr t) $ EApp $ VectorReplicate t n e

    vecLen :: m (SomeExpr s)
    vecLen =
      do Pair t e <- unary VectorSize_ synth
         case t of
           VectorRepr _ -> return $ SomeE NatRepr $ EApp $ VectorSize e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecEmptyP :: m (SomeExpr s)
    vecEmptyP =
      do Pair t e <- unary VectorIsEmpty_ synth
         case t of
           VectorRepr _ -> return $ SomeE BoolRepr $ EApp $ VectorIsEmpty e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecLit :: m (SomeExpr s)
    vecLit =
      let newhint = case typeHint of
                       Just (Some (VectorRepr t)) -> Just (Some t)
                       _ -> Nothing
       in describe "vector literal" $
          do ((),ls) <- cons (kw VectorLit_) (commit *> rep (synthExpr newhint))
             case findJointType newhint ls of
               Nothing -> later $ describe "unambiguous vector literal (add a type ascription to disambiguate)" empty
               Just (Some t) ->
                 SomeE (VectorRepr t) . EApp . VectorLit t . V.fromList
                   <$> mapM (evalSomeExpr t) ls

    vecCons :: m (SomeExpr s)
    vecCons =
      do let newhint = case typeHint of
                         Just (Some (VectorRepr t)) -> Just (Some t)
                         _ -> Nothing
         (a, d) <- binary VectorCons_ (later (synthExpr newhint)) (later (synthExpr typeHint))
         let g Nothing = Nothing
             g (Just (Some t)) = Just (Some (VectorRepr t))
         case join (find isJust [ typeHint, g (someExprType a), someExprType d ]) of
           Just (Some (VectorRepr t)) ->
             SomeE (VectorRepr t) . EApp <$> (VectorCons t <$> evalSomeExpr t a <*> evalSomeExpr (VectorRepr t) d)
           _ -> later $ describe "unambiguous vector cons (add a type ascription to disambiguate)" empty

    vecGet :: m (SomeExpr s)
    vecGet =
      do let newhint = case typeHint of
                         Just (Some t) -> Just (Some (VectorRepr t))
                         _ -> Nothing
         (Pair t e, n) <-
            binary VectorGetEntry_ (forceSynth =<< synthExpr newhint) (check NatRepr)
         case t of
           VectorRepr elemT -> return $ SomeE elemT $ EApp $ VectorGetEntry elemT e n
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecSet :: m (SomeExpr s)
    vecSet =
      do (kw VectorSetEntry_) `followedBy` (
           depCons (forceSynth =<< synthExpr typeHint) $
            \ (Pair t vec) ->
              case t of
                VectorRepr elemT ->
                  do (n, (elt, ())) <- cons (check NatRepr) $
                                       cons (check elemT) $
                                       emptyList
                     return $ SomeE (VectorRepr elemT) $ EApp $ VectorSetEntry elemT vec n elt
                _ -> later $ describe "argument with vector type" empty)

    showExpr :: m (SomeExpr s)
    showExpr =
      do Pair t1 e <- unary Show synth
         case asBaseType t1 of
           NotBaseType -> describe ("base type, but got " <> T.pack (show t1)) empty
           AsBaseType bt ->
             return $ SomeE StringRepr $ EApp $ ShowValue bt e

data NatHint
  = NoHint
  | forall w. (1 <= w) => NatHint (NatRepr w)

synthBV :: forall m h s .
  (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) =>
  NatHint ->
  m (SomeBVExpr s)
synthBV widthHint =
   bvLit <|> bvConcat <|> bvSelect <|> bvTrunc <|>
   bvZext <|> bvSext <|> boolToBV <|>
   naryBV BVAnd_ BVAnd 1 <|> naryBV BVOr_ BVOr 0 <|> naryBV BVXor_ BVXor 0 <|>
   binaryBV Sdiv BVSdiv <|> binaryBV Smod BVSrem <|>
   binaryBV BVShl_ BVShl <|> binaryBV BVLshr_ BVLshr <|> binaryBV BVAshr_ BVAshr <|>
   unaryBV Negate BVNeg <|> unaryBV BVNot_ BVNot

 where
    bvSubterm :: NatHint -> m (SomeBVExpr s)
    bvSubterm hint =
      do let newhint = case hint of
                         NatHint w -> Just (Some (BVRepr w))
                         _ -> Nothing
         (Pair t x) <- forceSynth =<< synthExpr newhint
         case t of
           BVRepr w -> return (SomeBVExpr w x)
           _ -> later $ describe "bitvector expression" $ empty

    bvLit :: m (SomeBVExpr s)
    bvLit =
      describe "bitvector literal" $
      do (PosNat w, i) <- binary BV posNat int
         return $ SomeBVExpr w $ EApp $ BVLit w i

    unaryBV :: Keyword
          -> (forall w. (1 <= w) => NatRepr w -> E s (BVType w) -> App () (E s) (BVType w))
          -> m (SomeBVExpr s)
    unaryBV k f =
      do SomeBVExpr wx x <- unary k (bvSubterm widthHint)
         return $ SomeBVExpr wx $ EApp $ f wx x

    binaryBV :: Keyword
          -> (forall w. (1 <= w) => NatRepr w -> E s (BVType w) -> E s (BVType w) -> App () (E s) (BVType w))
          -> m (SomeBVExpr s)
    binaryBV k f =
      do (SomeBVExpr wx x, SomeBVExpr wy y) <- binary k (bvSubterm widthHint) (bvSubterm widthHint)
         case testEquality wx wy of
           Just Refl -> return $ SomeBVExpr wx $ EApp $ f wx x y
           Nothing -> later $
             describe ("bitwise expression arguments with matching widths (" <>
                       T.pack (show wx) <> " /= " <> T.pack (show wy) <> ")")
                      empty

    naryBV :: Keyword
          -> (forall w. (1 <= w) => NatRepr w -> E s (BVType w) -> E s (BVType w) -> App () (E s) (BVType w))
          -> Integer
          -> m (SomeBVExpr s)
    naryBV k f u =
      do args <- kw k `followedBy` rep (later (bvSubterm widthHint))
         case args of
           [] -> case widthHint of
                   NoHint    -> later $ describe "ambiguous width" empty
                   NatHint w -> return $ SomeBVExpr w $ EApp $ BVLit w u
           (SomeBVExpr wx x:xs) -> SomeBVExpr wx <$> go wx x xs

     where
     go :: forall w. NatRepr w -> E s (BVType w) -> [SomeBVExpr s] -> m (E s (BVType w))
     go _wx x [] = return x
     go wx x (SomeBVExpr wy y : ys) =
       case testEquality wx wy of
         Just Refl -> go wx (EApp $ f wx x y) ys
         Nothing   -> later $
              describe ("bitwise expression arguments with matching widths (" <>
                        T.pack (show wx) <> " /= " <> T.pack (show wy) <> ")")
                       empty

    boolToBV :: m (SomeBVExpr s)
    boolToBV =
      do (PosNat w, x) <- binary BoolToBV_ posNat (check BoolRepr)
         return $ SomeBVExpr w $ EApp $ BoolToBV w x

    bvSelect :: m (SomeBVExpr s)
    bvSelect =
      do (Some idx, (PosNat len, (SomeBVExpr w x, ()))) <-
             followedBy (kw BVSelect_) (commit *> cons natRepr (cons posNat (cons (bvSubterm NoHint) emptyList)))
         case testLeq (addNat idx len) w of
           Just LeqProof -> return $ SomeBVExpr len $ EApp $ BVSelect idx len w x
           _ -> later $ describe ("valid bitvector select") $ empty

    bvConcat :: m (SomeBVExpr s)
    bvConcat =
      do (SomeBVExpr wx x, SomeBVExpr wy y) <- binary BVConcat_ (bvSubterm NoHint) (bvSubterm NoHint)
         let w = addNat wx wy
         Just LeqProof <- return (isPosNat w)
         return $ SomeBVExpr w (EApp $ BVConcat wx wy x y)

    bvTrunc :: m (SomeBVExpr s)
    bvTrunc =
      do (PosNat r, SomeBVExpr w x) <- binary BVTrunc_ posNat (bvSubterm NoHint)
         case testLeq (incNat r) w of
           Just LeqProof -> return $ SomeBVExpr r (EApp $ BVTrunc r w x)
           _ -> later $ describe "valid bitvector truncation" $ empty

    bvZext :: m (SomeBVExpr s)
    bvZext =
      do (PosNat r, SomeBVExpr w x) <- binary BVZext_ posNat (bvSubterm NoHint)
         case testLeq (incNat w) r of
           Just LeqProof -> return $ SomeBVExpr r (EApp $ BVZext r w x)
           _ -> later $ describe "valid zero extension" $ empty

    bvSext :: m (SomeBVExpr s)
    bvSext =
      do (PosNat r, SomeBVExpr w x) <- binary BVSext_ posNat (bvSubterm NoHint)
         case testLeq (incNat w) r of
           Just LeqProof -> return $ SomeBVExpr r (EApp $ BVSext r w x)
           _ -> later $ describe "valid zero extension" $ empty


check :: forall m t h s . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
       => TypeRepr t -> m (E s t)
check t =
  describe ("inhabitant of " <> T.pack (show t)) $
    do Pair t' e <- forceSynth =<< synthExpr (Just (Some t))
       later $ describe ("a " <> T.pack (show t) <> " rather than a " <> T.pack (show t')) $
         case testEquality t t' of
           Nothing -> later empty
           Just Refl -> return e

-------------------------------------------------------------------------

data LabelInfo :: * -> * where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . TypeRepr ty -> LambdaLabel s ty -> LabelInfo s

data GlobalInfo :: * where
  GlobalInfo :: forall t . Closed t => TypeRepr t -> GlobalVar t -> GlobalInfo

data ProgramState h s =
  ProgramState { _progFunctions :: Map FunctionName FunctionHeader
               , _progGlobals :: Map GlobalName GlobalInfo
               , _progHandleAlloc :: HandleAllocator h
               }

progFunctions :: Simple Lens (ProgramState h s) (Map FunctionName FunctionHeader)
progFunctions = lens _progFunctions (\s v -> s { _progFunctions = v })

progGlobals :: Simple Lens (ProgramState h s) (Map GlobalName GlobalInfo)
progGlobals = lens _progGlobals (\s v -> s { _progGlobals = v })

progHandleAlloc :: Simple Lens (ProgramState h s) (HandleAllocator h)
progHandleAlloc = lens _progHandleAlloc (\s v -> s { _progHandleAlloc = v })


data SyntaxState h s =
  SyntaxState { _stxLabels :: Map LabelName (LabelInfo s)
              , _stxAtoms :: Map AtomName (Pair TypeRepr (Atom s))
              , _stxTypeArgs :: [TyVarName]
              , _stxRegisters :: Map RegName (Pair TypeRepr (Reg s))
              , _stxNonceGen :: NonceGenerator (ST h) s
              , _stxProgState :: ProgramState h s
              }


initProgState :: [(SomeHandle,Position)] -> HandleAllocator h -> ProgramState h s
initProgState builtIns ha = ProgramState fns Map.empty ha
  where
  f tps = Ctx.generate
            (Ctx.size tps)
            (\i -> Arg (AtomName ("arg" <> (T.pack (show i)))) InternalPos (tps Ctx.! i))
  fns = Map.fromList
        [ (handleName h,
            FunctionHeader
              (handleName h)
              (f (handleArgTypes h))
              (handleReturnType h)
              h
              p
           )
        | (SomeHandle h,p) <- builtIns
        , Dict <- maybeToList (checkClosedCtx (handleArgTypes h))
        , Dict <- maybeToList (checkClosed (handleReturnType h))
        ]

<<<<<<< HEAD
initSyntaxState :: NonceGenerator (ST h) s -> ProgramState h s -> SyntaxState h s
initSyntaxState =
  SyntaxState Map.empty Map.empty Map.empty
=======
initSyntaxState :: ProgramState h s -> SyntaxState h s
initSyntaxState = SyntaxState Map.empty Map.empty [] Map.empty 0 0
>>>>>>> Preliminary parser support for polymorphism

stxLabels :: Simple Lens (SyntaxState h s) (Map LabelName (LabelInfo s))
stxLabels = lens _stxLabels (\s v -> s { _stxLabels = v })

stxAtoms :: Simple Lens (SyntaxState h s) (Map AtomName (Pair TypeRepr (Atom s)))
stxAtoms = lens _stxAtoms (\s v -> s { _stxAtoms = v })

stxRegisters :: Simple Lens (SyntaxState h s) (Map RegName (Pair TypeRepr (Reg s)))
stxRegisters = lens _stxRegisters (\s v -> s { _stxRegisters = v })

<<<<<<< HEAD
stxNonceGen :: Getter (SyntaxState h s) (NonceGenerator (ST h) s)
stxNonceGen = to _stxNonceGen
=======
stxTypeArgs :: Simple Lens (SyntaxState h s) [TyVarName]
stxTypeArgs = lens _stxTypeArgs (\s v -> s { _stxTypeArgs = v })

stxNextLabel :: Simple Lens (SyntaxState h s) Int
stxNextLabel = lens _stxNextLabel (\s v -> s { _stxNextLabel = v })

stxNextAtom :: Simple Lens (SyntaxState h s) Int
stxNextAtom = lens _stxNextAtom (\s v -> s { _stxNextAtom = v })
>>>>>>> Preliminary parser support for polymorphism

stxProgState :: Simple Lens (SyntaxState h s) (ProgramState h s)
stxProgState = lens _stxProgState (\s v -> s { _stxProgState = v })

stxFunctions :: Simple Lens (SyntaxState h s) (Map FunctionName FunctionHeader)
stxFunctions = stxProgState . progFunctions

stxGlobals :: Simple Lens (SyntaxState h s) (Map GlobalName GlobalInfo)
stxGlobals = stxProgState . progGlobals


newtype CFGParser h s ret a =
  CFGParser { runCFGParser :: (?returnType :: TypeRepr ret)
                           => ExceptT (ExprErr s)
                                (StateT (SyntaxState h s) (ST h))
                                a
            }
  deriving (Functor)

instance Applicative (CFGParser h s ret) where
  pure x = CFGParser (pure x)
  (CFGParser f) <*> (CFGParser x) = CFGParser (f <*> x)

instance Alternative (CFGParser h s ret) where
  empty = CFGParser $ throwError $ TrivialErr InternalPos
  (CFGParser x) <|> (CFGParser y) = CFGParser (x <|> y)

instance Semigroup (CFGParser h s ret a) where
  (<>) = (<|>)

instance Monoid (CFGParser h s ret a) where
  mempty = empty
  mappend = (<|>)

instance Monad (CFGParser h s ret) where
  return = pure
  (CFGParser m) >>= f = CFGParser $ m >>= runCFGParser . f

instance MonadError (ExprErr s) (CFGParser h s ret) where
  throwError = CFGParser . throwError
  catchError m h = CFGParser $ catchError (runCFGParser m) (runCFGParser . h)

instance MonadState (SyntaxState h s) (CFGParser h s ret) where
  get = CFGParser get
  put = CFGParser . put

instance MonadST h (CFGParser h s ret) where
  liftST = CFGParser . lift . lift


freshId :: (MonadState (SyntaxState h s) m, MonadST h m) => m (Nonce s tp)
freshId =
  do ng <- use stxNonceGen
     liftST $ freshNonce ng

freshLabel :: (MonadState (SyntaxState h s) m, MonadST h m) => m (Label s)
freshLabel = Label <$> freshId

freshAtom :: (MonadWriter [Posd (Stmt () s)] m, MonadState (SyntaxState h s) m, MonadST h m )
          => Position -> AtomValue () s t -> m (Atom s t)
freshAtom loc v =
  do i <- freshId
     let theAtom = Atom { atomPosition = OtherPos "Parser internals"
                        , atomId = i
                        , atomSource = Assigned
                        , typeOfAtom = typeOfAtomValue v
                        }
         stmt = DefineAtom theAtom v
     tell [Posd loc stmt]
     pure theAtom



newLabel :: (MonadState (SyntaxState h s) m, MonadST h m) => LabelName -> m (Label s)
newLabel x =
  do theLbl <- freshLabel
     stxLabels %= Map.insert x (NoArgLbl theLbl)
     return theLbl

freshLambdaLabel :: (MonadState (SyntaxState h s) m, MonadST h m) => TypeRepr tp -> m (LambdaLabel s tp, Atom s tp)
freshLambdaLabel t =
  do n <- freshId
     i <- freshId
     let lbl = LambdaLabel n a
         a   = Atom { atomPosition = OtherPos "Parser internals"
                    , atomId = i
                    , atomSource = LambdaArg lbl
                    , typeOfAtom = t
                    }
     return (lbl, a)

with :: MonadState s m => Lens' s a -> (a -> m b) -> m b
with l act = do x <- use l; act x


lambdaLabelBinding :: (MonadSyntax Atomic m, MonadState (SyntaxState h s) m, MonadST h m)
                   => m (LabelName, (Pair TypeRepr (LambdaLabel s)))
lambdaLabelBinding =
  call $
  depCons uniqueLabel $
  \l ->
    depCons uniqueAtom $
    \x ->
      depCons isType $
      \(Some t) ->
        do (lbl, anAtom) <- freshLambdaLabel t
           stxLabels %= Map.insert l (ArgLbl t lbl)
           stxAtoms %= Map.insert x (Pair t anAtom)
           return (l, (Pair t lbl))

  where uniqueLabel =
          do labels <- use stxLabels
             sideCondition "unique label"
               (\l -> case Map.lookup l labels of
                        Nothing -> Just l
                        Just _ -> Nothing)
               labelName


uniqueAtom :: (MonadSyntax Atomic m, MonadState (SyntaxState h s) m) => m AtomName
uniqueAtom =
  do atoms <- use stxAtoms
     sideCondition "unique Crucible atom"
       (\x -> case Map.lookup x atoms of
                Nothing -> Just x
                Just _ -> Nothing)
       atomName

newUnassignedReg :: (MonadState (SyntaxState h s) m, MonadST h m) => TypeRepr t -> m (Reg s t)
newUnassignedReg t =
  do i <- freshId
     let fakePos = OtherPos "Parser internals"
     return $! Reg { regPosition = fakePos
                   , regId = i
                   , typeOfReg = t
                   }

regRef' :: (MonadSyntax Atomic m, MonadState (SyntaxState h s) m) => m (Pair TypeRepr (Reg s))
regRef' =
  describe "known register name" $
  do rn <- regName
     perhapsReg <- use (stxRegisters . at rn)
     case perhapsReg of
       Just reg -> return reg
       Nothing -> empty

globRef' :: (MonadSyntax Atomic m, MonadState (SyntaxState h s) m) => m GlobalInfo
globRef' =
  describe "known global variable name" $
  do x <- globalName
     perhapsGlobal <- use (stxGlobals . at x)
     case perhapsGlobal of
       Just glob -> return glob
       Nothing -> empty



reading :: MonadState r m => ReaderT r m b -> m b
reading m = get >>= runReaderT m

--------------------------------------------------------------------------

atomSetter :: (MonadSyntax Atomic m, MonadWriter [Posd (Stmt () s)] m, MonadState (SyntaxState h s) m, MonadST h m)
           => AtomName -- ^ The name of the atom being set, used for fresh name internals
           -> m (Pair TypeRepr (Atom s))
atomSetter (AtomName anText) =
  call (newref <|> emptyref <|> fresh <|> funcall <|> evaluated)
  where
    fresh, emptyref, newref
      :: ( MonadSyntax Atomic m
         , MonadWriter [Posd (Stmt () s)] m
         , MonadState (SyntaxState h s) m
         , MonadST h m
         )
      => m (Pair TypeRepr (Atom s))

    newref =
      do Pair t e <- reading $ unary Ref synth
         loc <- position
         anAtom <- eval loc e
         anotherAtom <- freshAtom loc (NewRef anAtom)
         return $ Pair (ReferenceRepr t) anotherAtom

    emptyref =
      do Some t' <- reading $ unary EmptyRef isType
         loc <- position
         anAtom <- freshAtom loc (NewEmptyRef t')
         return $ Pair (ReferenceRepr t') anAtom

    fresh =
      do Some t <- reading (unary Fresh isBaseType)
         describe "user symbol" $
           case userSymbol (T.unpack anText) of
             Left err -> describe (T.pack (show err)) empty
             Right nm ->
               do loc <- position
                  Pair (baseToType t) <$>
                    freshAtom loc (FreshConstant t (Just nm))

    evaluated =
       do Pair tp e' <- reading synth
          loc <- position
          anAtom <- eval loc e'
          return $ Pair tp anAtom


funcall
  :: ( MonadSyntax Atomic m
     , MonadWriter [Posd (Stmt () s)] m
     , MonadState (SyntaxState h s) m
     , MonadST h m
     )
  => m (Pair TypeRepr (Atom s))
funcall =
  followedBy (kw Funcall) $
  depConsCond (reading synth) $
    \x ->
      case x of
        (Pair (FunctionHandleRepr funArgs ret) fun) ->
          do loc <- position
             funAtom <- eval loc fun
             operandExprs <- backwards $ go $ Ctx.viewAssign funArgs
             operandAtoms <- traverseFC (\(Rand a ex) -> eval (syntaxPos a) ex) operandExprs
             endAtom <- freshAtom loc $ Call funAtom operandAtoms ret
             return $ Right $ Pair ret endAtom
        _ -> return $ Left "a function"
  where
    go :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
       => Ctx.AssignView TypeRepr args
       -> m (Ctx.Assignment (Rand s) args)
    go Ctx.AssignEmpty = emptyList *> pure Ctx.empty
    go (Ctx.AssignExtend ctx' ty) =
      depCons (reading $ check ty) $ \e ->
        do rest <- go (Ctx.viewAssign ctx')
           this <- anything
           return $ Ctx.extend rest $ Rand this e


located :: MonadSyntax atom m => m a -> m (Posd a)
located p = Posd <$> position <*> p

normStmt' :: forall h s m
           . (MonadWriter [Posd (Stmt () s)] m, MonadSyntax Atomic m, MonadState (SyntaxState h s) m, MonadST h m) =>
             m ()
normStmt' =
  call (printStmt <|> letStmt <|> (void funcall) <|>
        setGlobal <|> setReg <|> setRef <|> dropRef <|>
        assertion <|> assumption)

  where
    printStmt, letStmt, setGlobal, setReg, setRef, dropRef, assertion :: m ()
    printStmt =
      do Posd loc e <- unary Print_ (located $ reading $ check StringRepr)
         strAtom <- eval loc e
         tell [Posd loc (Print strAtom)]

    letStmt =
      followedBy (kw Let) $
      depCons uniqueAtom $
        \x ->
          do setter <- fst <$> cons (atomSetter x) emptyList
             stxAtoms %= Map.insert x setter

    setGlobal =
      followedBy (kw SetGlobal) $
      depConsCond globalName $
        \g ->
          use (stxGlobals . at g) >>=
            \case
              Nothing -> return $ Left "known global variable name"
              Just (GlobalInfo t var) ->
                do (Posd loc e) <- fst <$> cons (located $ reading $ check t) emptyList
                   a <- eval loc e
                   tell [Posd loc $ WriteGlobal var a]
                   return (Right ())

    setReg =
      followedBy (kw SetRegister) $
      depCons (reading regRef') $
      \(Pair ty r) ->
        depCons (reading $ located $ check ty) $
        \(Posd loc e) ->
          do emptyList
             v <- eval loc e
             tell [Posd loc $ SetReg r v]

    setRef =
      do stmtLoc <- position
         followedBy (kw SetRef) $
           depConsCond (located $ reading $ synth) $
           \case
             (Posd refLoc (Pair (ReferenceRepr t') refE)) ->
               depCons (located $ reading $ check t') $
               \(Posd valLoc valE) ->
                 do emptyList
                    refAtom <- eval refLoc refE
                    valAtom <- eval valLoc valE
                    tell [Posd stmtLoc $ WriteRef refAtom valAtom]
                    return (Right ())
             (Posd _ _) ->
               return $ Left "expression with reference type"

    dropRef =
      do loc <- position
         followedBy (kw DropRef_) $
           depConsCond (located $ reading synth) $
            \(Posd eLoc (Pair t refE)) ->
               emptyList *>
               case t of
                 ReferenceRepr _ ->
                   do refAtom <- eval eLoc refE
                      tell [Posd loc $ DropRef refAtom]
                      return $ Right ()
                 _ -> return $ Left "expression with reference type"

    assertion =
      do (Posd loc (Posd cLoc cond, Posd mLoc msg)) <-
           located $
           binary Assert_
             (located $ reading $ check BoolRepr)
             (located $ reading $ check StringRepr)
         cond' <- eval cLoc cond
         msg' <- eval mLoc msg
         tell [Posd loc $ Assert cond' msg']

    assumption =
      do (Posd loc (Posd cLoc cond, Posd mLoc msg)) <-
           located $
           binary Assume_
             (located $ reading $ check BoolRepr)
             (located $ reading $ check StringRepr)
         cond' <- eval cLoc cond
         msg' <- eval mLoc msg
         tell [Posd loc $ Assume cond' msg']


blockBody' :: forall s h ret m
            . (MonadSyntax Atomic m, MonadState (SyntaxState h s) m, MonadST h m)
           => TypeRepr ret
           -> m (Posd (TermStmt s ret), [Posd (Stmt () s)])
blockBody' ret = runWriterT go
 where
 go :: WriterT [Posd (Stmt () s)] m (Posd (TermStmt s ret))
 go = (fst <$> (cons (later (termStmt' ret)) emptyList)) <|>
      (snd <$> (cons (later normStmt') go))

termStmt' :: forall m h s ret.
   (MonadWriter [Posd (Stmt () s)] m, MonadSyntax Atomic m, MonadState (SyntaxState h s) m, MonadST h m) =>
   TypeRepr ret -> m (Posd (TermStmt s ret))
termStmt' retTy =
  do stx <- anything
     call (withPosFrom stx <$>
       (jump <|> branch <|> maybeBranch <|> cases <|> ret <|> err <|> tailCall <|> out))

  where
    normalLabel =
      do x <- labelName
         l <- use (stxLabels . at x)
         later $ describe "known label with no arguments" $
           case l of
             Nothing -> empty
             Just (ArgLbl _ _) -> empty
             Just (NoArgLbl lbl) -> pure lbl

    lambdaLabel :: m (Pair TypeRepr (LambdaLabel s))
    lambdaLabel =
      do x <- labelName
         l <- use (stxLabels . at x)
         later $ describe "known label with an argument" $
           case l of
             Nothing -> empty
             Just (ArgLbl t lbl) -> pure $ Pair t lbl
             Just (NoArgLbl _) -> empty

    typedLambdaLabel :: TypeRepr t -> m (LambdaLabel s t)
    typedLambdaLabel t =
      do x <- labelName
         l <- use (stxLabels . at x)
         later $ describe ("known label with an " <> T.pack (show t) <> " argument") $
           case l of
             Nothing -> empty
             Just (ArgLbl t' lbl) ->
               case testEquality t' t of
                 Nothing -> empty
                 Just Refl -> pure lbl
             Just (NoArgLbl _) -> empty

    jump = unary Jump_ normalLabel <&> Jump

    branch = kw Branch_ `followedBy`
             (depCons (located (reading (check BoolRepr))) $
                \ (Posd eloc cond) ->
                  cons normalLabel (cons normalLabel emptyList) >>=
                  \(l1, (l2, ())) -> do
                    c <- eval eloc cond
                    return (Br c l1 l2))

    maybeBranch :: m (TermStmt s ret)
    maybeBranch =
      followedBy (kw MaybeBranch_) $
      describe "valid arguments to maybe-branch" $
      depCons (located (reading synth)) $
        \(Posd sloc (Pair ty scrut)) ->
          case ty of
            MaybeRepr ty' ->
              depCons (typedLambdaLabel ty') $
                \lbl1 ->
                  depCons normalLabel $
                    \ lbl2 ->
                      do s <- eval sloc scrut
                         return $ MaybeBranch ty' s lbl1 lbl2
            _ -> empty

    cases :: m (TermStmt s ret)
    cases =
      followedBy (kw Case) $
      depCons (located (reading synth)) $
        \(Posd tgtloc (Pair ty tgt)) ->
          describe ("cases for variant type " <> T.pack (show ty)) $
          case ty of
            VariantRepr ctx ->
              do t <- eval tgtloc tgt
                 VariantElim ctx t <$> backwards (go (Ctx.viewAssign ctx))
            _ -> empty
      where
        go :: forall cases
            . Ctx.AssignView TypeRepr cases
           -> m (Ctx.Assignment (LambdaLabel s) cases)
        go Ctx.AssignEmpty = emptyList $> Ctx.empty
        go (Ctx.AssignExtend ctx' t) =
          depCons (typedLambdaLabel t) $
            \ lbl -> Ctx.extend <$>
                       go (Ctx.viewAssign ctx') <*>
                       pure lbl

    ret :: m (TermStmt s ret)
    ret =
        do Posd loc e <- unary Return_ (located (reading (check retTy)))
           Return <$> eval loc e

    tailCall :: m (TermStmt s ret)
    tailCall =
      followedBy (kw TailCall_) $
        describe "function atom and arguments" $
          do -- commit
             depCons (located (reading synth)) $
               \case
                 Posd loc (Pair (FunctionHandleRepr argumentTypes retTy') funExpr) ->
                   case testEquality retTy retTy' of
                       Nothing -> empty
                       Just Refl ->
                         do funAtom <- eval loc funExpr
                            describe ("arguments with types " <> T.pack (show argumentTypes)) $
                              TailCall funAtom argumentTypes <$> backwards (go (Ctx.viewAssign argumentTypes))
                 _ -> empty
      where
        go :: forall argTypes
            . Ctx.AssignView TypeRepr argTypes
           -> m (Ctx.Assignment (Atom s) argTypes)
        go Ctx.AssignEmpty = emptyList *> pure Ctx.empty
        go (Ctx.AssignExtend tys ty) =
          depCons (located (reading (check ty))) $
            \(Posd loc arg) ->
               Ctx.extend <$> go (Ctx.viewAssign tys) <*> eval loc arg

    err :: m (TermStmt s ret)
    err =
      do Posd loc e <- unary Error_ (located (reading (check StringRepr)))
         ErrorStmt <$> eval loc e

    out :: m (TermStmt s ret)
    out = followedBy (kw Output_) $
          do -- commit
             depCons lambdaLabel $
               \(Pair argTy lbl) ->
                 depCons (located (reading (check argTy))) $
                   \(Posd loc arg) ->
                     emptyList *>
                       (Output lbl <$> eval loc arg)



data Rand s t = Rand (AST s) (E s t)




--------------------------------------------------------------------------

-- | Any CFG, regardless of its arguments and return type, with its helpers
data ACFG :: * where
  ACFG :: forall (s :: *) (init :: Ctx CrucibleType) (ret :: CrucibleType) .
          CtxRepr init -> TypeRepr ret ->
          CFG () s init ret ->
          ACFG

deriving instance Show ACFG

data Arg t = Arg AtomName Position (TypeRepr t)

data TypeArg = TypeArg { _typeArgName :: TyVarName
                       , _typeArgPos :: Position
                       }
typeArgName :: Simple Lens TypeArg TyVarName
typeArgName = lens _typeArgName (\s v -> s { _typeArgName = v })

typeArgPos :: Simple Lens TypeArg Position
typeArgPos = lens _typeArgPos (\s v -> s { _typeArgPos = v })

typeArguments :: forall m h s . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
              => m (Some (Ctx.Assignment TypeRepr))
typeArguments = call (go (Some Ctx.empty))
  where
    go args@(Some prev) =
      describe "type argument list" $
      (emptyList *> pure args) <|>
      (depCons oneArg $
       \(Some a) ->
         go (Some $ Ctx.extend prev a))
    oneArg =
      describe "type argument" $ isType

arguments' :: forall m h s . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
           => m (Some (Ctx.Assignment Arg))
arguments' = call (go (Some Ctx.empty))
  where
    go ::  Some (Ctx.Assignment Arg) -> m (Some (Ctx.Assignment Arg))
    go args@(Some prev) =
      describe "argument list" $
        (emptyList *> pure args) <|>
        (depCons oneArg $
           \(Some a) ->
             go (Some $ Ctx.extend prev a))

      where oneArg =
              (describe "argument" $
               located $
               cons atomName (cons isType emptyList)) <&>
              \(Posd loc (x, (Some t, ()))) -> Some (Arg x loc t)

checkDups :: MonadError (ExprErr s) m => [TypeArg] -> m ()
checkDups tvs = go Map.empty tvs
  where go seen [] = return ()
        go seen (v:vs) =
          let n = view typeArgName v
          in case Map.lookup n seen of
               Nothing -> go (Map.insert n v seen) vs
               Just seen -> throwError $ DuplicateTypeArg (view typeArgPos v) n

saveTypeArgs :: (MonadState (SyntaxState h s) m)
             => [TypeArg] -> m ()
saveTypeArgs args = stxTypeArgs .= map (view typeArgName) args


withTypeArgs :: (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m)
             => [TypeArg] -> m a -> m a
withTypeArgs args act =
  do oldArgs <- use stxTypeArgs
     catchError (do saveTypeArgs args
                    res <- act
                    stxTypeArgs .= oldArgs
                    return res)
       (\e -> do stxTypeArgs .= oldArgs ; throwError e)

parseWithTypeArgs :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
             => [TypeArg] -> m a -> m a
parseWithTypeArgs args act =
  do oldArgs <- use stxTypeArgs
     saveTypeArgs args
     res <- act
     stxTypeArgs .= oldArgs
     return res


saveArgs :: (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m)
         => Ctx.Assignment Arg init
         -> Ctx.Assignment (Atom s) init
         -> m ()
saveArgs ctx1 ctx2 =
  let combined = Ctx.zipWith
                   (\(Arg x p t) argAtom ->
                      (Const (Pair t (Functor.Pair (Const x) (Functor.Pair (Const p) argAtom)))))
                   ctx1 ctx2
  in forMFC_ combined $
       \(Const (Pair t (Functor.Pair (Const x) (Functor.Pair (Const argPos) y)))) ->
         with (stxAtoms . at x) $
           \case
             Just _ -> throwError $ DuplicateAtom argPos x
             Nothing ->
               do stxAtoms %= Map.insert x (Pair t y)

data FunctionHeader =
  forall args ret .
  (Closed args, Closed ret) =>
  FunctionHeader { _headerName :: FunctionName
                 , _headerArgs :: Ctx.Assignment Arg args
                 , _headerReturnType :: TypeRepr ret
                 , _headerHandle :: FnHandle args ret
                 , _headerLoc :: Position
                 }
  | forall args ret .
    PolyFunctionHeader { _headerName :: FunctionName
                       , _headerTypeArgs :: [TypeArg]
                       , _headerArgs :: Ctx.Assignment Arg args
                       , _headerReturnType :: TypeRepr ret
                       , _headerHandle :: FnHandle args ret
                       , _headerLoc :: Position
                       }

data FunctionSource s =
  FunctionSource { _functionRegisters :: [AST s]
                 , _functionBody :: AST s
                 }

functionHeader' :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
                => m ( (FunctionName, Some (Ctx.Assignment Arg), Some TypeRepr, Position)
                     , FunctionSource s
                     )
functionHeader' =
  do (fnName, (Some theArgs, (Some ret, (regs, body)))) <-
       followedBy (kw Defun) $
       cons funName $
       cons arguments' $
       cons isType $
       cons registers anything <|> ([], ) <$> anything
     loc <- position
     return ((fnName, Some theArgs, Some ret, loc), FunctionSource regs body)
  where
    registers = call $ kw Registers `followedBy` anyList

polyFunctionHeader' :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m)
                    => m ( (FunctionName, [TypeArg], Some (Ctx.Assignment Arg), Some TypeRepr, Position)
                         , FunctionSource s
                         )
polyFunctionHeader' =
  do (tyArgs, (fnName, (Some theArgs, (Some ret, (regs, body))))) <-
       followedBy (kw DefPoly) $
       depCons typeArgs $ \tyArgs ->
       (tyArgs ,) <$>
       parseWithTypeArgs tyArgs
         (cons funName $
         cons arguments' $
         cons isType $
         cons registers anything <|> ([], ) <$> anything)
     loc <- position
     return ((fnName, tyArgs, Some theArgs, Some ret, loc), FunctionSource regs body)
  where
    typeArgs = call $ rep typeArg
    typeArg =
      describe "type variable" $
      do loc <- position
         x <- typeVarName
         return $ TypeArg x loc
    registers = call $ kw Registers `followedBy` anyList


functionHeader :: AST s -> TopParser h s (FunctionHeader, FunctionSource s)
functionHeader defun =
  do st <- get
     ((fnName, Some theArgs, Some ret, loc), src) <- fst <$> liftSyntaxParse (runStateT functionHeader' st) defun
     ha <- use $ stxProgState  . progHandleAlloc
     handle <- liftST $ mkHandle' ha fnName (argTypes theArgs) ret
     Just Dict <- return $ checkClosed ret
     Just Dict <- return $ checkClosedCtx (argTypes theArgs)
     let header = FunctionHeader fnName theArgs ret handle loc

     saveHeader fnName header
     return $ (header, src)
  where
    saveHeader n h =
      stxFunctions %= Map.insert n h

polyFunctionHeader :: AST s -> TopParser h s (FunctionHeader, FunctionSource s)
polyFunctionHeader defun =
  do st <- get
     ((fnName, tyArgs, Some theArgs, Some ret, loc), src) <- fst <$> liftSyntaxParse (runStateT polyFunctionHeader' st) defun
     ha <- use $ stxProgState  . progHandleAlloc
     handle <- liftST $ mkHandle' ha fnName (argTypes theArgs) ret
     let header = PolyFunctionHeader fnName tyArgs theArgs ret handle loc

     saveHeader fnName header
     return $ (header, src)
  where
    saveHeader n h =
      stxFunctions %= Map.insert n h




global :: AST s -> TopParser h s (Pair TypeRepr GlobalVar)
global stx =
  do st <- get
     (var@(GlobalName varName), Some t) <- fst <$> liftSyntaxParse (runStateT (call (binary DefGlobal globalName isType)) st) stx
     Just Dict <- return $ checkClosed t
     ha <- use $ stxProgState  . progHandleAlloc
     v <- liftST $ freshGlobalVar ha varName t
     stxGlobals %= Map.insert var (GlobalInfo t v)
     return $ Pair t v

topLevel :: AST s -> TopParser h s (Maybe (FunctionHeader, FunctionSource s))
topLevel ast =
  catchError (Just <$> (functionHeader ast <|> polyFunctionHeader ast)) $
    \e ->
      catchError (global ast $> Nothing) $
        \_ -> throwError e

argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ _ t) -> t)


type BlockTodo h s ret =
  (LabelName, BlockID s, Progress, AST s)

blocks :: forall h s ret m . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m, MonadST h m) => TypeRepr ret -> m [Block () s ret]
blocks ret =
      depCons startBlock' $
      \ startContents ->
        do todo <- rep blockLabel'
           forM (startContents : todo) $ \(_, bid, pr, stmts) ->
             do (term, stmts') <- withProgress (const pr) $ parse stmts (call (blockBody' ret))
                pure $ mkBlock bid mempty (Seq.fromList stmts') term


  where

    startBlock' :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m, MonadST h m) => m (BlockTodo h s ret)
    startBlock' =
      call $
      describe "starting block" $
      followedBy (kw Start) $
      depCons labelName $
      \l ->
        do lbl <- newLabel l
           pr <- progress
           rest <- anything
           return (l, LabelID lbl, pr, rest)

    blockLabel' :: m (BlockTodo h s ret)
    blockLabel' =
      call $
      followedBy (kw DefBlock) $
      simpleBlock <|> argBlock
      where
        simpleBlock, argBlock :: m (BlockTodo h s ret)
        simpleBlock =
          depConsCond labelName $
          \ l ->
            do lbls <- use stxLabels
               pr <- progress
               body <- anything
               case Map.lookup l lbls of
                 Just _ -> return $ Left "unique label"
                 Nothing ->
                   do theLbl <- newLabel l
                      return $ Right (l, LabelID theLbl, pr, body)
        argBlock =
          call $
          depConsCond (lambdaLabelBinding) $
          \ (l, (Pair _ lbl)) ->
            do pr <- progress
               body <- anything
               return $ Right (l, LambdaID lbl, pr, body)

eval :: (MonadWriter [Posd (Stmt () s)] m, MonadState (SyntaxState h s) m, MonadST h m)
     => Position -> E s t -> m (Atom s t)
eval _   (EAtom theAtom)  = pure theAtom -- The expression is already evaluated
eval loc (EApp e)         = freshAtom loc . EvalApp =<< traverseFC (eval loc) e
eval _   (EReg loc reg)   = freshAtom loc (ReadReg reg)
eval _   (EGlob loc glob) = freshAtom loc (ReadGlobal glob)
eval loc (EDeref eloc e)  = freshAtom loc . ReadRef =<< eval eloc e

newtype TopParser h s a =
  TopParser { runTopParser :: ExceptT (ExprErr s)
                                (StateT (SyntaxState h s) (ST h))
                                a
            }
  deriving (Functor)

top :: NonceGenerator (ST h) s -> HandleAllocator h -> [(SomeHandle,Position)] -> TopParser h s a -> ST h (Either (ExprErr s) a)
top ng ha builtIns (TopParser (ExceptT (StateT act))) =
  fst <$> act (initSyntaxState ng (initProgState builtIns ha))

instance Applicative (TopParser h s) where
  pure x = TopParser (pure x)
  (TopParser f) <*> (TopParser x) = TopParser (f <*> x)

instance Alternative (TopParser h s) where
  empty = TopParser $ throwError (TrivialErr InternalPos)
  (TopParser x) <|> (TopParser y) = TopParser (x <|> y)

instance MonadPlus (TopParser h s) where
  mzero = empty
  mplus = (<|>)

instance Semigroup (TopParser h s a) where
  (<>) = (<|>)

instance Monoid (TopParser h s a) where
  mempty = empty
  mappend = (<|>)

instance Monad (TopParser h s) where
  return = pure
  (TopParser m) >>= f = TopParser $ m >>= runTopParser . f

instance MonadError (ExprErr s) (TopParser h s) where
  throwError = TopParser . throwError
  catchError m h = TopParser $ catchError (runTopParser m) (runTopParser . h)

instance MonadState (SyntaxState h s) (TopParser h s) where
  get = TopParser get
  put = TopParser . put

instance MonadST h (TopParser h s) where
  liftST = TopParser . lift . lift




initParser :: forall h s m
<<<<<<< HEAD
            . (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m, MonadST h m)
           => FunctionHeader
           -> FunctionSource s
           -> m ()
initParser (FunctionHeader _ (funArgs :: Ctx.Assignment Arg init) _ _ _) (FunctionSource regs _) =
  do ng <- use stxNonceGen
     progState <- use stxProgState
     put $ initSyntaxState ng progState
=======
            . (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m)
           => FunctionHeader
           -> FunctionSource s
           -> m ()
initParser header (FunctionSource regs _) =

  do (Pair (Const tyArgs) funArgs) <-
           case header of
             FunctionHeader _ (funArgs :: Ctx.Assignment Arg init) _ _ _ -> return (Pair (Const []) funArgs)
             PolyFunctionHeader _ ty (funArgs :: Ctx.Assignment Arg init) _ _ _ -> return (Pair (Const ty) funArgs)
     with stxProgState $ put . initSyntaxState
>>>>>>> Preliminary parser support for polymorphism
     let types = argTypes funArgs
     inputAtoms <- liftST $ mkInputAtoms ng (OtherPos "args") types
     saveArgs funArgs inputAtoms
     saveTypeArgs tyArgs
     forM_ regs saveRegister

  where
    saveRegister :: Syntax Atomic -> m ()
    saveRegister (L [A (Rg x), t]) =
      do st <- get
         Some ty <- fst <$> liftSyntaxParse (runStateT isType st) t
         r <- newUnassignedReg ty
         stxRegisters %= Map.insert x (Pair ty r)
    saveRegister other = throwError $ InvalidRegister (syntaxPos other) other


cfgs :: [AST s] -> TopParser h s [ACFG]
cfgs defuns =
  do headers <- catMaybes <$> traverse topLevel defuns
     forM headers $
<<<<<<< HEAD
       \(hdr@(FunctionHeader _ funArgs ret handle _), src@(FunctionSource _ body)) ->
         do let types = argTypes funArgs
            initParser hdr src
            let ?returnType = ret
            st <- get
            (theBlocks, st') <- liftSyntaxParse (runStateT (blocks ret) st) body
            put st'
            let entry = case blockID (head theBlocks) of
                  LabelID lbl -> lbl
                  LambdaID {} -> error "initial block is lambda"
            return $ ACFG types ret $ CFG handle entry theBlocks
=======
       \case
         (hdr@(FunctionHeader _ funArgs ret handle _), src@(FunctionSource _ body)) ->
           do let types = argTypes funArgs
              initParser hdr src
              let ?returnType = ret
              st <- get
              (theBlocks, st') <- liftSyntaxParse (runStateT (blocks ret) st) body
              put st'
              i <- freshAtomIndex
              j <- freshLabelIndex
              return $ ACFG types ret $ CFG handle theBlocks i j
         (hdr@(PolyFunctionHeader _ _ funArgs ret handle _), src@(FunctionSource _ body)) ->
           do let types = argTypes funArgs
              initParser hdr src
              let ?returnType = ret
              st <- get
              (theBlocks, st') <- liftSyntaxParse (runStateT (blocks ret) st) body
              put st'
              i <- freshAtomIndex
              j <- freshLabelIndex
              return $ ACFG types ret $ CFG handle theBlocks i j
>>>>>>> Preliminary parser support for polymorphism
