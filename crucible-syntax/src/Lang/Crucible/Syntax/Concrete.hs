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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# OPTIONS_GHC -fprint-explicit-kinds -fprint-explicit-foralls #-}
module Lang.Crucible.Syntax.Concrete where

import Prelude hiding (fail)

import Data.Monoid ()
import Data.Ratio

import Control.Lens hiding (cons)
import Control.Applicative
import Control.Monad.Identity hiding (fail)
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.State.Class
import Control.Monad.State.Strict
import Control.Monad.Except hiding (fail)
import Control.Monad.Error.Class ()
import Control.Monad.Writer.Strict
import Control.Monad.Writer.Class ()

import Lang.Crucible.Types

import Data.Foldable
import Data.Functor
import qualified Data.Functor.Product as Functor
import Data.Maybe
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.Map (MapF)
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx
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
import What4.Utils.MonadST

import Lang.Crucible.Syntax.SExpr (Syntax, pattern L, pattern A, toText, PrintRules(..), PrintStyle(..), syntaxPos, withPosFrom, showAtom)
import Lang.Crucible.Syntax.Atoms hiding (atom)

import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.Expr

import Lang.Crucible.FunctionHandle

import Numeric.Natural ()

liftSyntaxParse :: MonadError (ExprErr s) m => SyntaxParse Atomic a -> AST s -> m a
liftSyntaxParse p ast =
  case syntaxParse p ast of
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


newtype E s t = E { unE :: Expr () s t }
  deriving Show


data SomeExpr :: * -> * where
  SomeExpr :: TypeRepr t -> E s t -> SomeExpr s

deriving instance (Show (SomeExpr a))

data SomeVectorExpr :: * -> * where
  SomeVectorExpr :: TypeRepr t -> E s (VectorType t) -> SomeVectorExpr s

deriving instance (Show (SomeVectorExpr a))


data ExprErr s where
  TypeError :: Position -> AST s -> TypeRepr expected -> TypeRepr found -> ExprErr s
  AnonTypeError :: Position -> TypeRepr expected -> TypeRepr found -> ExprErr s
  TypeMismatch :: Position -> AST s -> TypeRepr left -> AST s -> TypeRepr right -> ExprErr s
  NotVector :: Position -> AST s -> TypeRepr tp -> ExprErr s
  BadSyntax :: Position -> AST s -> Text -> ExprErr s
  CantSynth :: Position -> AST s -> ExprErr s
  NotAType :: Position -> AST s -> ExprErr s
  NotANat :: Position -> Integer -> ExprErr s
  NotNumeric :: Position -> AST s -> TypeRepr t -> ExprErr s
  NotRef :: AST s -> TypeRepr t -> ExprErr s
  NotComparison :: Position -> AST s -> TypeRepr t -> ExprErr s
  NotABaseType :: Position -> TypeRepr t -> ExprErr s
  NotAVariantType :: Position -> TypeRepr t -> ExprErr s
  NotARefType :: Position -> TypeRepr t -> ExprErr s
  InvalidInjection :: AST s -> CtxRepr ctx -> Integer -> ExprErr s
  TrivialErr :: Position -> ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s
  TooSmall :: Position -> NatRepr n -> ExprErr s
  UnknownAtom :: Position -> AtomName -> ExprErr s
  UnknownGlobal :: Position -> GlobalName -> ExprErr s
  UnknownBlockLabel :: Position -> AST s -> ExprErr s
  UnknownFunction :: Position -> FunName -> ExprErr s
  DuplicateAtom :: Position -> AtomName -> ExprErr s
  DuplicateLabel :: Position -> LabelName -> ExprErr s
  NotArgumentSpec :: Position -> AST s -> ExprErr s
  NotFunctionName :: Position -> AST s -> ExprErr s
  NotFunDef :: Position -> AST s -> ExprErr s
  NotGlobal :: Position -> AST s -> ExprErr s
  NotArgumentList :: Position -> AST s -> ExprErr s
  NotTermStmt :: Position -> AST s -> ExprErr s
  EmptyFunBody :: Position -> ExprErr s
  EmptyBlock :: Position -> ExprErr s
  NotABlock :: Position -> AST s -> ExprErr s
  BadStatement :: Position -> AST s -> ExprErr s
  FirstBlockMustBeStart :: Position -> AST s -> ExprErr s
  CantJumpToLambda :: Position -> AST s -> ExprErr s
  CantThrowToNonLambda :: Position -> AST s -> ExprErr s
  NotAFunction :: Position -> AST s -> TypeRepr t -> ExprErr s
  NotAnAtom :: Position -> AST s -> ExprErr s
  WrongNumberOfArgs :: Position -> ExprErr s
  InvalidRegister :: Position -> AST s -> ExprErr s
  UnknownRegister :: Position -> RegName -> ExprErr s
  SyntaxError :: AST s -> Text -> ExprErr s
  WrongNumberOfCases :: AST s -> ExprErr s
  SyntaxParseError :: SP.SyntaxError Atomic -> ExprErr s

errPos :: ExprErr s -> Position
errPos (TypeError p _ _ _) = p
errPos (AnonTypeError p _ _) = p
errPos (TypeMismatch p _ _ _ _) = p
errPos (BadSyntax p _ _) = p
errPos (CantSynth p _) = p
errPos (NotAType p _) = p
errPos (NotANat p _) = p
errPos (NotNumeric p _ _) = p
errPos (NotComparison p _ _) = p
errPos (NotVector p _ _) = p
errPos (NotABaseType p _) = p
errPos (TrivialErr p) = p
errPos (Errs e1 e2) = best (errPos e1) (errPos e2)
  where best p@(SourcePos _ _ _) _ = p
        best _ p@(SourcePos _ _ _) = p
        best p@(BinaryPos _ _) _ = p
        best _ p@(BinaryPos _ _) = p
        best p@(OtherPos _) _ = p
        best _ p@(OtherPos _) = p
        best a _b = a
errPos (TooSmall p _) = p
errPos (UnknownAtom p _) = p
errPos (UnknownBlockLabel p _) = p
errPos (DuplicateAtom p _) = p
errPos (DuplicateLabel p _) = p
errPos (NotArgumentSpec p _) = p
errPos (NotFunctionName p _) = p
errPos (NotFunDef p _) = p
errPos (NotArgumentList p _) = p
errPos (NotTermStmt p _) = p
errPos (EmptyFunBody p) = p
errPos (EmptyBlock p) = p
errPos (NotABlock p _) = p
errPos (BadStatement p _) = p
errPos (FirstBlockMustBeStart p _) = p
errPos (CantJumpToLambda p _) = p
errPos (CantThrowToNonLambda p _) = p
errPos (NotAFunction p _ _) = p
errPos (NotAnAtom p _) = p
errPos (WrongNumberOfArgs p) = p
errPos (InvalidRegister p _) = p
errPos (UnknownRegister p _) = p
errPos (SyntaxError e _) = syntaxPos e
errPos (NotRef e _)  = syntaxPos e
errPos (UnknownFunction p _) = p
errPos (NotAVariantType p _) = p
errPos (InvalidInjection e _ _) = syntaxPos e
errPos (WrongNumberOfCases e) = syntaxPos e
errPos (NotGlobal p _) = p
errPos (NotARefType p _) = p
errPos (UnknownGlobal p _) = p
errPos (SyntaxParseError (SP.SyntaxError (Reason e _ :| _))) = syntaxPos e

deriving instance Show (ExprErr s)
instance Monoid (ExprErr s) where
  mempty = TrivialErr (OtherPos "mempty")
  mappend = Errs

printExprErr :: ExprErr s -> String
printExprErr = show


checkExpr :: (Alternative m, MonadError (ExprErr s) m, MonadState (SyntaxState h s) m)
          => TypeRepr t -> AST s -> m (E s t)

checkExpr t stx =
  do st <- get
     liftSyntaxParse (runReaderT (check' t) st) stx

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

rational :: MonadSyntax Atomic m => m Rational
rational = sideCondition "rational number literal" numeric atomic
  where numeric (Rat r) = Just r
        numeric _ = Nothing


string :: MonadSyntax Atomic m => m Text
string = sideCondition "string literal" stringy atomic
  where stringy (StrLit t) = Just t
        stringy _ = Nothing

atomName :: MonadSyntax Atomic m => m AtomName
atomName = sideCondition "Crucible atom" isCAtom atomic
  where isCAtom (At a) = Just a
        isCAtom _ = Nothing


bool :: MonadSyntax Atomic m => m  Bool
bool = sideCondition "Boolean literal" isBool atomic
  where isBool (Bool b) = Just b
        isBool _ = Nothing

funName :: MonadSyntax Atomic m => m  FunctionName
funName = functionNameFromText <$> sideCondition "function name" isFn atomic
  where isFn (Fn (FunName n)) = Just n
        isFn _ = Nothing

toCtx :: forall f . [Some f] -> Some (Ctx.Assignment f)
toCtx fs = toCtx' (reverse fs)
  where toCtx' :: [Some f] -> Some (Ctx.Assignment f)
        toCtx' [] = Some Ctx.empty
        toCtx' (Some x : (toCtx' -> Some xs)) =
          Some $ Ctx.extend xs x

unary :: MonadSyntax Atomic m => Keyword -> m a -> m a
unary k p = cons (kw k) (cons p emptyList) <&> fst . snd

binary :: MonadSyntax Atomic m => Keyword -> m a -> m b -> m (a, b)
binary k p1 p2 = cons (kw k) (cons p1 (cons p2 emptyList)) <&> \((), (x, (y, ()))) -> (x, y)


mkFunRepr :: [Some TypeRepr] -> Some TypeRepr -> Some TypeRepr
mkFunRepr (toCtx -> Some doms) (Some ran) = Some $ FunctionHandleRepr doms ran

repUntilLast :: MonadSyntax Atomic m => m a -> m ([a], a)
repUntilLast p = describe "zero or more followed by one" $ repUntilLast' p
  where repUntilLast' p =
          (cons p emptyList <&> \(x, ()) -> ([], x)) <|>
          (cons p (repUntilLast' p) <&> \(x, (xs, lst)) -> (x:xs, lst))


isType :: MonadError (ExprErr s) m => AST s -> m (Some TypeRepr)
isType ast = liftSyntaxParse isType' ast


isType' :: MonadSyntax Atomic m => m (Some TypeRepr)
isType' =
  describe "type" $
    atomicType <|> vector <|> ref <|> bv <|> fun <|> maybeT <|> var

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
    vector = unary VectorT isType' <&> \(Some t) -> Some (VectorRepr t)
    ref    = unary RefT isType' <&> \(Some t) -> Some (ReferenceRepr t)
    bv :: MonadSyntax Atomic m => m  (Some TypeRepr)
    bv     = do (Some len) <- unary BitVectorT (sideCondition "natural number" someNat int)
                describe "positive number" $
                  case testLeq (knownNat :: NatRepr 1) len of
                    Nothing -> empty
                    Just LeqProof -> return $ Some $ BVRepr len

    fun :: MonadSyntax Atomic m => m (Some TypeRepr)
    fun = cons (kw FunT) (repUntilLast isType') <&> \((), (args, ret)) -> mkFunRepr args ret

    maybeT = unary MaybeT isType' <&> \(Some t) -> Some (MaybeRepr t)
    var :: MonadSyntax Atomic m => m (Some TypeRepr)
    var = cons (kw VariantT) (rep isType') <&> \((), toCtx -> Some tys) -> Some (VariantRepr tys)


synth' :: forall m h s . MonadSyntax Atomic m => ReaderT (SyntaxState h s) m (SomeExpr s)
synth' =
  describe "synthesizable expression" $
    the <|> crucibleAtom <|> unitCon <|> boolLit <|> stringLit <|> funNameLit <|>
    notExpr <|> equalp <|> lessThan <|>
    toAny <|> fromAny <|>
    modulus <|>
    stringAppend <|> showExpr <|>
    vecRep <|> vecLen <|> vecEmptyP <|> vecGet <|> vecSet <|>
    binaryBool And_ And <|> binaryBool Or_ Or <|> binaryBool Xor_ BoolXor <|> ite <|>
    intp

  where
    the :: ReaderT (SyntaxState h s) m (SomeExpr s)
    the = do describe "type-annotated expression" $
               kw The `followedBy`
                 (depCons isType' $
                  \(Some t) ->
                    do (e, ()) <- cons (check' t) emptyList
                       return $ SomeExpr t e)



    okAtom theAtoms x =
      case Map.lookup x theAtoms of
        Nothing -> Nothing
        Just (Pair t anAtom) -> Just $ SomeExpr t (E (AtomExpr anAtom))

    crucibleAtom :: ReaderT (SyntaxState h s) m (SomeExpr s)
    crucibleAtom =
      do theAtoms <- view stxAtoms
         sideCondition "known atom" (okAtom theAtoms) atomName

    unitCon = describe "unit constructor" (emptyList $> SomeExpr UnitRepr (E (App EmptyApp)))

    boolLit = bool <&> SomeExpr BoolRepr . E . App . BoolLit

    stringLit = string <&> SomeExpr StringRepr . E . App . TextLit

    binaryBool k f =
      do (E x, E y) <- binary k (check' BoolRepr) (check' BoolRepr)
         return $ SomeExpr BoolRepr $ E $ App $ f x y


    intp =
      do E e <- unary Integerp (check' RealValRepr)
         return $ SomeExpr BoolRepr $ E $ App $ RealIsInteger e

    funNameLit =
      do fn <- funName
         fh <- view $ stxFunctions . at fn
         describe "known function name" $
           case fh of
             Nothing -> empty
             Just (FunctionHeader _ funArgs ret handle _) ->
               return $ SomeExpr (FunctionHandleRepr (argTypes funArgs) ret) (E (App $ HandleLit handle))

    notExpr =
      do E e <- describe "negation expression" $ unary Not_ (check' BoolRepr)
         return $ SomeExpr BoolRepr $ E $ App $ Not e

    equalp :: ReaderT (SyntaxState h s) m (SomeExpr s)
    equalp =
      do (SomeExpr t1 (E e1), SomeExpr t2 (E e2)) <-
           describe "equality test" $
           binary Equalp synth' synth'
         case testEquality t1 t2 of
           Just Refl ->
             case asBaseType t1 of
               NotBaseType -> later $ describe ("a base type (got " <> T.pack (show t1) <> ")") empty
               AsBaseType bt ->
                 return $ SomeExpr BoolRepr $ E $ App $ BaseIsEq bt e1 e2
           Nothing -> later $
                      describe (T.concat [ "matching types of branches "
                                         , T.pack (show t1)
                                         , " and "
                                         , T.pack (show t1)]) $
                      empty

    lessThan :: ReaderT (SyntaxState h s) m (SomeExpr s)
    lessThan =
      do (SomeExpr t1 (E e1), SomeExpr t2 (E e2)) <-
           binary Lt synth' synth'
         case testEquality t1 t2 of
           Nothing ->
             lift $
             describe (T.concat [ "expressions with the same type, got "
                                , T.pack (show t1), " and ", T.pack (show t2)
                                ]) $
             empty
           Just Refl ->
             case t1 of
               NatRepr     -> return $ SomeExpr BoolRepr $ E $ App $ NatLt e1 e2
               IntegerRepr -> return $ SomeExpr BoolRepr $ E $ App $ IntLt e1 e2
               RealValRepr -> return $ SomeExpr BoolRepr $ E $ App $ RealLt e1 e2
               other ->
                 describe ("valid comparison type (got " <> T.pack (show other) <> ")") empty


    ite :: ReaderT (SyntaxState h s) m (SomeExpr s)
    ite =
      do ((), (E c, (SomeExpr tTy (E t), (SomeExpr fTy (E f), ())))) <-
           cons (kw If) $
           cons (check' BoolRepr) $
           cons synth' $
           cons synth' $
           emptyList
         case testEquality tTy fTy of
           Nothing ->
             let msg = T.concat [ "conditional where branches have same type (got "
                                , T.pack (show tTy), " and "
                                , T.pack (show fTy)
                                ]
             in later $ describe msg empty
           Just Refl ->
             case asBaseType tTy of
               NotBaseType ->
                 let msg = T.concat [ "conditional where branches have base type (got "
                                    , T.pack (show tTy)
                                    ]
                 in later $ describe msg empty
               AsBaseType bTy ->
                 return $ SomeExpr tTy $ E $ App $ BaseIte bTy c t f

    modulus =
      do (E e1, E e2) <- binary Mod (check' RealValRepr) (check' RealValRepr)
         return $ SomeExpr RealValRepr $ E $ App $ RealMod e1 e2


    toAny =
      (unary ToAny synth') <&>
        \(SomeExpr ty (E e)) -> SomeExpr AnyRepr (E (App (PackAny ty e)))
    fromAny =
      (binary FromAny isType' (check' AnyRepr)) <&>
        \(Some ty, E e) -> SomeExpr (MaybeRepr ty) (E (App (UnpackAny ty e)))

    stringAppend =
      do (E s1, E s2) <-
           binary StringAppend (check' StringRepr) (check' StringRepr)
         return $ SomeExpr StringRepr $ E $ App $ AppendString s1 s2

    vecRep =
      do (E n, SomeExpr t (E e)) <-
           binary VectorReplicate_ (check' NatRepr) synth'
         return $ SomeExpr (VectorRepr t) $ E $ App $ VectorReplicate t n e

    vecLen :: ReaderT (SyntaxState h s) m (SomeExpr s)
    vecLen =
      do SomeExpr t (E e) <- unary VectorSize_ synth'
         case t of
           VectorRepr _ -> return $ SomeExpr NatRepr $ E $ App $ VectorSize e
           other -> lift $ later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecEmptyP :: ReaderT (SyntaxState h s) m (SomeExpr s)
    vecEmptyP =
      do SomeExpr t (E e) <- unary VectorIsEmpty_ synth'
         case t of
           VectorRepr _ -> return $ SomeExpr BoolRepr $ E $ App $ VectorIsEmpty e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecGet :: ReaderT (SyntaxState h s) m (SomeExpr s)
    vecGet =
      do (SomeExpr t (E e), E n) <-
           binary VectorGetEntry_ synth' (check' NatRepr)
         case t of
           VectorRepr elemT -> return $ SomeExpr elemT $ E $ App $ VectorGetEntry elemT e n
           other -> lift $ later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    someVec :: SomeExpr t -> Maybe (SomeVectorExpr t)
    someVec (SomeExpr (VectorRepr t) e) = Just (SomeVectorExpr t e)
    someVec _ = Nothing

    synthVec = sideCondition "expression with vector type" someVec synth'

    vecSet :: ReaderT (SyntaxState h s) m (SomeExpr s)
    vecSet =
      do kw VectorSetEntry_ `followedBy`
           (depCons synthVec $
            \(SomeVectorExpr t (E vec)) ->
              do (E n, (E elt, ())) <- cons (check' NatRepr) $
                                       cons (check' t) $
                                       emptyList
                 return $ SomeExpr (VectorRepr t) $ E $ App $ VectorSetEntry t vec n elt)


    showExpr :: ReaderT (SyntaxState h s) m (SomeExpr s)
    showExpr =
      do SomeExpr t1 (E e) <- unary Show synth'
         case asBaseType t1 of
           NotBaseType -> describe ("base type, but got " <> T.pack (show t1)) empty
           AsBaseType bt ->
             return $ SomeExpr StringRepr $ E $ App $ ShowValue bt e

check' :: forall m t h s . MonadSyntax Atomic m => TypeRepr t -> ReaderT (SyntaxState h s) m (E s t)
check' t =
  describe ("inhabitant of " <> T.pack (show t)) $
    literal <|> unpack <|> just <|> nothing <|> fromJust_ <|> injection <|>
    addition <|> subtraction <|> multiplication <|> division <|>
    vecLit <|> vecCons <|> modeSwitch
  where
    typed :: TypeRepr t' -> ReaderT (SyntaxState h s) m (E s t')
          -> ReaderT (SyntaxState h s) m (E s t)
    typed t' p =
      case testEquality t' t of
        Just Refl -> p
        Nothing -> empty

    literal = natLiteral <|> intLiteral <|> rationalLiteral

    natLiteral =
      typed NatRepr $
        lift $ sideCondition "nat literal" isNat int
      where isNat i | i >= 0 = Just (E (App (NatLit (fromInteger i))))
            isNat _ = Nothing

    intLiteral =
      typed IntegerRepr (lift int <&> E . App . IntLit . fromInteger)

    rationalLiteral =
      typed RealValRepr $
        (rational <&> E . App . RationalLit) <|>
        (int <&> \i -> E $ App $ RationalLit (i % 1))

    unpack =
      do package <- unary Unpack anything
         describe "context expecting Maybe" $
           case t of
             MaybeRepr expected ->
               do E e <- withProgress Rest $ withProgress SP.First $
                         parse package $ check' AnyRepr
                  return $ E $ App (UnpackAny expected e)
             _ -> empty

    just =
      do inj <- lift $ unary Just_ anything
         describe "context expecting Maybe" $
           case t of
             MaybeRepr expected ->
               do E e <- withProgress Rest $ withProgress SP.First $
                         parse inj $ check' expected
                  return $ E $ App (JustValue expected e)
             _ -> empty

    nothing =
      lift $ describe "context expecting Maybe" $
        case t of
          MaybeRepr expected ->
            do kw Nothing_
               return $ E $ App (NothingValue expected)
          _ -> empty

    fromJust_ =
      do describe "coercion from Maybe (fromJust-expression)" $
           followedBy (kw FromJust) $
           depCons (check' (MaybeRepr t)) $
             \ (E e) ->
               depCons (check' StringRepr) $
                 \ (E str) ->
                   do emptyList
                      return $ E $ App $ FromJustValue t e str

    injection =
      do ((), (n, (e, ()))) <- lift $ describe "injection into variant type" $
                               cons (kw Inj) $ cons int $ cons anything $ emptyList
         case t of
           VariantRepr ts ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 lift $
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = view (ixF' idx) ts
                    E out <- withProgress Rest $ withProgress Rest $ withProgress SP.First $
                             parse e (check' ty)
                    return $ E $ App $ InjectVariant ts idx out
           _ -> lift $ describe ("context expecting variant type (got " <> T.pack (show t) <> ")") empty

    addition =
      arith t NatRepr Plus NatAdd <|>
      arith t IntegerRepr Plus IntAdd <|>
      arith t RealValRepr Plus RealAdd

    subtraction =
      arith t NatRepr Minus NatSub <|>
      arith t IntegerRepr Minus IntSub <|>
      arith t RealValRepr Minus RealSub

    multiplication =
      arith t NatRepr Times NatMul <|>
      arith t IntegerRepr Times IntMul <|>
      arith t RealValRepr Times RealMul

    division =
      arith t RealValRepr Div RealDiv


    arith :: TypeRepr t1 -> TypeRepr t2
          -> Keyword
          -> (Expr () s t2 -> Expr () s t2 -> App () (Expr () s) t2)
          -> ReaderT (SyntaxState h s) m (E s t1)
    arith t1 t2 k f =
      case testEquality t1 t2 of
        Nothing ->
          lift $
          describe ("arithmetic expression beginning with " <> T.pack (show k) <> " type " <>  (T.pack (show t2)))
            empty
        Just Refl ->
          -- describe ("arithmetic expression of type " <> T.pack (show t2)) $
          followedBy (kw k) $
          depCons (check' t1) $
            \ (E e1) ->
              depCons (check' t1) $
                \ (E e2) ->
                  do emptyList
                     return $ E $ App $ f e1 e2

    vecLit =
      describe "vector literal" $
      followedBy (kw VectorLit_) $
      (pure () <|> cut) *>
      case t of
        VectorRepr elemTy ->
          do es <- rep $ check' elemTy
             return $ E $ App $ VectorLit elemTy (V.fromList (map unE es))
        _ -> lift $ describe ("context expecting a vector") $ empty

    vecCons =
      case t of
        VectorRepr elemTy ->
          do (E a, E d) <- binary VectorCons_
                             (check' elemTy)
                             (check' (VectorRepr elemTy))
             return $ E $ App $ VectorCons elemTy a d
        _ -> empty


    modeSwitch :: ReaderT (SyntaxState h s) m (E s t)
    modeSwitch =
      do SomeExpr t' e <- synth'
         later $ describe ("a " <> T.pack (show t) <> " rather than a " <> T.pack (show t')) $
           case testEquality t t' of
             Nothing -> later empty
             Just Refl -> return e

synthExpr :: (MonadError (ExprErr s) m, MonadState (SyntaxState h s) m)
          => AST s
          -> m (SomeExpr s)
synthExpr stx =
  do st <- get
     liftSyntaxParse (runReaderT synth' st) stx



-------------------------------------------------------------------------

data LabelInfo :: * -> * where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . TypeRepr ty -> LambdaLabel s ty -> LabelInfo s

data ProgramState h s =
  ProgramState { _progFunctions :: Map FunctionName FunctionHeader
               , _progGlobals :: Map GlobalName (Pair TypeRepr GlobalVar)
               , _progHandleAlloc :: HandleAllocator h
               }

progFunctions :: Simple Lens (ProgramState h s) (Map FunctionName FunctionHeader)
progFunctions = lens _progFunctions (\s v -> s { _progFunctions = v })

progGlobals :: Simple Lens (ProgramState h s) (Map GlobalName (Pair TypeRepr GlobalVar))
progGlobals = lens _progGlobals (\s v -> s { _progGlobals = v })

progHandleAlloc :: Simple Lens (ProgramState h s) (HandleAllocator h)
progHandleAlloc = lens _progHandleAlloc (\s v -> s { _progHandleAlloc = v })


data SyntaxState h s =
  SyntaxState { _stxLabels :: Map LabelName (LabelInfo s)
              , _stxAtoms :: Map AtomName (Pair TypeRepr (Atom s))
              , _stxRegisters :: Map RegName (Pair TypeRepr (Reg s))
              , _stxNextLabel :: Int
              , _stxNextAtom :: Int
              , _stxProgState :: ProgramState h s
              }

initProgState :: HandleAllocator h -> ProgramState h s
initProgState = ProgramState Map.empty Map.empty

initSyntaxState :: ProgramState h s -> SyntaxState h s
initSyntaxState = SyntaxState Map.empty Map.empty Map.empty 0 0

stxLabels :: Simple Lens (SyntaxState h s) (Map LabelName (LabelInfo s))
stxLabels = lens _stxLabels (\s v -> s { _stxLabels = v })

stxAtoms :: Simple Lens (SyntaxState h s) (Map AtomName (Pair TypeRepr (Atom s)))
stxAtoms = lens _stxAtoms (\s v -> s { _stxAtoms = v })

stxRegisters :: Simple Lens (SyntaxState h s) (Map RegName (Pair TypeRepr (Reg s)))
stxRegisters = lens _stxRegisters (\s v -> s { _stxRegisters = v })


stxNextLabel :: Simple Lens (SyntaxState h s) Int
stxNextLabel = lens _stxNextLabel (\s v -> s { _stxNextLabel = v })

stxNextAtom :: Simple Lens (SyntaxState h s) Int
stxNextAtom = lens _stxNextAtom (\s v -> s { _stxNextAtom = v })

stxProgState :: Simple Lens (SyntaxState h s) (ProgramState h s)
stxProgState = lens _stxProgState (\s v -> s { _stxProgState = v })

stxFunctions :: Simple Lens (SyntaxState h s) (Map FunctionName FunctionHeader)
stxFunctions = stxProgState . progFunctions

stxGlobals :: Simple Lens (SyntaxState h s) (Map GlobalName (Pair TypeRepr GlobalVar))
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

getReturnType :: CFGParser h s ret (TypeRepr ret)
getReturnType = CFGParser $ return ?returnType

freshIndex :: (MonadState st m, Num n) => Simple Lens st n -> m n
freshIndex l =
  do n <- use l
     l .= n + 1
     return n

freshLabelIndex :: MonadState (SyntaxState h s) m => m Int
freshLabelIndex = freshIndex stxNextLabel

freshAtomIndex :: MonadState (SyntaxState h s) m => m Int
freshAtomIndex = freshIndex stxNextAtom

freshLabel :: MonadState (SyntaxState h s) m => m (Label s)
freshLabel = Label <$> freshLabelIndex

freshAtom :: AST s -> AtomValue () s t -> WriterT [Posd (Stmt () s)] (CFGParser h s ret) (Atom s t)
freshAtom e v =
  do i <- lift freshAtomIndex
     let theAtom = Atom { atomPosition = OtherPos "Parser internals"
                        , atomId = i
                        , atomSource = Assigned
                        , typeOfAtom = typeOfAtomValue v
                        }
         stmt = DefineAtom theAtom v
     tell [withPosFrom e stmt]
     pure theAtom

newLabel :: LabelName -> CFGParser h s ret (Label s)
newLabel x =
  do theLbl <- freshLabel
     stxLabels %= Map.insert x (NoArgLbl theLbl)
     return theLbl

freshLambdaLabel :: MonadState (SyntaxState h s) m => TypeRepr tp -> m (LambdaLabel s tp, Atom s tp)
freshLambdaLabel t =
  do n <- freshLabelIndex
     i <- freshAtomIndex
     let lbl = LambdaLabel n a
         a   = Atom { atomPosition = OtherPos "Parser internals"
                    , atomId = i
                    , atomSource = LambdaArg lbl
                    , typeOfAtom = t
                    }
     return (lbl, a)

with :: MonadState s m => Lens' s a -> (a -> m b) -> m b
with l act = do x <- use l; act x

newLambdaLabel :: Position -> LabelName -> AtomName -> TypeRepr t -> CFGParser h s ret (LambdaLabel s t)
newLambdaLabel p l x t =
  do with (stxLabels . at l) $ maybe (return ()) (const $ throwError $ DuplicateLabel p l)
     with (stxAtoms . at x) $ maybe (return ()) (const $ throwError $ DuplicateAtom p x)
     (lbl, anAtom) <- freshLambdaLabel t
     stxLabels %= Map.insert l (ArgLbl t lbl)
     stxAtoms %= Map.insert x (Pair t anAtom) -- TODO check for duplicate atoms here
     return lbl

getLabel :: LabelName -> CFGParser h s ret (LabelInfo s)
getLabel x =
  with (stxLabels . at x) $ \case
    Just lbl -> return lbl
    Nothing -> NoArgLbl <$> newLabel x

label :: AST s -> CFGParser h s ret (LabelInfo s)
label (A (Lbl x)) = getLabel x
label other = throwError $ UnknownBlockLabel (syntaxPos other) other

labelNoArgs :: AST s -> CFGParser h s ret (Label s)
labelNoArgs ast =
  label ast >>= \case
    NoArgLbl l -> return l
    ArgLbl _t _l -> throwError $ CantJumpToLambda (syntaxPos ast) ast

labelArgs :: AST s -> CFGParser h s ret (Pair TypeRepr (LambdaLabel s))
labelArgs ast =
  label ast >>= \case
    NoArgLbl _l -> throwError $ CantThrowToNonLambda (syntaxPos ast) ast
    ArgLbl t l -> return (Pair t l)


newUnassignedReg :: MonadState (SyntaxState h s) m => TypeRepr t -> m (Reg s t)
newUnassignedReg t =
  do i <- freshAtomIndex
     let fakePos = OtherPos "Parser internals"
     return $! Reg { regPosition = fakePos
                   , regId = i
                   , typeOfReg = t
                   }

regRef :: (MonadError (ExprErr s) m, MonadState (SyntaxState h s) m) => AST s -> m (Pair TypeRepr (Reg s))
regRef e@(A (Rg x)) =
  do perhapsReg <- use (stxRegisters . at x)
     case perhapsReg of
       Just reg -> return reg
       Nothing -> throwError $ UnknownRegister (syntaxPos e) x
regRef other = throwError $ InvalidRegister (syntaxPos other) other



--------------------------------------------------------------------------



-- | Build an ordinary statement
normStmt :: AST s -> WriterT [Posd (Stmt () s)] (CFGParser h s ret) ()
normStmt stmt@(L [A (Kw Print_), e]) =
  do (E e') <- lift $ checkExpr StringRepr e
     strAtom <- eval e e'
     tell [withPosFrom stmt $ Print strAtom]
normStmt stmt@(L [A (Kw Let), A (At an), e]) =
  do Pair tp resAtom <- atomValue e
     stxAtoms %= Map.insert an (Pair tp resAtom)
  where
    atomValue stx@(A (Rg _)) =
      do Pair t r <- regRef stx
         resAtom <- freshAtom stmt (ReadReg r)
         return $ Pair t resAtom
    -- no case for EvalExt because we don't have exts
    atomValue ex@(A (Gl x)) =
      do perhapsGlobal <- use (stxGlobals . at x)
         case perhapsGlobal of
           Nothing -> throwError $ UnknownGlobal (syntaxPos ex) x
           Just (Pair t var) ->
             do resAtom <- freshAtom stmt (ReadGlobal var)
                return $ Pair t resAtom
    atomValue stx@(L [A (Kw Deref), ex]) =
      do SomeExpr t (E ex') <- synthExpr ex
         case t of
           ReferenceRepr t' ->
             do anAtom <- eval ex ex'
                anotherAtom <- freshAtom stmt (ReadRef anAtom)
                return $ Pair t' anotherAtom
           notRef -> throwError $ NotRef stx notRef
    atomValue (L [A (Kw Ref), refE]) =
      do SomeExpr t (E e') <- synthExpr refE
         anAtom <- eval refE e'
         anotherAtom <- freshAtom stmt (NewRef anAtom)
         return $ Pair (ReferenceRepr t) anotherAtom
    atomValue (L [A (Kw EmptyRef), t]) =
      do Some t' <- isType t
         anAtom <- freshAtom stmt (NewEmptyRef t')
         return $ Pair (ReferenceRepr t') anAtom
    atomValue (L (A (Kw Funcall) : fun : args)) =
      do SomeExpr t (E fun') <- synthExpr fun
         case t of
           FunctionHandleRepr funArgs ret ->
             do funAtom <- eval fun fun'
                operandExprs <- lift $ operands (syntaxPos fun) args funArgs
                operandAtoms <- traverseFC (\(Rand a (E ex)) -> eval a ex) operandExprs
                endAtom <- freshAtom stmt $ Call funAtom operandAtoms ret
                return $ Pair ret endAtom
           other -> throwError $ NotAFunction (syntaxPos fun) fun other
    atomValue expr =
      do SomeExpr tp (E e') <- lift $ synthExpr expr
         anAtom <- eval expr e'
         return $ Pair tp anAtom
normStmt stmt@(L [A (Kw SetGlobal), gl@(A (Gl g)), e]) =
  do perhapsG <- use (stxGlobals . at g)
     case perhapsG of
       Nothing -> throwError $ UnknownGlobal (syntaxPos gl) g
       Just (Pair t var) ->
         do E e' <- checkExpr t e
            a <- eval e e'
            tell [withPosFrom stmt $ WriteGlobal var a]
normStmt stmt@(L [A (Kw SetRegister), regStx, e]) =
  do Pair ty r <- lift $ regRef regStx
     (E e') <- lift $ checkExpr ty e
     v <- eval e e'
     tell [withPosFrom stmt $ SetReg r v]
normStmt stmt@(L [A (Kw SetRef), ref, val]) =
  do SomeExpr t (E refE) <- synthExpr ref
     case t of
       ReferenceRepr t' ->
         do E valE <- checkExpr t' val
            refAtom <- eval ref refE
            valAtom <- eval val valE
            tell [withPosFrom stmt $ WriteRef refAtom valAtom]
       other -> throwError $ NotARefType (syntaxPos ref) other
normStmt stmt@(L [A (Kw DropRef_), ref]) =
  do SomeExpr t (E refE) <- synthExpr ref
     case t of
       ReferenceRepr _ ->
         do refAtom <- eval ref refE
            tell [withPosFrom stmt $ DropRef refAtom]
       other -> throwError $ NotARefType (syntaxPos ref) other
normStmt stmt@(L [A (Kw Assert_), cond, message]) =
  do E cond' <- checkExpr BoolRepr cond
     E message' <- checkExpr StringRepr message
     cond'' <- eval cond cond'
     message'' <- eval message message'
     tell [withPosFrom stmt $ Assert cond'' message'']
normStmt other = throwError $ BadStatement (syntaxPos other) other

blockBody :: forall s h ret . Position -> [AST s] -> CFGParser h s ret ([Posd (Stmt () s)], Posd (TermStmt s ret))
blockBody p [] = throwError $ EmptyBlock p
blockBody _p (stmt:stmts) = helper (fmap snd . runWriterT . traverse normStmt) stmt stmts
  where helper ss s [] =
          (,) <$> ss [] <*> termStmt s
        helper ss s (s':ss') =
          helper (\x -> (ss (s : x))) s' ss'


typedAtom :: (MonadError (ExprErr s) m, MonadState (SyntaxState h s) m) => Position -> TypeRepr a -> AtomName -> m (Atom s a)
typedAtom p ty x =
  do perhapsAtom <- use (stxAtoms . at x)
     case perhapsAtom of
       Nothing -> throwError $ UnknownAtom p x
       Just (Pair ty' at') ->
         case testEquality ty ty' of
           Just Refl -> return at'
           Nothing -> throwError $ AnonTypeError p ty ty'


typedAtom' :: (MonadError (ExprErr s) m, MonadState (SyntaxState h s) m) => TypeRepr a -> AST s -> m (Atom s a)
typedAtom' ty e@(A (At x)) =
  do perhapsAtom <- use (stxAtoms . at x)
     case perhapsAtom of
       Nothing -> throwError $ UnknownAtom (syntaxPos e) x
       Just (Pair ty' at') ->
         case testEquality ty ty' of
           Just Refl -> return at'
           Nothing -> throwError $ AnonTypeError (syntaxPos e) ty ty'
typedAtom' _ other = throwError $ NotAnAtom (syntaxPos other) other


-- termStmt' :: MonadSyntax Atomic m => ReaderT (SyntaxState h s) m (Posd (TermStmt s ret))
-- termStmt' =
--   do stx <- anything
--      withPosFrom stx <$> jump

--   where
--     normalLabel =
--       _foo labelName
    
--     jump = unary Jump_ normalLabel <&> Jump

termStmt :: forall h s ret . AST s -> CFGParser h s ret (Posd (TermStmt s ret))
-- termStmt stx =
--   do st <- get
--      liftSyntaxParse (runReaderT termStmt' st) stx
termStmt stx@(L [A (Kw Jump_), lbl]) =
  withPosFrom stx . Jump <$> labelNoArgs lbl
termStmt stx@(L [A (Kw Branch_), A (At c), l1, l2]) =
  withPosFrom stx <$> (Br <$> typedAtom (syntaxPos stx) BoolRepr c <*> labelNoArgs l1 <*> labelNoArgs l2)
termStmt stx@(L [A (Kw MaybeBranch_), A (At c), l1, l2]) =
  do Pair ty' l1' <- labelArgs l1
     withPosFrom stx <$>
       (MaybeBranch ty' <$>
        typedAtom (syntaxPos stx) (MaybeRepr ty') c <*>
        pure l1' <*>
        labelNoArgs l2)
termStmt stx@(L (A (Kw Case) : aStx@(A (At c)) : branches)) =
  do perhapsAtom <- use (stxAtoms . at c)
     case perhapsAtom of
       Nothing -> throwError $ UnknownAtom (syntaxPos stx) c
       Just (Pair (VariantRepr vars) tgt) ->
         do labels <- branchCtx (Ctx.viewAssign vars) (reverse branches)
            return $ withPosFrom stx $ VariantElim vars tgt labels
       Just (Pair otherType _) ->
         throwError $ NotAVariantType (syntaxPos aStx) otherType
  where branchCtx :: forall cases
                   . Ctx.AssignView TypeRepr cases -> [AST s]
                  -> CFGParser h s ret (Ctx.Assignment (LambdaLabel s) cases)
        branchCtx Ctx.AssignEmpty [] =
          return Ctx.empty
        branchCtx (Ctx.AssignExtend c' t) (l:ls) =
          do rest <- branchCtx (Ctx.viewAssign c') ls
             Pair t' lbl <- labelArgs l
             case testEquality t t' of
               Nothing -> throwError $ TypeError (syntaxPos l) l t t'
               Just Refl ->
                 return $ Ctx.extend rest lbl
        branchCtx _ _ = throwError $ WrongNumberOfCases stx
termStmt stx@(L (A (Kw Return_) : more)) =
  case more of
    [] -> throwError $ BadSyntax (syntaxPos stx) stx "Not enough arguments to return"
    [A (At x)] ->
      do ret <- getReturnType
         withPosFrom stx . Return <$> typedAtom (syntaxPos stx) ret x
    [_] -> throwError $ BadSyntax (syntaxPos stx) stx "Not a literal atom in argument to return"
    _ -> throwError $ BadSyntax (syntaxPos stx) stx "Too many arguments to return"
termStmt stx@(L (A (Kw TailCall_) : atomAst@(A (At f)) : args)) =
  do ret <- getReturnType
     perhapsAtom <- use (stxAtoms . at f)
     case perhapsAtom of
       Nothing -> throwError $ UnknownAtom (syntaxPos stx) f
       Just (Pair (FunctionHandleRepr argumentTypes ret') funAtom) ->
         case testEquality ret ret' of
           Nothing -> throwError $ TypeError (syntaxPos stx) atomAst ret ret'
           Just Refl ->
             do theArgs <- argAtoms (syntaxPos stx) (toSnoc args) argumentTypes
                return $ withPosFrom stx (TailCall funAtom argumentTypes theArgs)
       Just (Pair otherType _) -> throwError $ NotAFunction (syntaxPos stx) atomAst otherType
termStmt stx@(L [A (Kw Error_), msg]) =
  withPosFrom stx . ErrorStmt <$> typedAtom' StringRepr msg
termStmt stx@(L [A (Kw Output_), l, atm]) =
  do Pair ty lbl <- labelArgs l
     argAtom <- typedAtom' ty atm
     return $ withPosFrom stx (Output lbl argAtom)
termStmt e = throwError $ NotTermStmt (syntaxPos e) e

data SnocList a = Begin | Snoc (SnocList a) a

toSnoc :: [a] -> SnocList a
toSnoc = foldl Snoc Begin

data Rand s t = Rand (AST s) (E s t)

operands :: Position -> [AST s] -> Ctx.Assignment TypeRepr args -> CFGParser h s ret (Ctx.Assignment (Rand s) args)
operands fpos argexprs argtypes = operands' (reverse argexprs) (Ctx.viewAssign argtypes)
  where
    operands' :: [AST s] -> Ctx.AssignView TypeRepr args -> CFGParser h s ret (Ctx.Assignment (Rand s) args)
    operands' [] Ctx.AssignEmpty = return Ctx.empty
    operands' (a:as) (Ctx.AssignExtend theArgTypes anArgType) =
      do a' <- checkExpr anArgType a
         rest <- operands' as (Ctx.viewAssign theArgTypes)
         return $ Ctx.extend rest (Rand a a')
    operands' _ _ = throwError $ WrongNumberOfArgs (findPosition argexprs)
    findPosition [] = fpos
    findPosition (e : _) = syntaxPos e

argAtoms :: Position -> SnocList (AST s) -> CtxRepr ctx -> CFGParser h s ret (Ctx.Assignment (Atom s) ctx)
argAtoms p xs ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty ->
      case xs of
        Begin -> pure Ctx.empty
        Snoc _ _ -> throwError $ WrongNumberOfArgs p
    Ctx.AssignExtend ctx' ty ->
      case xs of
        Begin -> throwError $ WrongNumberOfArgs p
        Snoc xs' x ->
          do more <- argAtoms (syntaxPos x) xs' ctx'
             thisOne <- typedAtom' ty x
             return $ Ctx.extend more thisOne


--------------------------------------------------------------------------

-- | Any CFG, regardless of its arguments and return type, with its helpers
data ACFG :: * where
  ACFG :: forall (s :: *) (init :: Ctx CrucibleType) (ret :: CrucibleType) .
          CtxRepr init -> TypeRepr ret ->
          CFG () s init ret ->
          ACFG

deriving instance Show ACFG

data Arg t = Arg AtomName Position (TypeRepr t)

arg :: AST s -> TopParser h s (Some Arg)
arg a@(L [A (At x), t]) =
  do Some t' <- isType t
     return $ Some $ Arg x (syntaxPos a) t'
arg other = throwError $ NotArgumentSpec (syntaxPos other) other


arguments :: AST s -> Some (Ctx.Assignment Arg) -> TopParser h s (Some (Ctx.Assignment Arg))
arguments (L xs) = args' xs
  where
    args' [] soFar = return soFar
    args' (a : as) (Some soFar) =
      do Some (Arg x p t) <- arg a
         args' as (Some $ Ctx.extend soFar (Arg x p t))
arguments other = const . throwError $ NotArgumentList (syntaxPos other) other


funName' :: MonadError (ExprErr s) m => AST s -> m FunctionName
funName' (A (Fn (FunName x))) = pure $ functionNameFromText x
funName' other = throwError $ NotFunctionName (syntaxPos other) other


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
                  stxNextAtom %= max (atomId y + 1)

data FunctionHeader =
  forall args ret .
  FunctionHeader { headerName :: FunctionName
                 , headerArgs :: Ctx.Assignment Arg args
                 , headerReturnType :: TypeRepr ret
                 , headerHandle :: FnHandle args ret
                 , headerLoc :: Position
                 }

data FunctionSource s =
  FunctionSource { functionRegisters :: [AST s]
                 , functionBody :: [AST s]
                 }

functionHeader :: AST s -> TopParser h s (FunctionHeader, FunctionSource s)
functionHeader defun@(L (A (Kw Defun) : name : arglist : ret : rest)) =
  do fnName <- funName' name
     Some theArgs <- arguments arglist (Some Ctx.empty)
     Some ty <- isType ret
     let (regs, body) = getRegisters rest
     ha <- use $ stxProgState  . progHandleAlloc
     handle <- liftST $ mkHandle' ha fnName (argTypes theArgs) ty

     let header = FunctionHeader fnName theArgs ty handle (syntaxPos defun)
     saveHeader fnName header
     return $ (header, FunctionSource regs body)
  where getRegisters (L (A (Kw Registers) : regs) : more) = (regs, more)
        getRegisters other = ([], other)
        saveHeader n h =
          stxFunctions %= Map.insert n h
functionHeader other = throwError $ NotFunDef (syntaxPos other) other

global :: AST s -> TopParser h s (Pair TypeRepr GlobalVar)
global (L [A (Kw DefGlobal), A (Gl var@(GlobalName varName)), ty]) =
  do Some t <- isType ty
     ha <- use $ stxProgState  . progHandleAlloc
     v <- liftST $ freshGlobalVar ha varName t
     stxGlobals %= Map.insert var (Pair t v)
     return $ Pair t v
global other = throwError $ NotGlobal (syntaxPos other) other

topLevel :: AST s -> TopParser h s (Maybe (FunctionHeader, FunctionSource s))
topLevel ast =
  catchError (Just <$> functionHeader ast) $
    \e ->
      catchError (global ast $> Nothing) $
        \_ -> throwError e

argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ _ t) -> t)


type BlockTodo h s ret =
  (LabelName, BlockID s, Position, [AST s])

blocks :: forall h s ret . Position -> [AST s] -> CFGParser h s ret [Block () s ret]
blocks funPos [] = throwError $ EmptyFunBody funPos
blocks _      (aBlock:moreBlocks) =
  do startContents <- startBlock aBlock
     todo <- allBlockLabels moreBlocks
     blockDefs <- forM (startContents : todo) $ \(_, bid, loc, stmts) ->
       do (stmts', term) <- blockBody loc stmts
          pure $ mkBlock bid mempty (Seq.fromList stmts') term
     return $ blockDefs

  where
    bodyPos fun [] = syntaxPos fun
    bodyPos _ (x:_) = syntaxPos x

    startBlock :: AST s -> CFGParser h s ret (BlockTodo h s ret)
    startBlock (L (kw@(A (Kw Start)) : (A (Lbl l)) : stmts)) =
      do lbl <- newLabel l
         stxLabels %= Map.insert l (NoArgLbl lbl)
         return (l, LabelID lbl, bodyPos kw stmts, stmts)
    startBlock other = throwError $ FirstBlockMustBeStart (syntaxPos other) other

    allBlockLabels :: [AST s] -> CFGParser h s ret [BlockTodo h s ret]
    allBlockLabels = traverse blockLabel
      where blockLabel :: AST s -> CFGParser h s ret (BlockTodo h s ret)
            blockLabel start@(L (A (Kw Start) : (A (Lbl _)) : _)) =
              throwError $ FirstBlockMustBeStart (syntaxPos start) start
            blockLabel (L (kw@(A (Kw DefBlock)) : lStx@(A (Lbl l)) : body)) =
              do lbls <- use stxLabels
                 case Map.lookup l lbls of
                   Just _ -> throwError $ DuplicateLabel (syntaxPos lStx) l
                   Nothing ->
                     do theLbl <- newLabel l
                        return (l, LabelID theLbl, bodyPos kw body, body)
            blockLabel (L (kw@(A (Kw DefBlock)) : lStx@(L [(A (Lbl l)), A (At x), t]) : body)) =
              do Some ty <- isType t
                 lbls <- use stxLabels
                 case Map.lookup l lbls of
                   Just _ -> throwError $ DuplicateLabel (syntaxPos lStx) l
                   Nothing ->
                     do lbl <- newLambdaLabel (syntaxPos lStx) l x ty
                        let lblInfo = ArgLbl ty lbl
                        stxLabels %= Map.insert l lblInfo
                        argAtom <- pure $ lambdaAtom lbl
                        stxAtoms %= Map.insert x (Pair ty argAtom)
                        return (l, LambdaID lbl, bodyPos kw body, body)

            blockLabel other = throwError $ NotABlock (syntaxPos other) other

eval :: AST s -> Expr () s t -> WriterT [Posd (Stmt () s)] (CFGParser h s ret) (Atom s t)
eval stx (App e)            = freshAtom stx . EvalApp =<< traverseFC (eval stx) e
eval _   (AtomExpr theAtom) = pure theAtom -- The expression is already evaluated


newtype TopParser h s a =
  TopParser { runTopParser :: ExceptT (ExprErr s)
                                (StateT (SyntaxState h s) (ST h))
                                a
            }
  deriving (Functor)

top :: TopParser h s a -> ST h (Either (ExprErr s) a)
top (TopParser (ExceptT (StateT act))) =
  do ha <- newHandleAllocator
     fst <$> act (initSyntaxState (initProgState ha))

instance Applicative (TopParser h s) where
  pure x = TopParser (pure x)
  (TopParser f) <*> (TopParser x) = TopParser (f <*> x)

instance Alternative (TopParser h s) where
  empty = TopParser $ throwError (TrivialErr InternalPos)
  (TopParser x) <|> (TopParser y) = TopParser (x <|> y)

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


parseCFG :: (?returnType :: TypeRepr ret)
         => FnHandle init ret
         -> CFGParser h s ret [Block () s ret]
         -> TopParser h s (CFG () s init ret)
parseCFG h (CFGParser act) = CFG h <$> TopParser act


initParser :: (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m)
           => FunctionHeader
           -> FunctionSource s
           -> m ()
initParser (FunctionHeader _ (funArgs :: Ctx.Assignment Arg init) _ _ _) (FunctionSource regs _) =
  do with stxProgState $ put . initSyntaxState
     let types = argTypes funArgs
     let inputAtoms = mkInputAtoms (OtherPos "args") types
     saveArgs funArgs inputAtoms
     forM_ regs saveRegister

  where
    saveRegister (L [A (Rg x), t]) =
      do Some ty <- isType t
         r <- newUnassignedReg ty
         stxRegisters %= Map.insert x (Pair ty r)
    saveRegister other = throwError $ InvalidRegister (syntaxPos other) other



cfgs :: [AST s] -> TopParser h s [ACFG]
cfgs defuns =
  do headers <- catMaybes <$> traverse topLevel defuns
     forM headers $
       \(hdr@(FunctionHeader _ funArgs ret handle p), src@(FunctionSource _ body)) ->
         do let types = argTypes funArgs
            initParser hdr src
            let ?returnType = ret
            ACFG types ret <$> (parseCFG handle (blocks p body))

