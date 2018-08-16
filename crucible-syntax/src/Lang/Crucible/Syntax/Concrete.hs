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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Syntax.Concrete
  ( -- * Errors
    ExprErr(..)
  , errPos
  -- * Parsing and Results
  , ACFG(..)
  , top
  , cfgs
  -- * Rules for pretty-printing language syntax
  , printExpr
  )
where

import Prelude hiding (fail)

import Data.Ratio
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

import Data.Foldable
import Data.Functor
import qualified Data.Functor.Product as Functor
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
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
import What4.Symbol
import What4.Utils.MonadST

import Lang.Crucible.Syntax.SExpr (Syntax, pattern L, pattern A, toText, PrintRules(..), PrintStyle(..), syntaxPos, withPosFrom, showAtom)
import Lang.Crucible.Syntax.Atoms hiding (atom)

import Lang.Crucible.CFG.Reg hiding (globalName)
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
  TrivialErr :: Position -> ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s
  DuplicateAtom :: Position -> AtomName -> ExprErr s
  DuplicateLabel :: Position -> LabelName -> ExprErr s
  EmptyBlock :: Position -> ExprErr s
  NotGlobal :: Position -> AST s -> ExprErr s
  InvalidRegister :: Position -> AST s -> ExprErr s
  SyntaxParseError :: SP.SyntaxError Atomic -> ExprErr s

errPos :: ExprErr s -> Position
errPos (TrivialErr p) = p
errPos (Errs e1 e2) = best (errPos e1) (errPos e2)
  where best p@(SourcePos _ _ _) _ = p
        best _ p@(SourcePos _ _ _) = p
        best p@(BinaryPos _ _) _ = p
        best _ p@(BinaryPos _ _) = p
        best p@(OtherPos _) _ = p
        best _ p@(OtherPos _) = p
        best a _b = a
errPos (DuplicateAtom p _) = p
errPos (DuplicateLabel p _) = p
errPos (EmptyBlock p) = p
errPos (InvalidRegister p _) = p
errPos (NotGlobal p _) = p
errPos (SyntaxParseError (SP.SyntaxError (Reason e _ :| _))) = syntaxPos e

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



isBaseType :: MonadSyntax Atomic m => m (Some BaseTypeRepr)
isBaseType =
  describe "base type" $
  do Some tp <- isType
     case asBaseType tp of
       NotBaseType -> empty
       AsBaseType bt -> return (Some bt)

isType :: MonadSyntax Atomic m => m (Some TypeRepr)
isType =
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
    vector = unary VectorT isType <&> \(Some t) -> Some (VectorRepr t)
    ref    = unary RefT isType <&> \(Some t) -> Some (ReferenceRepr t)
    bv :: MonadSyntax Atomic m => m  (Some TypeRepr)
    bv     = do (Some len) <- unary BitVectorT (sideCondition "natural number" someNat int)
                describe "positive number" $
                  case testLeq (knownNat :: NatRepr 1) len of
                    Nothing -> empty
                    Just LeqProof -> return $ Some $ BVRepr len

    fun :: MonadSyntax Atomic m => m (Some TypeRepr)
    fun = cons (kw FunT) (repUntilLast isType) <&> \((), (args, ret)) -> mkFunRepr args ret

    maybeT = unary MaybeT isType <&> \(Some t) -> Some (MaybeRepr t)
    var :: MonadSyntax Atomic m => m (Some TypeRepr)
    var = cons (kw VariantT) (rep isType) <&> \((), toCtx -> Some tys) -> Some (VariantRepr tys)


synth :: forall m h s . (MonadReader (SyntaxState h s) m, MonadSyntax Atomic m)
       => m (SomeExpr s)
synth =
  describe "synthesizable expression" $
    (the <|> crucibleAtom <|> unitCon <|> boolLit <|> stringLit <|> funNameLit <|>
     notExpr <|> equalp <|> lessThan <|> lessThanEq <|>
     toAny <|> fromAny <|>
     stringAppend <|> showExpr <|>
     vecRep <|> vecLen <|> vecEmptyP <|> vecGet <|> vecSet <|>
     binaryBool And_ And <|> binaryBool Or_ Or <|> binaryBool Xor_ BoolXor <|> ite <|>
     intp) <* commit

  where
    the :: m (SomeExpr s)
    the = do describe "type-annotated expression" $
               kw The `followedBy`
                 (depCons isType $
                  \(Some t) ->
                    do (e, ()) <- cons (check t) emptyList
                       return $ SomeExpr t e)

    okAtom theAtoms x =
      case Map.lookup x theAtoms of
        Nothing -> Nothing
        Just (Pair t anAtom) -> Just $ SomeExpr t (E (AtomExpr anAtom))

    crucibleAtom :: m (SomeExpr s)
    crucibleAtom =
      do theAtoms <- view stxAtoms
         sideCondition "known atom" (okAtom theAtoms) atomName

    unitCon = describe "unit constructor" (emptyList $> SomeExpr UnitRepr (E (App EmptyApp)))

    boolLit = bool <&> SomeExpr BoolRepr . E . App . BoolLit

    stringLit = string <&> SomeExpr StringRepr . E . App . TextLit

    binaryBool k f =
      do (E x, E y) <- binary k (check BoolRepr) (check BoolRepr)
         return $ SomeExpr BoolRepr $ E $ App $ f x y


    intp =
      do E e <- unary Integerp (check RealValRepr)
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
      do E e <- describe "negation expression" $ unary Not_ (check BoolRepr)
         return $ SomeExpr BoolRepr $ E $ App $ Not e

    equalp :: m (SomeExpr s)
    equalp =
      do (SomeExpr t1 (E e1), SomeExpr t2 (E e2)) <-
           describe "equality test" $
           binary Equalp synth synth
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

    lessThan :: m (SomeExpr s)
    lessThan =
      do (SomeExpr t1 (E e1), SomeExpr t2 (E e2)) <-
           binary Lt synth synth
         case testEquality t1 t2 of
           Nothing ->
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

    lessThanEq :: m (SomeExpr s)
    lessThanEq =
      do (SomeExpr t1 (E e1), SomeExpr t2 (E e2)) <-
           binary Le synth synth
         case testEquality t1 t2 of
           Nothing ->
             describe (T.concat [ "expressions with the same type, got "
                                , T.pack (show t1), " and ", T.pack (show t2)
                                ]) $
             empty
           Just Refl ->
             case t1 of
               NatRepr     -> return $ SomeExpr BoolRepr $ E $ App $ NatLe e1 e2
               IntegerRepr -> return $ SomeExpr BoolRepr $ E $ App $ IntLe e1 e2
               RealValRepr -> return $ SomeExpr BoolRepr $ E $ App $ RealLe e1 e2
               other ->
                 describe ("valid comparison type (got " <> T.pack (show other) <> ")") empty

    ite :: m (SomeExpr s)
    ite =
      do ((), (E c, (SomeExpr tTy (E t), (SomeExpr fTy (E f), ())))) <-
           cons (kw If) $
           cons (check BoolRepr) $
           cons synth $
           cons synth $
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

    toAny =
      (unary ToAny synth) <&>
        \(SomeExpr ty (E e)) -> SomeExpr AnyRepr (E (App (PackAny ty e)))
    fromAny =
      (binary FromAny isType (check AnyRepr)) <&>
        \(Some ty, E e) -> SomeExpr (MaybeRepr ty) (E (App (UnpackAny ty e)))

    stringAppend =
      do (E s1, E s2) <-
           binary StringAppend (check StringRepr) (check StringRepr)
         return $ SomeExpr StringRepr $ E $ App $ AppendString s1 s2

    vecRep =
      do (E n, SomeExpr t (E e)) <-
           binary VectorReplicate_ (check NatRepr) synth
         return $ SomeExpr (VectorRepr t) $ E $ App $ VectorReplicate t n e

    vecLen :: m (SomeExpr s)
    vecLen =
      do SomeExpr t (E e) <- unary VectorSize_ synth
         case t of
           VectorRepr _ -> return $ SomeExpr NatRepr $ E $ App $ VectorSize e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecEmptyP :: m (SomeExpr s)
    vecEmptyP =
      do SomeExpr t (E e) <- unary VectorIsEmpty_ synth
         case t of
           VectorRepr _ -> return $ SomeExpr BoolRepr $ E $ App $ VectorIsEmpty e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecGet :: m (SomeExpr s)
    vecGet =
      do (SomeExpr t (E e), E n) <-
           binary VectorGetEntry_ synth (check NatRepr)
         case t of
           VectorRepr elemT -> return $ SomeExpr elemT $ E $ App $ VectorGetEntry elemT e n
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    someVec :: SomeExpr t -> Maybe (SomeVectorExpr t)
    someVec (SomeExpr (VectorRepr t) e) = Just (SomeVectorExpr t e)
    someVec _ = Nothing

    synthVec = sideCondition "expression with vector type" someVec synth

    vecSet :: m (SomeExpr s)
    vecSet =
      do kw VectorSetEntry_ `followedBy`
           (depCons synthVec $
            \(SomeVectorExpr t (E vec)) ->
              do (E n, (E elt, ())) <- cons (check NatRepr) $
                                       cons (check t) $
                                       emptyList
                 return $ SomeExpr (VectorRepr t) $ E $ App $ VectorSetEntry t vec n elt)


    showExpr :: m (SomeExpr s)
    showExpr =
      do SomeExpr t1 (E e) <- unary Show synth
         case asBaseType t1 of
           NotBaseType -> describe ("base type, but got " <> T.pack (show t1)) empty
           AsBaseType bt ->
             return $ SomeExpr StringRepr $ E $ App $ ShowValue bt e

check :: forall m t h s . (MonadReader (SyntaxState h s) m, MonadSyntax Atomic m)
       => TypeRepr t -> m (E s t)
check t =
  describe ("inhabitant of " <> T.pack (show t)) $
    (literal <|> unpack <|> just <|> nothing <|> fromJust_ <|> injection <|>
     addition <|> subtraction <|> multiplication <|> division <|> modulus <|>
     negation <|> absoluteValue <|>
     vecLit <|> vecCons <|> modeSwitch) <* commit
  where
    typed :: TypeRepr t' ->  m (E s t')
          -> m (E s t)
    typed t' p =
      case testEquality t' t of
        Just Refl -> p
        Nothing -> empty

    literal = natLiteral <|> intLiteral <|> rationalLiteral

    natLiteral =
      typed NatRepr $
        sideCondition "nat literal" isNat int
      where isNat i | i >= 0 = Just (E (App (NatLit (fromInteger i))))
            isNat _ = Nothing

    intLiteral =
      typed IntegerRepr (int <&> E . App . IntLit . fromInteger)

    rationalLiteral =
      typed RealValRepr $
        (rational <&> E . App . RationalLit) <|>
        (int <&> \i -> E $ App $ RationalLit (i % 1))

    unpack =
      do package <- unary Unpack anything
         describe "context expecting Maybe" $
           case t of
             MaybeRepr expected ->
               do E e <- withProgressStep Rest $ withProgressStep SP.First $
                         parse package $ check AnyRepr
                  return $ E $ App (UnpackAny expected e)
             _ -> empty

    just =
      do inj <- unary Just_ anything
         describe "context expecting Maybe" $
           case t of
             MaybeRepr expected ->
               do E e <- withProgressStep Rest $ withProgressStep SP.First $
                         parse inj $ check expected
                  return $ E $ App (JustValue expected e)
             _ -> empty

    nothing =
      describe "context expecting Maybe" $
        case t of
          MaybeRepr expected ->
            do kw Nothing_
               return $ E $ App (NothingValue expected)
          _ -> empty

    fromJust_ =
      do describe "coercion from Maybe (fromJust-expression)" $
           followedBy (kw FromJust) $
           depCons (check (MaybeRepr t)) $
             \ (E e) ->
               depCons (check StringRepr) $
                 \ (E str) ->
                   do emptyList
                      return $ E $ App $ FromJustValue t e str
    injection =
      do ((), (n, (e, ()))) <- describe "injection into variant type" $
                               cons (kw Inj) $ cons int $ cons anything $ emptyList
         case t of
           VariantRepr ts ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = view (ixF' idx) ts
                    E out <- withProgressStep Rest $ withProgressStep Rest $ withProgressStep SP.First $
                             parse e (check ty)
                    return $ E $ App $ InjectVariant ts idx out
           _ -> describe ("context expecting variant type (got " <> T.pack (show t) <> ")") empty

    negation =
      arith1 t IntegerRepr Negate IntNeg <|>
      arith1 t RealValRepr Negate RealNeg

    absoluteValue =
      arith1 t IntegerRepr Abs IntAbs

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
      arith t NatRepr Div NatDiv <|>
      arith t IntegerRepr Div IntDiv <|>
      arith t RealValRepr Div RealDiv

    modulus =
      arith t NatRepr Mod NatMod <|>
      arith t IntegerRepr Mod IntMod <|>
      arith t RealValRepr Mod RealMod

    arith1 :: TypeRepr t1 -> TypeRepr t2
          -> Keyword
          -> (Expr () s t2 -> App () (Expr () s) t2)
          -> m (E s t1)
    arith1 t1 t2 k f =
      case testEquality t1 t2 of
        Nothing ->
          describe ("unary arithmetic expression beginning with " <> T.pack (show k) <> " type " <>  (T.pack (show t2)))
            empty
        Just Refl ->
          followedBy (kw k) $
          depCons (check t1) $
            \ (E e) ->
                do emptyList
                   return $ E $ App $ f e



    arith :: TypeRepr t1 -> TypeRepr t2
          -> Keyword
          -> (Expr () s t2 -> Expr () s t2 -> App () (Expr () s) t2)
          -> m (E s t1)
    arith t1 t2 k f =
      case testEquality t1 t2 of
        Nothing ->
          describe ("arithmetic expression beginning with " <> T.pack (show k) <> " type " <>  (T.pack (show t2)))
            empty
        Just Refl ->
          -- describe ("arithmetic expression of type " <> T.pack (show t2)) $
          followedBy (kw k) $
          depCons (check t1) $
            \ (E e1) ->
              depCons (check t1) $
                \ (E e2) ->
                  do emptyList
                     return $ E $ App $ f e1 e2

    vecLit =
      describe "vector literal" $
      followedBy (kw VectorLit_) $
      (pure () <|> cut) *>
      case t of
        VectorRepr elemTy ->
          do es <- rep $ check elemTy
             return $ E $ App $ VectorLit elemTy (V.fromList (map unE es))
        _ -> describe ("context expecting a vector") $ empty

    vecCons =
      case t of
        VectorRepr elemTy ->
          do (E a, E d) <- binary VectorCons_
                             (check elemTy)
                             (check (VectorRepr elemTy))
             return $ E $ App $ VectorCons elemTy a d
        _ -> empty


    modeSwitch :: m (E s t)
    modeSwitch =
      do SomeExpr t' e <- synth
         later $ describe ("a " <> T.pack (show t) <> " rather than a " <> T.pack (show t')) $
           case testEquality t t' of
             Nothing -> later empty
             Just Refl -> return e


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

freshAtom :: (MonadWriter [Posd (Stmt () s)] m, MonadState (SyntaxState h s) m)
          => Position -> AtomValue () s t -> m (Atom s t)
freshAtom loc v =
  do i <- freshAtomIndex
     let theAtom = Atom { atomPosition = OtherPos "Parser internals"
                        , atomId = i
                        , atomSource = Assigned
                        , typeOfAtom = typeOfAtomValue v
                        }
         stmt = DefineAtom theAtom v
     tell [Posd loc stmt]
     pure theAtom



newLabel :: MonadState (SyntaxState h s) m => LabelName -> m (Label s)
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


lambdaLabelBinding :: (MonadSyntax Atomic m, MonadState (SyntaxState h s) m)
                   => m (LabelName, (Pair TypeRepr (LambdaLabel s)))
lambdaLabelBinding =
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
        uniqueAtom =
          do atoms <- use stxAtoms
             sideCondition "unique Crucible atom"
               (\x -> case Map.lookup x atoms of
                        Nothing -> Just x
                        Just _ -> Nothing)
               atomName

newUnassignedReg :: MonadState (SyntaxState h s) m => TypeRepr t -> m (Reg s t)
newUnassignedReg t =
  do i <- freshAtomIndex
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

globRef' :: (MonadSyntax Atomic m, MonadState (SyntaxState h s) m) => m (Pair TypeRepr GlobalVar)
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

atomSetter :: (MonadSyntax Atomic m, MonadWriter [Posd (Stmt () s)] m, MonadState (SyntaxState h s) m)
           => AtomName -- ^ The name of the atom being set, used for fresh name internals
           -> m (Pair TypeRepr (Atom s))
atomSetter (AtomName anText) =
  fromReg <|> fromGlobal <|> deref <|> newref <|> emptyref <|> fresh <|> funcall <|> evaluated
  where
    fromReg, fresh, fromGlobal, newref, deref, funcall
      :: ( MonadSyntax Atomic m
         , MonadWriter [Posd (Stmt () s)] m
         , MonadState (SyntaxState h s) m
         )
      => m (Pair TypeRepr (Atom s))
    fromReg =
      do Pair t r <- regRef'
         loc <- SP.position
         resAtom <- freshAtom loc (ReadReg r)
         return $ Pair t resAtom
    fromGlobal =
      do Pair t g <- globRef'
         loc <- SP.position
         resAtom <- freshAtom loc (ReadGlobal g)
         return $ Pair t resAtom
    deref =
      do SomeExpr t (E e) <- reading (unary Deref synth)
         case t of
           ReferenceRepr t' ->
             do loc <- position
                anAtom <- eval loc e
                anotherAtom <- freshAtom loc (ReadRef anAtom)
                return $ Pair t' anotherAtom
           notRef -> later $ describe ("reference type (provided a "<> T.pack (show notRef) <>")") empty
    newref =
      do SomeExpr t (E e) <- reading (unary Ref synth)
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

    funcall =
      followedBy (kw Funcall) $
      depConsCond (reading synth) $
        \x ->
          case x of
            (SomeExpr (FunctionHandleRepr funArgs ret) (E fun)) ->
              do loc <- position
                 funAtom <- eval loc fun
                 operandExprs <- backwards $ go $ Ctx.viewAssign funArgs
                 operandAtoms <- traverseFC (\(Rand a (E ex)) -> eval (syntaxPos a) ex) operandExprs
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
    evaluated =
       do SomeExpr tp (E e') <- reading synth
          loc <- position
          anAtom <- eval loc e'
          return $ Pair tp anAtom


located :: MonadSyntax atom m => m a -> m (Posd a)
located p = Posd <$> position <*> p

normStmt' :: forall h s m
           . (MonadWriter [Posd (Stmt () s)] m, MonadSyntax Atomic m, MonadState (SyntaxState h s) m) =>
             m ()
normStmt' =
  call $
  printStmt <|> letStmt <|> setGlobal <|> setReg <|> setRef <|> dropRef <|> assertion


  where
    printStmt, letStmt, setGlobal, setReg, setRef, dropRef, assertion :: m ()
    printStmt =
      do Posd loc (E e) <- unary Print_ (located $ reading $ check StringRepr)
         strAtom <- eval loc e
         tell [Posd loc (Print strAtom)]

    letStmt =
      followedBy (kw Let) $
      depCons atomName $
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
              Just (Pair t var) ->
                do (Posd loc (E e)) <- fst <$> cons (located $ reading $ check t) emptyList
                   a <- eval loc e
                   tell [Posd loc $ WriteGlobal var a]
                   return (Right ())
    setReg =
      followedBy (kw SetRegister) $
      depCons regRef' $
      \(Pair ty r) ->
        depCons (reading $ located $ check ty) $
        \(Posd loc (E e)) ->
          do emptyList
             v <- eval loc e
             tell [Posd loc $ SetReg r v]

    setRef =
      do stmtLoc <- position
         followedBy (kw SetRef) $
           depConsCond (located $ reading $ synth) $
           \case
             (Posd refLoc (SomeExpr (ReferenceRepr t') (E refE))) ->
               depCons (located $ reading $ check t') $
               \(Posd valLoc (E valE)) ->
                 do emptyList
                    refAtom <- eval refLoc refE
                    valAtom <- eval valLoc valE
                    tell [Posd stmtLoc $ WriteRef refAtom valAtom]
                    return (Right ())
             (Posd _ (SomeExpr _ _)) ->
               return $ Left "expression with reference type"
    dropRef =
      do loc <- position
         followedBy (kw DropRef_) $
           depConsCond (located $ reading synth) $
            \(Posd eLoc (SomeExpr t (E refE))) ->
               emptyList *>
               case t of
                 ReferenceRepr _ ->
                   do refAtom <- eval eLoc refE
                      tell [Posd loc $ DropRef refAtom]
                      return $ Right ()
                 _ -> return $ Left "expression with reference type"
    assertion =
      do (Posd loc (Posd cLoc (E cond), Posd mLoc (E msg))) <-
           located $
           binary Assert_
             (located $ reading $ check BoolRepr)
             (located $ reading $ check StringRepr)
         cond' <- eval cLoc cond
         msg' <- eval mLoc msg
         tell [Posd loc $ Assert cond' msg']


blockBody' :: forall s h ret m
            . (MonadSyntax Atomic m, MonadState (SyntaxState h s) m)
           => TypeRepr ret
           -> m (Posd (TermStmt s ret), [Posd (Stmt () s)])
blockBody' ret = runWriterT go
 where
 go :: WriterT [Posd (Stmt () s)] m (Posd (TermStmt s ret))
 go = (fst <$> (cons (termStmt' ret) emptyList)) <|>
      (snd <$> (cons (later normStmt') go))


termStmt' :: forall m h s ret.
   (MonadWriter [Posd (Stmt () s)] m, MonadSyntax Atomic m, MonadState (SyntaxState h s) m) =>
   TypeRepr ret -> m (Posd (TermStmt s ret))
termStmt' retTy =
  do stx <- anything
     withPosFrom stx <$>
       (jump <|> branch <|> maybeBranch <|> cases <|> ret <|> err <|> tailCall <|> out)

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
                \ (Posd eloc (E cond)) ->
                  cons normalLabel (cons normalLabel emptyList) >>=
                  \(l1, (l2, ())) -> do
                    c <- eval eloc cond
                    return (Br c l1 l2))

    maybeBranch :: m (TermStmt s ret)
    maybeBranch =
      followedBy (kw MaybeBranch_) $
      describe "valid arguments to maybe-branch" $
      depCons (located (reading synth)) $
        \(Posd sloc (SomeExpr ty (E scrut))) ->
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
        \(Posd tgtloc (SomeExpr ty (E tgt))) ->
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
        do Posd loc (E e) <- unary Return_ (located (reading (check retTy)))
           Return <$> eval loc e

    tailCall :: m (TermStmt s ret)
    tailCall =
      followedBy (kw TailCall_) $
        describe "function atom and arguments" $
          do -- commit
             depCons (located (reading synth)) $
               \case
                 Posd loc (SomeExpr (FunctionHandleRepr argumentTypes retTy') (E funExpr)) ->
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
            \(Posd loc (E arg)) ->
               Ctx.extend <$> go (Ctx.viewAssign tys) <*> eval loc arg

    err :: m (TermStmt s ret)
    err =
      do Posd loc (E e) <- unary Error_ (located (reading (check StringRepr)))
         ErrorStmt <$> eval loc e

    out :: m (TermStmt s ret)
    out = followedBy (kw Output_) $
          do -- commit
             depCons lambdaLabel $
               \(Pair argTy lbl) ->
                 depCons (located (reading (check argTy))) $
                   \(Posd loc (E arg)) ->
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



arguments' :: forall m . MonadSyntax Atomic m => m (Some (Ctx.Assignment Arg))
arguments' = go (Some Ctx.empty)
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
  FunctionHeader { _headerName :: FunctionName
                 , _headerArgs :: Ctx.Assignment Arg args
                 , _headerReturnType :: TypeRepr ret
                 , _headerHandle :: FnHandle args ret
                 , _headerLoc :: Position
                 }

data FunctionSource s =
  FunctionSource { _functionRegisters :: [AST s]
                 , _functionBody :: AST s
                 }

functionHeader' :: MonadSyntax Atomic m
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
    registers = kw Registers `followedBy` anyList

functionHeader :: AST s -> TopParser h s (FunctionHeader, FunctionSource s)
functionHeader defun =
  do ((fnName, Some theArgs, Some ret, loc), src) <- liftSyntaxParse functionHeader' defun
     ha <- use $ stxProgState  . progHandleAlloc
     handle <- liftST $ mkHandle' ha fnName (argTypes theArgs) ret
     let header = FunctionHeader fnName theArgs ret handle loc

     saveHeader fnName header
     return $ (header, src)
  where
    saveHeader n h =
      stxFunctions %= Map.insert n h




global :: AST s -> TopParser h s (Pair TypeRepr GlobalVar)
global stx =
  do (var@(GlobalName varName), Some t) <- liftSyntaxParse (binary DefGlobal globalName isType) stx
     ha <- use $ stxProgState  . progHandleAlloc
     v <- liftST $ freshGlobalVar ha varName t
     stxGlobals %= Map.insert var (Pair t v)
     return $ Pair t v

topLevel :: AST s -> TopParser h s (Maybe (FunctionHeader, FunctionSource s))
topLevel ast =
  catchError (Just <$> functionHeader ast) $
    \e ->
      catchError (global ast $> Nothing) $
        \_ -> throwError e

argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ _ t) -> t)


type BlockTodo h s ret =
  (LabelName, BlockID s, Progress, AST s)

blocks :: forall h s ret m . (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) => TypeRepr ret -> m [Block () s ret]
blocks ret =
      depCons startBlock' $
      \ startContents ->
        do todo <- rep blockLabel'
           forM (startContents : todo) $ \(_, bid, pr, stmts) ->
             do (term, stmts') <- withProgress (const pr) $ parse stmts (blockBody' ret)
                pure $ mkBlock bid mempty (Seq.fromList stmts') term


  where

    startBlock' :: (MonadState (SyntaxState h s) m, MonadSyntax Atomic m) => m (BlockTodo h s ret)
    startBlock' =
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
          depConsCond (lambdaLabelBinding) $
          \ (l, (Pair _ lbl)) ->
            do pr <- progress
               body <- anything
               return $ Right (l, LambdaID lbl, pr, body)

eval :: (MonadWriter [Posd (Stmt () s)] m, MonadState (SyntaxState h s) m)
     => Position -> Expr () s t -> m (Atom s t)
eval loc (App e)            = freshAtom loc . EvalApp =<< traverseFC (eval loc) e
eval _   (AtomExpr theAtom) = pure theAtom -- The expression is already evaluated


newtype TopParser h s a =
  TopParser { runTopParser :: ExceptT (ExprErr s)
                                (StateT (SyntaxState h s) (ST h))
                                a
            }
  deriving (Functor)

top :: HandleAllocator h -> TopParser h s a -> ST h (Either (ExprErr s) a)
top ha (TopParser (ExceptT (StateT act))) =
  fst <$> act (initSyntaxState (initProgState ha))

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
      do Some ty <- liftSyntaxParse isType t
         r <- newUnassignedReg ty
         stxRegisters %= Map.insert x (Pair ty r)
    saveRegister other = throwError $ InvalidRegister (syntaxPos other) other


cfgs :: [AST s] -> TopParser h s [ACFG]
cfgs defuns =
  do headers <- catMaybes <$> traverse topLevel defuns
     forM headers $
       \(hdr@(FunctionHeader _ funArgs ret handle _), src@(FunctionSource _ body)) ->
         do let types = argTypes funArgs
            initParser hdr src
            let ?returnType = ret
            st <- get
            (theBlocks, st') <- liftSyntaxParse (runStateT (blocks ret) st) body
            put st'
            i <- freshAtomIndex
            j <- freshLabelIndex
            return $ ACFG types ret $ CFG handle theBlocks i j
