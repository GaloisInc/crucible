{-# LANGUAGE DeriveFunctor, GADTs, OverloadedStrings, RankNTypes, LiberalTypeSynonyms, KindSignatures, DataKinds, StandaloneDeriving, FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies, PatternGuards, PolyKinds, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances, PartialTypeSignatures, FlexibleContexts, ImplicitParams, LambdaCase, ViewPatterns #-}
-- {-# OPTIONS_GHC -fprint-explicit-kinds -fprint-explicit-foralls #-}
module Lang.Crucible.Syntax.Concrete where

import Prelude hiding (fail)

import Data.Monoid

import Control.Lens
import Control.Applicative
import Control.Monad.Identity hiding (fail)
import Control.Monad.Trans.Except
import Control.Monad.State.Class
import Control.Monad.State.Strict
import Control.Monad.Except hiding (fail)
import Control.Monad.Error.Class ()
import Control.Monad.Writer.Strict
import Control.Monad.Writer.Class ()

import Lang.Crucible.Types

--import Data.Functor
import qualified Data.Functor.Product as Functor
--import Data.Ratio
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.Map (MapF)
import Data.Parameterized.TraversableFC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx
import Data.Map (Map)
import qualified Data.Map as Map
--import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V

import What4.ProgramLoc
import What4.FunctionName
import What4.Utils.MonadST

import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.Atoms

import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.Expr
--import Lang.Crucible.CFG.Generator (Generator)
--import qualified Lang.Crucible.CFG.Generator as Gen

import Lang.Crucible.FunctionHandle

import Numeric.Natural ()



type AST s = Syntax Atomic




printExpr :: AST s -> Text
printExpr = toText (PrintRules rules) printAtom
  where printAtom (Kw s) = T.pack (show s)
        printAtom (Lbl (LabelName l)) = l <> ":"
        printAtom (Rg (RegName r)) = "$" <> r
        printAtom (At (AtomName a)) = a
        printAtom (Fn (FunName a)) = "@" <> a
        printAtom (Int i) = T.pack (show i)
        printAtom (Rat r) = T.pack (show r)
        printAtom (Bool b) = if b then "#t" else "#f"
        rules (Kw Defun) = Just (Special 3)
        rules (Kw DefBlock) = Just (Special 1)
        rules (Kw Start) = Just (Special 1)
        rules (Kw Registers) = Just (Special 0)
        rules _ = Nothing


newtype E s t = E { unE :: Expr () s t }
  deriving Show


data SomeExpr :: * -> * where
  SomeExpr :: TypeRepr t -> E s t -> SomeExpr s

deriving instance (Show (SomeExpr a))

data ExprErr s where
  TypeError :: Position -> AST s -> TypeRepr expected -> TypeRepr found -> ExprErr s
  AnonTypeError :: Position -> TypeRepr expected -> TypeRepr found -> ExprErr s
  TypeMismatch :: Position -> AST s -> TypeRepr left -> AST s -> TypeRepr right -> ExprErr s
  NotVector :: Position -> AST s -> TypeRepr tp -> ExprErr s
  BadSyntax :: Position -> AST s -> ExprErr s
  CantSynth :: Position -> AST s -> ExprErr s
  NotAType :: Position -> AST s -> ExprErr s
  NotANat :: Position -> Integer -> ExprErr s
  NotNumeric :: Position -> AST s -> TypeRepr t -> ExprErr s
  NotRef :: AST s -> TypeRepr t -> ExprErr s
  NotComparison :: Position -> AST s -> TypeRepr t -> ExprErr s
  NotABaseType :: Position -> TypeRepr t -> ExprErr s
  TrivialErr :: Position -> ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s
  TooSmall :: Position -> NatRepr n -> ExprErr s
  UnknownAtom :: Position -> AtomName -> ExprErr s
  UnknownBlockLabel :: Position -> AST s -> ExprErr s
  UnknownFunction :: Position -> FunName -> ExprErr s
  DuplicateAtom :: Position -> AtomName -> ExprErr s
  DuplicateLabel :: Position -> LabelName -> ExprErr s
  NotArgumentSpec :: Position -> AST s -> ExprErr s
  NotFunctionName :: Position -> AST s -> ExprErr s
  NotFunDef :: Position -> AST s -> ExprErr s
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

errPos :: ExprErr s -> Position
errPos (TypeError p _ _ _) = p
errPos (AnonTypeError p _ _) = p
errPos (TypeMismatch p _ _ _ _) = p
errPos (BadSyntax p _) = p
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

deriving instance Show (ExprErr s)
instance Monoid (ExprErr s) where
  mempty = TrivialErr (OtherPos "mempty")
  mappend = Errs

printExprErr :: ExprErr s -> String
printExprErr = show

data ComparisonCtor s t = ComparisonCtor (Expr () s t -> Expr () s t -> App () (Expr () s) BoolType)

synthComparison :: (Alternative m, MonadError (ExprErr s) m, MonadState (SyntaxState h s) m)
                => MapF TypeRepr (ComparisonCtor s)
                -> AST s -> AST s -> AST s
                -> m (E s BoolType)
synthComparison ts e a b =
  do SomeExpr t1 (E a') <- synthExpr a
     SomeExpr t2 (E b') <- synthExpr b
     case testEquality t1 t2 of
       Nothing -> throwError$ TypeMismatch (syntaxPos e) a t1 b t2
       Just Refl ->
         case MapF.lookup t1 ts of
           Nothing -> throwError$ NotComparison (syntaxPos e) e t1
           Just (ComparisonCtor f) -> return $ E (App (f a' b'))

checkNumeric :: (Alternative m, MonadError (ExprErr s) m, MonadState (SyntaxState h s) m)
             => TypeRepr t1 -> TypeRepr t2
             -> AST s -> AST s -> AST s
             -> (Expr () s t2 -> Expr () s t2 -> App () (Expr () s) t2)
             -> m (E s t1)
checkNumeric t1 t2 e a b f =
  case testEquality t1 t2 of
    Just Refl ->
      do E a' <- checkExpr t2 a
         E b' <- checkExpr t2 b
         return (E (App (f a' b')))
    Nothing -> throwError$ NotNumeric (syntaxPos e) e t2

checkExpr :: (Alternative m, MonadError (ExprErr s) m, MonadState (SyntaxState h s) m)
          => TypeRepr t -> AST s -> m (E s t)
checkExpr (MaybeRepr expectedT) (L [A (Kw Unpack), package]) =
  do E e <- checkExpr AnyRepr package
     return $ E (App (UnpackAny expectedT e))
checkExpr NatRepr e@(A (Int i)) =
  if i < 0
    then throwError $ NotANat (syntaxPos e) i
    else return (E (App (NatLit (fromInteger i))))
checkExpr IntegerRepr (A (Int i)) =
  return (E (App (IntLit (fromInteger i))))
checkExpr expectedT e@(L [A (Kw Plus), a, b]) =
      checkNumeric expectedT NatRepr e a b NatAdd
  <|> checkNumeric expectedT IntegerRepr e a b IntAdd
  <|> checkNumeric expectedT RealValRepr e a b RealAdd
checkExpr expectedT e@(L [A (Kw Minus), a, b]) =
      checkNumeric expectedT NatRepr e a b NatSub
  <|> checkNumeric expectedT IntegerRepr e a b IntSub
  <|> checkNumeric expectedT RealValRepr e a b RealSub
checkExpr expectedT e@(L [A (Kw Times), a, b]) =
      checkNumeric expectedT NatRepr e a b NatMul
  <|> checkNumeric expectedT IntegerRepr e a b IntMul
  <|> checkNumeric expectedT RealValRepr e a b RealMul
checkExpr (MaybeRepr t) (L [A (Kw Just_), a]) =
  do E a' <- checkExpr t a
     return (E (App (JustValue t a')))
checkExpr (MaybeRepr t) (A (Kw Nothing_)) =
  return (E (App (NothingValue t)))
checkExpr t (L [A (Kw FromJust), a, str]) =
  do E a' <- checkExpr (MaybeRepr t) a
     E str' <- checkExpr StringRepr str
     return (E (App (FromJustValue t a' str')))
checkExpr expectedT ast =
  do SomeExpr foundT e <- synthExpr ast
     case testEquality expectedT foundT of
       Just Refl -> return $ e
       Nothing -> throwError $ TypeError (syntaxPos ast) ast expectedT foundT


isType :: MonadError (ExprErr s) m => AST s -> m (Some TypeRepr)
isType t@(A (Kw x)) =
  case x of
    AnyT -> return $ Some AnyRepr
    UnitT -> return $ Some UnitRepr
    BoolT -> return $ Some BoolRepr
    NatT -> return $ Some NatRepr
    IntegerT -> return $ Some IntegerRepr
    RealT -> return $ Some RealValRepr
    ComplexRealT -> return $ Some ComplexRealRepr
    CharT -> return $ Some CharRepr
    StringT -> return $ Some StringRepr
    _ -> throwError $ NotAType (syntaxPos t) t

isType (L [A (Kw VectorT), a]) =
  do Some t <- isType a
     return $ Some (VectorRepr t)

isType (L [A (Kw BitVectorT), n]) =
  case n of
    A (Int i) ->
      case someNat i of
        Nothing -> throwError $ NotANat (syntaxPos n) i
        Just (Some len) ->
          case testLeq (knownNat :: NatRepr 1) len of
            Nothing -> throwError $ TooSmall (syntaxPos n) len
            Just LeqProof -> return $ Some $ BVRepr len
    other -> throwError $ NotNumeric (syntaxPos other) other NatRepr

isType (L (A (Kw FunT) : domAndRan)) | Just (doms, ran) <- withLast domAndRan =
  do doms' <- mapM isType doms
     Some argTypes <- return $ toCtx (reverse doms')
     Some ran' <- isType ran
     return $ Some $ FunctionHandleRepr argTypes ran'
  where withLast [] = Nothing
        withLast [x] = Just ([], x)
        withLast (x : xs) = fmap (\(most, last) -> (x : most, last)) (withLast xs)
        toCtx [] = Some Ctx.empty
        toCtx (Some t : ts) | Some ts' <- toCtx ts = Some $ Ctx.extend ts' t

-- TODO more types
isType e = throwError $ NotAType (syntaxPos e) e



synthExpr :: (Alternative m, MonadError (ExprErr s) m, MonadState (SyntaxState h s) m) => AST s -> m (SomeExpr s)
synthExpr (L [A (Kw The), t, e]) =
  do Some ty <- isType t
     e' <- checkExpr ty e
     return $ SomeExpr ty e'
synthExpr e@(L [A (Kw Equalp), a, b]) =
  do SomeExpr t1 (E a') <- synthExpr a
     SomeExpr t2 (E b') <- synthExpr b
     case testEquality t1 t2 of
       Just Refl ->
         case asBaseType t1 of
           NotBaseType -> throwError $ NotABaseType (syntaxPos e) t1
           AsBaseType bt ->
             return $ SomeExpr BoolRepr (E (App (BaseIsEq bt a' b')))
       Nothing -> throwError $ TypeMismatch (syntaxPos e) a t1 b t2
synthExpr e@(L [A (Kw If), c, t, f]) =
  do E c' <- checkExpr BoolRepr c
     SomeExpr ty1 (E t') <- synthExpr t
     SomeExpr ty2 (E f') <- synthExpr f
     case testEquality ty1 ty2 of
       Just Refl ->
         case asBaseType ty1 of
           NotBaseType -> throwError $ NotABaseType (syntaxPos e) ty1
           AsBaseType bt ->
             return $ SomeExpr ty1 (E (App (BaseIte bt c' t' f')))
       Nothing -> throwError $ TypeMismatch (syntaxPos e) t ty1 f ty2
synthExpr x@(A (Fn n)) =
  do fn <- funName x
     fh <- use $ stxFunctions . at fn
     case fh of
       Nothing -> throwError $ UnknownFunction (syntaxPos x) n
       Just (FunctionHeader name args ret handle _) ->
         return $ SomeExpr (FunctionHandleRepr (argTypes args) ret) (E (App $ HandleLit handle))
synthExpr (L []) =
  return $ SomeExpr UnitRepr (E (App EmptyApp))
synthExpr (L [A (Kw Pack), arg]) =
  do SomeExpr ty (E e) <- synthExpr arg
     return $ SomeExpr AnyRepr (E (App (PackAny ty e)))
synthExpr (A (Bool b)) =
  return $ SomeExpr BoolRepr (E (App (BoolLit b)))
synthExpr (L [A (Kw Not_), arg]) =
  do E bE <- checkExpr BoolRepr arg
     return $ SomeExpr BoolRepr (E (App (Not bE)))
synthExpr (L [A (Kw And_), e1, e2]) =
  do E bE1 <- checkExpr BoolRepr e1
     E bE2 <- checkExpr BoolRepr e2
     return $ SomeExpr BoolRepr (E (App (And bE1 bE2)))
synthExpr (L [A (Kw Or_), e1, e2]) =
  do E bE1 <- checkExpr BoolRepr e1
     E bE2 <- checkExpr BoolRepr e2
     return $ SomeExpr BoolRepr (E (App (Or bE1 bE2)))
synthExpr (L [A (Kw Xor_), e1, e2]) =
  do E bE1 <- checkExpr BoolRepr e1
     E bE2 <- checkExpr BoolRepr e2
     return $ SomeExpr BoolRepr (E (App (BoolXor bE1 bE2)))
synthExpr (A (Rat r)) =
  return $ SomeExpr RealValRepr (E (App (RationalLit r)))
synthExpr (L [A (Kw Div), e1, e2]) =
  do E rE1 <- checkExpr RealValRepr e1
     E rE2 <- checkExpr RealValRepr e2
     return $ SomeExpr RealValRepr (E (App (RealDiv rE1 rE2)))
synthExpr (L [A (Kw Mod), e1, e2]) =
  do E rE1 <- checkExpr RealValRepr e1
     E rE2 <- checkExpr RealValRepr e2
     return $ SomeExpr RealValRepr (E (App (RealMod rE1 rE2)))
synthExpr (L [A (Kw Integerp), e]) =
  do E e' <- checkExpr RealValRepr e
     return $ SomeExpr BoolRepr (E (App (RealIsInteger e')))
synthExpr e@(L [A (Kw Lt), a, b]) =
  SomeExpr BoolRepr <$>
  synthComparison
    (MapF.fromList [ Pair NatRepr (ComparisonCtor NatLt)
                   , Pair IntegerRepr (ComparisonCtor IntLt)
                   , Pair RealValRepr (ComparisonCtor RealLt)
                   ])
    e a b
synthExpr e@(A (At x)) =
  do ats <- use (stxAtoms . at x)
     case ats of
       Nothing -> throwError $ UnknownAtom (syntaxPos e) x
       Just (Pair t at) -> return $ SomeExpr t (E (AtomExpr at))

synthExpr e@(L [A (Kw VectorLit_), tpe, L vs]) =
  do Some tp <- isType tpe
     vs' <- (V.fromList . map unE) <$> mapM (checkExpr tp) vs
     return (SomeExpr (VectorRepr tp) (E (App (VectorLit tp vs'))))

synthExpr e@(L [A (Kw VectorReplicate_), n, x]) =
  do E n' <- checkExpr NatRepr n
     SomeExpr tp (E x') <- synthExpr x
     return (SomeExpr (VectorRepr tp) (E (App (VectorReplicate tp n' x'))))

synthExpr e@(L [A (Kw VectorIsEmpty_), v]) =
  do SomeExpr tp (E v') <- synthExpr v
     case tp of
       VectorRepr eltp ->
         return (SomeExpr BoolRepr (E (App (VectorIsEmpty v'))))
       _ -> throwError $ NotVector (syntaxPos v) v tp

synthExpr e@(L [A (Kw VectorSize_), v]) =
  do SomeExpr tp (E v') <- synthExpr v
     case tp of
       VectorRepr eltp ->
         return (SomeExpr NatRepr (E (App (VectorSize v'))))
       _ -> throwError $ NotVector (syntaxPos v) v tp

synthExpr e@(L [A (Kw VectorGetEntry_), v, n]) =
  do SomeExpr tp (E v') <- synthExpr v
     E n' <- checkExpr NatRepr n
     case tp of
       VectorRepr eltp ->
         return (SomeExpr eltp (E (App (VectorGetEntry eltp v' n'))))
       _ -> throwError $ NotVector (syntaxPos v) v tp

synthExpr e@(L [A (Kw VectorSetEntry_), v, n, x]) =
 (do SomeExpr eltp (E x') <- synthExpr x
     E v' <- checkExpr (VectorRepr eltp) v
     E n' <- checkExpr NatRepr n
     return (SomeExpr (VectorRepr eltp) (E (App (VectorSetEntry eltp v' n' x')))))
 <|>
 (do SomeExpr tp (E v') <- synthExpr v
     E n' <- checkExpr NatRepr n
     case tp of
       VectorRepr eltp ->
         do E x' <- checkExpr eltp x
            return (SomeExpr (VectorRepr eltp) (E (App (VectorSetEntry eltp v' n' x'))))
       _ -> throwError $ NotVector (syntaxPos v) v tp)

synthExpr e@(L [A (Kw VectorCons_), h, v]) =
  (do SomeExpr eltp (E h') <- synthExpr h
      E v' <- checkExpr (VectorRepr eltp) v
      return (SomeExpr (VectorRepr eltp) (E (App (VectorCons eltp h' v')))))
  <|>
  (do SomeExpr tp (E v') <- synthExpr v
      case tp of
        VectorRepr eltp ->
          do E h' <- checkExpr eltp h
             return (SomeExpr (VectorRepr eltp) (E (App (VectorCons eltp h' v'))))
        _ -> throwError $ NotVector (syntaxPos v) v tp)

synthExpr e@(L [A (Kw StringAppend), e1, e2]) =
  do E e1' <- checkExpr StringRepr e1
     E e2' <- checkExpr StringRepr e2
     return $ SomeExpr StringRepr (E (App (AppendString e1' e2')))

synthExpr ast = throwError $ CantSynth (syntaxPos ast) ast


-------------------------------------------------------------------------

data LabelInfo :: * -> * where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . TypeRepr ty -> LambdaLabel s ty -> LabelInfo s

data ProgramState h s =
  ProgramState { _progFunctions :: Map FunctionName FunctionHeader
               , _progHandleAlloc :: HandleAllocator h
               }

progFunctions :: Simple Lens (ProgramState h s) (Map FunctionName FunctionHeader)
progFunctions = lens _progFunctions (\s v -> s { _progFunctions = v })

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
initProgState = ProgramState Map.empty

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
     let atom = Atom { atomPosition = OtherPos "Parser internals"
                     , atomId = i
                     , atomSource = Assigned
                     , typeOfAtom = typeOfAtomValue v
                     }
         stmt = DefineAtom atom v
     tell [withPosFrom e stmt]
     pure atom

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
     (lbl, at) <- freshLambdaLabel t
     stxLabels %= Map.insert l (ArgLbl t lbl)
     stxAtoms %= Map.insert x (Pair t at) -- TODO check for duplicate atoms here
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
     at <- eval e e'
     tell [withPosFrom stmt $ Print at]
normStmt stmt@(L [A (Kw Let), A (At an), e]) =
  do Pair tp atom <- atomValue e
     stxAtoms %= Map.insert an (Pair tp atom)
  where
    atomValue stx@(A (Rg _)) =
      do Pair t r <- regRef stx
         atom <- freshAtom stmt (ReadReg r)
         return $ Pair t atom
    -- no case for EvalExt because we don't have exts
    -- TODO ReadGlobal
    atomValue stx@(L [A (Kw Deref), e]) =
      do SomeExpr t (E e') <- synthExpr e
         case t of
           ReferenceRepr t' ->
             do anAtom <- eval e e'
                anotherAtom <- freshAtom stmt (ReadRef anAtom)
                return $ Pair t' anotherAtom
           notRef -> throwError $ NotRef stx notRef
    atomValue stx@(L [A (Kw Ref), e]) =
      do SomeExpr t (E e') <- synthExpr e
         anAtom <- eval e e'
         anotherAtom <- freshAtom stmt (NewRef anAtom)
         return $ Pair (ReferenceRepr t) anotherAtom
    atomValue stx@(L [A (Kw EmptyRef), t]) =
      do Some t' <- isType t
         anAtom <- freshAtom stmt (NewEmptyRef t')
         return $ Pair (ReferenceRepr t') anAtom
    atomValue stx@(L (A (Kw Funcall) : fun : args)) =
      do SomeExpr t (E fun') <- synthExpr fun
         case t of
           FunctionHandleRepr argTypes ret ->
             do funAtom <- eval fun fun'
                operandExprs <- lift $ operands (syntaxPos fun) args argTypes
                operandAtoms <- traverseFC (\(Rand a (E e)) -> eval a e) operandExprs
                endAtom <- freshAtom stmt $ Call funAtom operandAtoms ret
                return $ Pair ret endAtom
           other -> throwError $ NotAFunction (syntaxPos fun) fun other
    atomValue expr =
      do SomeExpr tp (E e') <- lift $ synthExpr expr
         atom <- eval expr e'
         return $ Pair tp atom
normStmt stmt@(L [A (Kw SetRegister), regStx, e]) =
  do Pair ty r <- lift $ regRef regStx
     (E e') <- lift $ checkExpr ty e
     v <- eval e e'
     tell [withPosFrom stmt $ SetReg r v]
normStmt other = throwError $ BadStatement (syntaxPos other) other

blockBody :: forall s h ret . Position -> [AST s] -> CFGParser h s ret ([Posd (Stmt () s)], Posd (TermStmt s ret))
blockBody p [] = throwError $ EmptyBlock p
blockBody _p (stmt:stmts) = helper (fmap snd . runWriterT . traverse normStmt) stmt stmts
  where helper ss s [] =
          do stmts <- ss []
             t <- termStmt s
             return (stmts, t)
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

-- | Run a generator monad action corresponding to a terminating statement
termStmt :: AST s -> CFGParser h s ret (Posd (TermStmt s ret))
termStmt stx@(L [A (Kw Jump_), lbl]) =
  withPosFrom stx . Jump <$> labelNoArgs lbl
termStmt stx@(L [A (Kw Branch_), A (At c), l1, l2]) =
  withPosFrom stx <$> (Br <$> typedAtom (syntaxPos stx) BoolRepr c <*> labelNoArgs l1 <*> labelNoArgs l2)
termStmt stx@(L [A (Kw MaybeBranch_), ty, A (At c), l1, l2]) =
  do Pair ty' l1 <- labelArgs l1
     withPosFrom stx <$> (MaybeBranch ty' <$> typedAtom (syntaxPos stx) (MaybeRepr ty') c <*> pure l1 <*> labelNoArgs l2)
-- TODO VariantElim
termStmt stx@(L [A (Kw Return_), (A (At x))]) =
  do ret <- getReturnType
     withPosFrom stx . Return <$> typedAtom (syntaxPos stx) ret x
termStmt stx@(L (A (Kw TailCall_) : atomAst@(A (At f)) : args)) =
  do ret <- getReturnType
     perhapsAtom <- use (stxAtoms . at f)
     case perhapsAtom of
       Nothing -> throwError $ UnknownAtom (syntaxPos stx) f
       Just (Pair (FunctionHandleRepr argTypes ret') at) ->
         case testEquality ret ret' of
           Nothing -> throwError $ TypeError (syntaxPos stx) atomAst ret ret'
           Just Refl ->
             do theArgs <- argAtoms (syntaxPos stx) (toSnoc args) argTypes
                return $ withPosFrom stx (TailCall at argTypes theArgs)
       Just (Pair otherType _) -> throwError $ NotAFunction (syntaxPos stx) atomAst otherType
termStmt stx@(L [A (Kw Error_), msg]) =
  withPosFrom stx . ErrorStmt <$> typedAtom' StringRepr msg
termStmt stx@(L [A (Kw Output_), l, atm]) =
  do Pair ty lbl <- labelArgs l
     arg <- typedAtom' ty atm
     return $ withPosFrom stx (Output lbl arg)
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
    operands' (a:as) (Ctx.AssignExtend argTypes anArgType) =
      do a' <- checkExpr anArgType a
         rest <- operands' as (Ctx.viewAssign argTypes)
         return $ Ctx.extend rest (Rand a a')
    operands' otherArgs otherCtx = throwError $ WrongNumberOfArgs (findPosition argexprs)
    findPosition [] = fpos
    findPosition (e:es) = syntaxPos e

argAtoms :: Position -> SnocList (AST s) -> CtxRepr ctx -> CFGParser h s ret (Ctx.Assignment (Atom s) ctx)
argAtoms p xs ctx =
  case Ctx.view ctx of
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


args :: AST s -> Some (Ctx.Assignment Arg) -> TopParser h s (Some (Ctx.Assignment Arg))
args (L xs) = args' xs
  where
    args' [] soFar = return soFar
    args' (a : as) (Some soFar) =
      do Some (Arg x p t) <- arg a
         args' as (Some $ Ctx.extend soFar (Arg x p t))
args other = const . throwError $ NotArgumentList (syntaxPos other) other


funName :: MonadError (ExprErr s) m => AST s -> m FunctionName
funName (A (Fn (FunName x))) = pure $ functionNameFromText x
funName other = throwError $ NotFunctionName (syntaxPos other) other


saveArgs :: (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m)
         => Ctx.Assignment Arg init
         -> Ctx.Assignment (Atom s) init
         -> m ()
saveArgs ctx1 ctx2 =
  let combined = Ctx.zipWith
                   (\(Arg x p t) at ->
                      (Const (Pair t (Functor.Pair (Const x) (Functor.Pair (Const p) at)))))
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
  do fnName <- funName name
     Some theArgs <- args arglist (Some Ctx.empty)
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


argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ _ t) -> t)


type BlockTodo h s ret =
  (LabelName, BlockID s, Position, [AST s])

blocks :: forall h s ret . Position -> [AST s] -> CFGParser h s ret [Block () s ret]
blocks funPos [] = throwError $ EmptyFunBody funPos
blocks _      (aBlock:moreBlocks) =
  do startContents <- startBlock aBlock
     todo <- allBlockLabels moreBlocks
     blockDefs <- forM (startContents : todo) $ \(lblName, bid, pos, stmts) ->
       do (stmts', term) <- blockBody pos stmts
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
            blockLabel start@(L (A (Kw Start) : (A (Lbl l)) : blockBody)) =
              throwError $ FirstBlockMustBeStart (syntaxPos start) start
            blockLabel (L (kw@(A (Kw DefBlock)) : lStx@(A (Lbl l)) : blockBody)) =
              do lbls <- use stxLabels
                 case Map.lookup l lbls of
                   Just _ -> throwError $ DuplicateLabel (syntaxPos lStx) l
                   Nothing ->
                     do theLbl <- newLabel l
                        return (l, LabelID theLbl, bodyPos kw blockBody, blockBody)
            blockLabel (L (kw@(A (Kw DefBlock)) : lStx@(L [(A (Lbl l)), L [A (At x), t]]) : blockBody)) =
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
                        return (l, LambdaID lbl, bodyPos kw blockBody, blockBody)

            blockLabel other = throwError $ NotABlock (syntaxPos other) other

eval :: AST s -> Expr () s t -> WriterT [Posd (Stmt () s)] (CFGParser h s ret) (Atom s t)
eval stx (App e) = freshAtom stx . EvalApp =<< traverseFC (eval stx) e
eval stx (AtomExpr at) = pure at -- The expression is already evaluated


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


initParser :: (MonadState (SyntaxState h s) m, MonadError (ExprErr s) m) => FunctionHeader -> FunctionSource s -> m ()
initParser (FunctionHeader name (args :: Ctx.Assignment Arg init) ret handle pos) (FunctionSource regs body) =
  do with stxProgState $ put . initSyntaxState
     let types = argTypes args
     let inputAtoms = mkInputAtoms (OtherPos "args") types
     saveArgs args inputAtoms
     forM_ regs saveRegister

  where
    saveRegister (L [A (Rg x), t]) =
      do Some ty <- isType t
         r <- newUnassignedReg ty
         stxRegisters %= Map.insert x (Pair ty r)
    saveRegister other = throwError $ InvalidRegister (syntaxPos other) other

cfgs :: [AST s] -> TopParser h s [ACFG]
cfgs defuns =
  do headers <- traverse functionHeader defuns
     forM headers $
       \(hdr@(FunctionHeader name args ret handle pos), src@(FunctionSource _ body)) ->
         do let types = argTypes args
            initParser hdr src
            let ?returnType = ret
            ACFG types ret <$> (parseCFG handle (blocks pos body))

