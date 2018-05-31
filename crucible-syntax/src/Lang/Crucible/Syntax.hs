{-# LANGUAGE GADTs, OverloadedStrings, RankNTypes, LiberalTypeSynonyms, KindSignatures, DataKinds, StandaloneDeriving, FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies, PolyKinds, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_GHC -fprint-explicit-kinds -fprint-explicit-foralls #-}
module Lang.Crucible.Syntax where

import Control.Applicative
import Control.Arrow
import Control.Monad.Identity
import Control.Monad.Reader.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict (StateT(..))
import Control.Monad.Trans.Reader(ReaderT(..))
import Control.Monad.State.Class
import Control.Monad.Except

import Lang.Crucible.Types


import Data.Functor
import Data.Ratio
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T


import Data.SCargot

import Data.SCargot.Common
import Data.SCargot.Comments
import Data.SCargot.Repr.WellFormed

import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Generator
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Utils.MonadST
import Lang.Crucible.FunctionHandle
import Lang.Crucible.FunctionName

import Numeric.Natural()

import Text.Parsec.Text (Parser)
import Text.Parsec.Char (char)


data Atomic = Symbol Text
            | Int Integer
            | Rat Rational
            | Bool Bool
  deriving (Eq, Ord, Show)

type AST s = WellFormedSExpr Atomic


atom :: Parser Atomic
atom =  Symbol <$> parseR7RSIdent
    <|> Int . fromInteger <$> signedPrefixedNumber
    <|> Rat <$> ((%) <$> signedPrefixedNumber <* char '/' <*> prefixedNumber)
    <|> char '#' *>  (char 't' $> Bool True <|> char 'f' $> Bool False)


parseExpr :: SExprParser Atomic (AST s)
parseExpr = withLispComments $ setCarrier toWellFormed $ mkParser atom

printExpr :: SExprPrinter Atomic (AST s)
printExpr = setMaxWidth 72 $ setIndentAmount 2 $ setFromCarrier fromWellFormed $ basicPrint printAtom
  where printAtom (Symbol s) = s
        printAtom (Int i) = T.pack (show i)
        printAtom (Rat r) = T.pack (show r)
        printAtom (Bool b) = if b then "#t" else "#f"



newtype E s t = E (Expr () s t)
  deriving Show


data SomeExpr :: * -> * where
  SomeExpr :: TypeRepr t -> E s t -> SomeExpr s

deriving instance (Show (SomeExpr a))

data ExprErr s where
  TypeError :: AST s -> TypeRepr expected -> TypeRepr found -> ExprErr s
  TypeMismatch :: AST s -> TypeRepr left -> AST s -> TypeRepr right -> ExprErr s
  BadSyntax :: AST s -> ExprErr s
  CantSynth :: AST s -> ExprErr s
  NotAType :: AST s -> ExprErr s
  NotANat :: Integer -> ExprErr s
  NotNumeric :: AST s -> TypeRepr t -> ExprErr s
  NotComparison :: AST s -> TypeRepr t -> ExprErr s
  NotABaseType :: TypeRepr t -> ExprErr s
  TrivialErr :: ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s

deriving instance Show (ExprErr s)
instance Monoid (ExprErr s) where
  mempty = TrivialErr
  mappend = Errs

data ComparisonCtor s t = ComparisonCtor (Expr () s t -> Expr () s t -> App () (Expr () s) BoolType)

synthComparison :: MapF TypeRepr (ComparisonCtor s)
                -> AST s -> AST s -> AST s
                -> Except (ExprErr s) (E s BoolType)
synthComparison ts e a b =
  do SomeExpr t1 (E a') <- synthExpr a
     SomeExpr t2 (E b') <- synthExpr b
     case testEquality t1 t2 of
       Nothing -> throwE $ TypeMismatch a t1 b t2
       Just Refl ->
         case MapF.lookup t1 ts of
           Nothing -> throwE $ NotComparison e t1
           Just (ComparisonCtor f) -> return $ E (App (f a' b'))

checkNumeric :: TypeRepr t1 -> TypeRepr t2
             -> AST s -> AST s -> AST s
             -> (Expr () s t2 -> Expr () s t2 -> App () (Expr () s) t2)
             -> Except (ExprErr s) (E s t1)
checkNumeric t1 t2 e a b f =
  case testEquality t1 t2 of
    Just Refl ->
      do E a' <- checkExpr t2 a
         E b' <- checkExpr t2 b
         return (E (App (f a' b')))
    Nothing -> throwE $ NotNumeric e t2

checkExpr :: TypeRepr t -> AST s -> Except (ExprErr s) (E s t)
checkExpr (MaybeRepr expectedT) (L [A (Symbol "unpack"), package]) =
  do E e <- checkExpr AnyRepr package
     return $ E (App (UnpackAny expectedT e))
checkExpr NatRepr (A (Int i)) =
  if i < 0
    then throwE $ NotANat i
    else return (E (App (NatLit (fromInteger i))))
checkExpr IntegerRepr (A (Int i)) =
  return (E (App (IntLit (fromInteger i))))
checkExpr expectedT e@(L [A (Symbol "+"), a, b]) =
      checkNumeric expectedT NatRepr e a b NatAdd
  <|> checkNumeric expectedT IntegerRepr e a b IntAdd
  <|> checkNumeric expectedT RealValRepr e a b RealAdd
checkExpr expectedT e@(L [A (Symbol "-"), a, b]) =
      checkNumeric expectedT NatRepr e a b NatSub
  <|> checkNumeric expectedT IntegerRepr e a b IntSub
  <|> checkNumeric expectedT RealValRepr e a b RealSub
checkExpr expectedT e@(L [A (Symbol "*"), a, b]) =
      checkNumeric expectedT NatRepr e a b NatMul
  <|> checkNumeric expectedT IntegerRepr e a b IntMul
  <|> checkNumeric expectedT RealValRepr e a b RealMul
checkExpr (MaybeRepr t) (L [A (Symbol "just"), a]) =
  do E a' <- checkExpr t a
     return (E (App (JustValue t a')))
checkExpr (MaybeRepr t) (A (Symbol "nothing")) =
  return (E (App (NothingValue t)))
checkExpr t (L [A (Symbol "from-just"), a, str]) =
  do E a' <- checkExpr (MaybeRepr t) a
     E str' <- checkExpr StringRepr str
     return (E (App (FromJustValue t a' str')))
checkExpr expectedT ast =
  do SomeExpr foundT e <- synthExpr ast
     case testEquality expectedT foundT of
       Just Refl -> return $ e
       Nothing -> throwE $ TypeError ast expectedT foundT

data Ex (f :: k1 -> k2) where
  Ex :: f a -> Ex f

isType :: AST s -> Except (ExprErr s) (Ex TypeRepr)
isType e = throwE $ NotAType e

synthExpr :: AST s -> Except (ExprErr s) (SomeExpr s)
synthExpr (L [A (Symbol "the"), t, e]) =
  do Ex ty <- isType t
     e' <- checkExpr ty e
     return $ SomeExpr ty e'
synthExpr (L [A (Symbol "equal?"), a, b]) =
  do SomeExpr t1 (E a') <- synthExpr a
     SomeExpr t2 (E b') <- synthExpr b
     case testEquality t1 t2 of
       Just Refl ->
         case asBaseType t1 of
           NotBaseType -> throwE $ NotABaseType t1
           AsBaseType bt ->
             return $ SomeExpr BoolRepr (E (App (BaseIsEq bt a' b')))
       Nothing -> throwE $ TypeMismatch a t1 b t2
synthExpr (L [A (Symbol "if"), c, t, f]) =
  do E c' <- checkExpr BoolRepr c
     SomeExpr ty1 (E t') <- synthExpr t
     SomeExpr ty2 (E f') <- synthExpr f
     case testEquality ty1 ty2 of
       Just Refl ->
         case asBaseType ty1 of
           NotBaseType -> throwE $ NotABaseType ty1
           AsBaseType bt ->
             return $ SomeExpr ty1 (E (App (BaseIte bt c' t' f')))
       Nothing -> throwE $ TypeMismatch t ty1 f ty2
synthExpr (L []) =
  return $ SomeExpr UnitRepr (E (App EmptyApp))
synthExpr (L [A (Symbol "pack"), arg]) =
  do SomeExpr ty (E e) <- synthExpr arg
     return $ SomeExpr AnyRepr (E (App (PackAny ty e)))
  -- TODO case for ConcreteLit
synthExpr (A (Bool b)) =
  return $ SomeExpr BoolRepr (E (App (BoolLit b)))
synthExpr (L [A (Symbol "not"), arg]) =
  do E bE <- checkExpr BoolRepr arg
     return $ SomeExpr BoolRepr (E (App (Not bE)))
synthExpr (L [A (Symbol "and"), e1, e2]) =
  do E bE1 <- checkExpr BoolRepr e1
     E bE2 <- checkExpr BoolRepr e2
     return $ SomeExpr BoolRepr (E (App (And bE1 bE2)))
synthExpr (L [A (Symbol "or"), e1, e2]) =
  do E bE1 <- checkExpr BoolRepr e1
     E bE2 <- checkExpr BoolRepr e2
     return $ SomeExpr BoolRepr (E (App (Or bE1 bE2)))
synthExpr (L [A (Symbol "xor"), e1, e2]) =
  do E bE1 <- checkExpr BoolRepr e1
     E bE2 <- checkExpr BoolRepr e2
     return $ SomeExpr BoolRepr (E (App (BoolXor bE1 bE2)))
synthExpr (A (Rat r)) =
  return $ SomeExpr RealValRepr (E (App (RationalLit r)))
synthExpr (L [A (Symbol "/"), e1, e2]) =
  do E rE1 <- checkExpr RealValRepr e1
     E rE2 <- checkExpr RealValRepr e2
     return $ SomeExpr RealValRepr (E (App (RealDiv rE1 rE2)))
synthExpr (L [A (Symbol "mod"), e1, e2]) =
  do E rE1 <- checkExpr RealValRepr e1
     E rE2 <- checkExpr RealValRepr e2
     return $ SomeExpr RealValRepr (E (App (RealMod rE1 rE2)))
synthExpr (L [A (Symbol "integer?"), e]) =
  do E e' <- checkExpr RealValRepr e
     return $ SomeExpr BoolRepr (E (App (RealIsInteger e')))
synthExpr e@(L [A (Symbol "<"), a, b]) =
  SomeExpr BoolRepr <$>
  synthComparison
    (MapF.fromList [ Pair NatRepr (ComparisonCtor NatLt)
                   , Pair IntegerRepr (ComparisonCtor IntLt)
                   , Pair RealValRepr (ComparisonCtor RealLt)
                   ])
    e a b
synthExpr ast = throwE $ CantSynth ast


-------------------------------------------------------------------------

data BlockState s = BlockState { nextLabel :: !Int
                               , blockLabels :: Map Text (Label s)
                               , nextAtom :: !Int
                               , blockAtoms :: Map Text (Pair TypeRepr (Atom s))
                               }

data BlockParseErr s where
  NotTermStmt :: AST s -> BlockParseErr s
  NotBlockID :: AST s -> BlockParseErr s
  NotBlock :: AST s -> BlockParseErr s
  NotFun :: AST s -> BlockParseErr s
  NotArg :: AST s -> BlockParseErr s
  NotArglist :: AST s -> BlockParseErr s
  ExprErr :: ExprErr s -> BlockParseErr s
  ArgNameTaken :: Text -> BlockParseErr s
  InvalidName :: AST s -> BlockParseErr s
  UnknownAtom :: Text -> BlockParseErr s

liftExpr :: Except (ExprErr s) a -> Blocks s a
liftExpr m =
  case runExcept m of
    Left e -> throwError (ExprErr e)
    Right x -> pure x

newtype Blocks s a = Blocks (ExceptT (BlockParseErr s) (ReaderT (HandleAllocator s) (StateT (BlockState s) (ST s))) a)
  deriving (Functor, Applicative, Monad, MonadState (BlockState s), MonadError (BlockParseErr s), MonadReader (HandleAllocator s))

instance MonadST s (Blocks s) where
  liftST m = Blocks $ ExceptT $ ReaderT $ \_ -> StateT $ \s -> fmap (Right &&& const s) m

runBlocks :: Blocks s a -> BlockState s -> ST s (Either (BlockParseErr s) a)
runBlocks (Blocks (ExceptT (ReaderT g))) st =
  withHandleAllocator $
   \ha -> let (StateT f) = g ha
          in fst <$> f st

newLabel :: Text -> Blocks s (Label s)
newLabel x =
  do (BlockState i lbls j ats) <- get
     let theLbl = Label i
     put (BlockState (i + 1) (Map.insert x theLbl lbls) j ats)
     return theLbl

getLabel :: Text -> Blocks s (Label s)
getLabel x =
  do (BlockState _ lbls _ _) <- get
     case Map.lookup x lbls of
       Just lbl -> return lbl
       Nothing -> newLabel x

label :: AST s -> Blocks s (Label s)
label (A (Symbol x)) = getLabel x
label other = throwError (NotBlockID other)

newFunArg :: Text -> TypeRepr t -> Blocks s (Atom s t)
newFunArg x t =
  do (BlockState j lbls i args) <- get
     case Map.lookup x args of
       Just _ -> throwError $ ArgNameTaken x
       Nothing ->
         do let theAtom = Atom (OtherPos "Parser internals") i FnInput t
            put (BlockState j lbls (i + 1) (Map.insert x (Pair t theAtom) args))
            return theAtom

newHandle :: FunctionName ->  CtxRepr args -> TypeRepr ret -> Blocks s (FnHandle args ret)
newHandle fn args ret =
  do ha <- ask
     liftST $ mkHandle' ha fn args ret

atomRef :: Text -> Blocks s (Pair TypeRepr (Atom s))
atomRef x =
  do (BlockState _ _ _ ats) <- get
     case Map.lookup x ats of
       Nothing -> throwError $ UnknownAtom x
       Just y -> return y

--------------------------------------------------------------------------

parseBlockID :: AST s -> Blocks s (BlockID s)
parseBlockID (A (Symbol s)) =  LabelID <$> getLabel s
parseBlockID other = throwError $ NotBlockID other

block :: AST s -> TypeRepr ret -> Blocks s (Block ext s ret)
block (L (A (Symbol "define-block") : bid : rest)) ret =
  do theId <- parseBlockID bid
     _lkjkk
     return $ Block theId _stmts _term _knownInputs _assignedValues
block other ret = throwError $ NotBlock other



--------------------------------------------------------------------------

termStmt :: AST s -> TypeRepr ret -> Blocks s (TermStmt s ret)
termStmt (L [A (Symbol "jump"), lbl]) ret =
  do s <- label lbl
     return $ Jump s
termStmt (L [A (Symbol "return"), at]) ret =
  do a <- cAtom ret at
     return $ Return a
termStmt e ret = throwError (NotTermStmt e)


--------------------------------------------------------------------------

-- | Any CFG, regardless of its arguments and return type
data ACFG (ext :: *) (s :: *) :: * where
  ACFG :: forall (ext :: *) (s :: *) (init :: Ctx CrucibleType) (ret :: CrucibleType) .
          CtxRepr init -> TypeRepr ret ->
          CFG ext s init ret ->
          ACFG ext s


arg :: AST s -> Blocks s (Text, Ex TypeRepr)
arg (L [A (Symbol x), t]) =
  do Ex t' <- liftExpr $ isType t
     _ <- newFunArg x t'
     return (x, Ex t')
arg other = throwError $ NotArg other

args :: AST s -> Ex CtxRepr -> Blocks s (Ex CtxRepr)
args (L []) soFar = return soFar
args (a ::: as) (Ex soFar) =
  do (_, Ex a') <- arg a
     args as (Ex $ Ctx.extend soFar a')
args other _ = throwError $ NotArglist other

funName :: AST s -> Blocks s FunctionName
funName (A (Symbol x)) = pure $ functionNameFromText x
funName other = throwError $ InvalidName other

cfg :: AST s -> Blocks s (ACFG ext s)
cfg (L [A (Symbol "defun"), name, arglist, ret, body]) =
  do fnName <- funName name
     Ex fnArgs <- args arglist (Ex Ctx.empty)
     Ex t <- liftExpr $ isType ret
     handle <- newHandle fnName fnArgs t
     return $ ACFG fnArgs t $ CFG handle _blocks
cfg other = throwError $ NotFun other
