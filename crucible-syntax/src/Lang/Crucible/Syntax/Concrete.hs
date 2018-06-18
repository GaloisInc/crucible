{-# LANGUAGE DeriveFunctor, GADTs, OverloadedStrings, RankNTypes, LiberalTypeSynonyms, KindSignatures, DataKinds, StandaloneDeriving, FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies, PolyKinds, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances, PartialTypeSignatures, FlexibleContexts, ImplicitParams, LambdaCase #-}
-- {-# OPTIONS_GHC -fprint-explicit-kinds -fprint-explicit-foralls #-}
module Lang.Crucible.Syntax.Concrete where

import Prelude hiding (fail)

import Data.Monoid

import Control.Lens
import Control.Applicative
import Control.Monad.Fail
import Control.Monad.Identity hiding (fail)
import Control.Monad.Trans.Except
import Control.Monad.State.Class
import Control.Monad.State.Strict
import Control.Monad.Except hiding (fail)
import Control.Monad.Error.Class hiding (fail)
import Control.Monad.Writer.Strict
import Control.Monad.Writer.Class

import Lang.Crucible.Types

import Lang.Crucible.CFG.Core (AnyCFG)

import Data.Functor
import qualified Data.Functor.Product as Functor
import Data.Ratio
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.Map (MapF)
import Data.Parameterized.TraversableFC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Context as Ctx
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as T


import Data.SCargot

import Data.SCargot.Common hiding (At)
import Data.SCargot.Comments
import Data.SCargot.Repr.WellFormed

import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Generator (Generator)
import qualified Lang.Crucible.CFG.Generator as Gen
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Utils.MonadST
import Lang.Crucible.FunctionHandle
import Lang.Crucible.FunctionName

import Numeric.Natural()

import Text.Parsec (try)
import Text.Parsec.Text (Parser)
import Text.Parsec.Char (char, letter)


data Keyword = Defun | DefBlock
             | Start
             | Unpack
             | Plus | Minus | Times | Div
             | Just_ | Nothing_ | FromJust
             | AnyT | UnitT | BoolT | NatT | IntegerT | RealT | ComplexRealT | CharT | StringT
             | BitVectorT
             | The
             | Equalp | Integerp
             | If
             | Pack
             | Not_ | And_ | Or_ | Xor_
             | Mod
             | Lt
             | Jump_ | Return_
             | Print_
  deriving (Eq, Ord)

data Atomic = Kw Keyword -- keywords are all the built-in operators and expression formers
            | Lbl Text -- Labels, but not the trailing colon
            | At Text -- Atom names (which look like Scheme symbols)
            | Rg Text -- Registers, whose names have a leading $
            | Fn Text -- Function names, minus the leading @
            | Int Integer
            | Rat Rational
            | Bool Bool
  deriving (Eq, Ord, Show)

type AST s = WellFormedSExpr Atomic

keywords :: [(Text, Keyword)]
keywords =
  [ ("defun" , Defun)
  , ("defblock" , DefBlock)
  , ("start" , Start)
  , ("unpack" , Unpack)
  , ("+" , Plus)
  , ("-" , Minus)
  , ("*" , Times)
  , ("/" , Div)
  , ("<" , Lt)
  , ("just" , Just_)
  , ("nothing" , Nothing_)
  , ("from-just" , FromJust)
  , ("the" , The)
  , ("equal?" , Equalp)
  , ("integer?" , Integerp)
  , ("Any" , AnyT)
  , ("Unit" , UnitT)
  , ("Bool" , BoolT)
  , ("Nat" , NatT)
  , ("Integer" , IntegerT)
  , ("Real" , RealT)
  , ("ComplexReal" , ComplexRealT)
  , ("Char" , CharT)
  , ("String" , StringT)
  , ("BitVector" , BitVectorT)
  , ("if" , If)
  , ("pack" , Pack)
  , ("not" , Not_)
  , ("and" , And_)
  , ("or" , Or_)
  , ("xor" , Xor_)
  , ("mod" , Mod)
  , ("jump" , Jump_)
  , ("return" , Return_)
  , ("print" , Print_)
  ]

instance Show Keyword where
  show k = case [str | (str, k') <- keywords, k == k'] of
             [] -> "UNKNOWN KW"
             (s:_) -> T.unpack s

kwOrAtom :: Parser Atomic
kwOrAtom = do x <- parseR7RSIdent
              return $ maybe (At x) Kw (lookup x keywords)

atom :: Parser Atomic
atom =  try (Lbl <$> (T.pack <$> many letter) <* char ':')
    <|> kwOrAtom
    <|> Fn <$> (char '@' *> parseR7RSIdent)
    <|> Rg <$> (char '$' *> parseR7RSIdent)
    <|> try (Int . fromInteger <$> signedPrefixedNumber)
    <|> Rat <$> ((%) <$> signedPrefixedNumber <* char '/' <*> prefixedNumber)
    <|> char '#' *>  (char 't' $> Bool True <|> char 'f' $> Bool False)


parseExpr :: SExprParser Atomic (AST s)
parseExpr = withLispComments $ setCarrier toWellFormed $ mkParser atom

printExpr :: SExprPrinter Atomic (AST s)
printExpr = setMaxWidth 72 $ setIndentAmount 2 $ setFromCarrier fromWellFormed $ basicPrint printAtom
  where printAtom (Kw s) = T.pack (show s)
        printAtom (Lbl l) = l <> ":"
        printAtom (Rg r) = "$" <> r
        printAtom (At a) = a
        printAtom (Fn a) = "@" <> a
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
  TooSmall :: NatRepr n -> ExprErr s
  UnknownAtom :: Text -> ExprErr s
  UnknownBlockLabel :: AST s -> ExprErr s
  DuplicateAtom :: Text -> ExprErr s
  DuplicateLabel :: Text -> ExprErr s
  NotArgumentSpec :: AST s -> ExprErr s
  NotFunctionName :: AST s -> ExprErr s
  NotFunDef :: AST s -> ExprErr s
  NotArgumentList :: AST s -> ExprErr s
  NotTermStmt :: AST s -> ExprErr s
  EmptyFunBody :: ExprErr s
  EmptyBlock :: ExprErr s
  NotABlock :: AST s -> ExprErr s
  BadStatement :: AST s -> ExprErr s
  FirstBlockMustBeStart :: AST s -> ExprErr s
  CantJumpToLambda :: AST s -> ExprErr s

deriving instance Show (ExprErr s)
instance Monoid (ExprErr s) where
  mempty = TrivialErr
  mappend = Errs

printExprErr :: ExprErr s -> String
printExprErr = show

data ComparisonCtor s t = ComparisonCtor (Expr () s t -> Expr () s t -> App () (Expr () s) BoolType)

synthComparison :: MapF TypeRepr (ComparisonCtor s)
                -> AST s -> AST s -> AST s
                -> CFGParser h s ret (E s BoolType)
synthComparison ts e a b =
  do SomeExpr t1 (E a') <- synthExpr a
     SomeExpr t2 (E b') <- synthExpr b
     case testEquality t1 t2 of
       Nothing -> throwError$ TypeMismatch a t1 b t2
       Just Refl ->
         case MapF.lookup t1 ts of
           Nothing -> throwError$ NotComparison e t1
           Just (ComparisonCtor f) -> return $ E (App (f a' b'))

checkNumeric :: TypeRepr t1 -> TypeRepr t2
             -> AST s -> AST s -> AST s
             -> (Expr () s t2 -> Expr () s t2 -> App () (Expr () s) t2)
             -> CFGParser h s ret (E s t1)
checkNumeric t1 t2 e a b f =
  case testEquality t1 t2 of
    Just Refl ->
      do E a' <- checkExpr t2 a
         E b' <- checkExpr t2 b
         return (E (App (f a' b')))
    Nothing -> throwError$ NotNumeric e t2

checkExpr :: TypeRepr t -> AST s -> CFGParser h s ret (E s t)
checkExpr (MaybeRepr expectedT) (L [A (Kw Unpack), package]) =
  do E e <- checkExpr AnyRepr package
     return $ E (App (UnpackAny expectedT e))
checkExpr NatRepr (A (Int i)) =
  if i < 0
    then throwError $ NotANat i
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
       Nothing -> throwError $ TypeError ast expectedT foundT


isType :: AST s -> CFGParser h s ret (Some TypeRepr)
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
    _ -> throwError $ NotAType t
isType (L [A (Kw BitVectorT), n]) =
  case n of
    A (Int i) ->
      case someNat i of
        Nothing -> throwError $ NotANat i
        Just (Some len) ->
          case testLeq (knownNat :: NatRepr 1) len of
            Nothing -> throwError $ TooSmall len
            Just LeqProof -> return $ Some $ BVRepr len
    other -> throwError $ NotNumeric other NatRepr
-- TODO more types
isType e = throwError $ NotAType e

synthExpr :: AST s -> CFGParser h s ret (SomeExpr s)
synthExpr (L [A (Kw The), t, e]) =
  do Some ty <- isType t
     e' <- checkExpr ty e
     return $ SomeExpr ty e'
synthExpr (L [A (Kw Equalp), a, b]) =
  do SomeExpr t1 (E a') <- synthExpr a
     SomeExpr t2 (E b') <- synthExpr b
     case testEquality t1 t2 of
       Just Refl ->
         case asBaseType t1 of
           NotBaseType -> throwError $ NotABaseType t1
           AsBaseType bt ->
             return $ SomeExpr BoolRepr (E (App (BaseIsEq bt a' b')))
       Nothing -> throwError $ TypeMismatch a t1 b t2
synthExpr (L [A (Kw If), c, t, f]) =
  do E c' <- checkExpr BoolRepr c
     SomeExpr ty1 (E t') <- synthExpr t
     SomeExpr ty2 (E f') <- synthExpr f
     case testEquality ty1 ty2 of
       Just Refl ->
         case asBaseType ty1 of
           NotBaseType -> throwError $ NotABaseType ty1
           AsBaseType bt ->
             return $ SomeExpr ty1 (E (App (BaseIte bt c' t' f')))
       Nothing -> throwError $ TypeMismatch t ty1 f ty2
synthExpr (L []) =
  return $ SomeExpr UnitRepr (E (App EmptyApp))
synthExpr (L [A (Kw Pack), arg]) =
  do SomeExpr ty (E e) <- synthExpr arg
     return $ SomeExpr AnyRepr (E (App (PackAny ty e)))
  -- TODO case for ConcreteLit
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
  do ats <- use blockAtoms
     case Map.lookup x ats of
       Nothing -> throwError $ UnknownAtom x
       Just (Pair t at) -> return $ SomeExpr t (E at)
synthExpr ast = throwError $ CantSynth ast


-------------------------------------------------------------------------

data LabelInfo :: * -> * where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . TypeRepr ty -> LambdaLabel s ty -> LabelInfo s

data BlockState s = BlockState { _handleAlloc :: () -- TODO delete
                               , _blockLabels :: Map Text (LabelInfo s)
                               , _blockAtoms :: Map Text (Pair TypeRepr (Expr () s))
                               , _nextLabel :: Int
                               , _nextAtom :: Int
                               }

handleAlloc :: Simple Lens (BlockState s) ()
handleAlloc = lens _handleAlloc (\s v -> s { _handleAlloc = v })

blockLabels :: Simple Lens (BlockState s) (Map Text (LabelInfo s))
blockLabels = lens _blockLabels (\s v -> s { _blockLabels = v })

blockAtoms :: Simple Lens (BlockState s) (Map Text (Pair TypeRepr (Expr () s)))
blockAtoms = lens _blockAtoms (\s v -> s { _blockAtoms = v })

nextLabel :: Simple Lens (BlockState s) Int
nextLabel = lens _nextLabel (\s v -> s { _nextLabel = v })

nextAtom :: Simple Lens (BlockState s) Int
nextAtom = lens _nextAtom (\s v -> s { _nextAtom = v })


newtype CFGParser h s ret a =
  CFGParser { runCFGParser :: (?returnType :: TypeRepr ret)
                           => ExceptT (ExprErr s)
                                (StateT (BlockState s) Identity)
                                a
            }
  deriving (Functor)

instance Applicative (CFGParser h s ret) where
  pure x = CFGParser (pure x)
  (CFGParser f) <*> (CFGParser x) = CFGParser (f <*> x)

instance Alternative (CFGParser h s ret) where
  empty = CFGParser $ throwError TrivialErr
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

instance MonadState (BlockState s) (CFGParser h s ret) where
  get = CFGParser get
  put = CFGParser . put

freshIndex :: (MonadState st m, Num n) => Simple Lens st n -> m n
freshIndex l =
  do n <- use l
     l .= n + 1
     return n

freshLabelIndex :: CFGParser h s ret Int
freshLabelIndex = freshIndex nextLabel

freshAtomIndex :: CFGParser h s ret Int
freshAtomIndex = freshIndex nextAtom

freshLabel :: CFGParser h s ret (Label s)
freshLabel = Label <$> freshLabelIndex

freshAtom :: AtomValue () s t -> WriterT [Stmt () s] (CFGParser h s ret) (Atom s t)
freshAtom v =
  do i <- lift freshAtomIndex
     let atom = Atom { atomPosition = OtherPos "Parser internals"
                     , atomId = i
                     , atomSource = Assigned
                     , typeOfAtom = typeOfAtomValue v
                     }
         stmt = DefineAtom atom v
     tell [stmt]
     pure atom

newLabel :: Text -> CFGParser h s ret (Label s)
newLabel x =
  do theLbl <- freshLabel
     blockLabels %= Map.insert x (NoArgLbl theLbl)
     return theLbl

freshLambdaLabel :: TypeRepr tp -> CFGParser h s ret (LambdaLabel s tp, Atom s tp)
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

newLambdaLabel :: Text -> Text -> TypeRepr t -> CFGParser h s ret (LambdaLabel s t)
newLambdaLabel l x t =
  do with (blockLabels . at l) $ maybe (return ()) (const $ throwError $ DuplicateLabel l)
     with (blockAtoms . at x) $ maybe (return ()) (const $ throwError $ DuplicateAtom x)
     (lbl, at) <- freshLambdaLabel t
     blockLabels %= Map.insert l (ArgLbl t lbl)
     blockAtoms %= Map.insert x (Pair t (AtomExpr at)) -- TODO check for duplicate atoms here
     return lbl

getLabel :: Text -> CFGParser h s ret (LabelInfo s)
getLabel x =
  with (blockLabels . at x) $ \case
    Just lbl -> return lbl
    Nothing -> NoArgLbl <$> newLabel x

label :: AST s -> CFGParser h s ret (LabelInfo s)
label (A (Lbl x)) = getLabel x
label other = throwError $ UnknownBlockLabel other

saveAtom :: Text -> TypeRepr ty -> Expr () s ty -> CFGParser h s ret ()
saveAtom x t e =
  with (blockAtoms . at x) $ \case
    Nothing -> blockAtoms %= Map.insert x (Pair t e)
    Just _ -> throwError $ DuplicateAtom x


--------------------------------------------------------------------------

-- | Build an ordinary statement
normStmt :: AST s -> WriterT [Stmt () s] (CFGParser h s ret) ()
normStmt (L [A (Kw Print_), e]) =
  do (E e') <- lift $ checkExpr StringRepr e
     at <- eval e'
     tell [Print at]
normStmt other = throwError $ BadStatement other

blockBody :: forall s h ret . [AST s] -> CFGParser h s ret ([Stmt () s], TermStmt s ret)
blockBody [] = throwError $ EmptyBlock
blockBody (stmt:stmts) = helper (fmap snd . runWriterT . traverse normStmt) stmt stmts
  where helper ss s [] =
          do stmts <- ss []
             t <- termStmt s
             return (stmts, t)
        helper ss s (s':ss') =
          helper (\x -> (ss (s : x))) s' ss'


-- | Run a generator monad action corresponding to a terminating statement
termStmt :: AST s -> CFGParser h s ret (TermStmt s ret)
termStmt (L [A (Kw Jump_), lbl]) =
  do s <- label lbl
     case s of
       NoArgLbl s' -> return $ Jump s'
       ArgLbl ty ll -> throwError $ CantJumpToLambda lbl
-- termStmt (L [A (Kw Jump_), lbl, arg]) =
--   do s <- label lbl
--      case s of
--        NoArgLbl s' -> fail $ "Can't send arguments to a non-lambda label: " ++ show lbl
--        ArgLbl ty ll ->
--          do E theArg <- checkExpr ty arg
--             lift $ Gen.jumpToLambda ll theArg
-- termStmt (L [A (Kw Return_), at]) =
--   do E res <- checkExpr ?returnType at
--      lift $ Gen.returnFromFunction res
termStmt e = throwError $ NotTermStmt e


--------------------------------------------------------------------------

-- | Any CFG, regardless of its arguments and return type, with its helpers
data ACFG :: * where
  ACFG :: forall (s :: *) (init :: Ctx CrucibleType) (ret :: CrucibleType) .
          CtxRepr init -> TypeRepr ret ->
          CFG () s init ret ->
          [AnyCFG ()] ->
          ACFG

deriving instance Show ACFG

data Arg t = Arg Text (TypeRepr t)

arg :: AST s -> CFGParser h s ret (Some Arg)
arg (L [A (At x), t]) =
  do Some t' <- isType t
     return $ Some $ Arg x t'
arg other = throwError $ NotArgumentSpec other


args :: AST s -> Some (Ctx.Assignment Arg) -> CFGParser h s ret (Some (Ctx.Assignment Arg))
args (L []) soFar = return soFar
args (a ::: as) (Some soFar) =
  do Some (Arg x t) <- arg a
     args as (Some $ Ctx.extend soFar (Arg x t))
args other _ = throwError $ NotArgumentList other


funName :: MonadError (ExprErr s) m => AST s -> m FunctionName
funName (A (Fn x)) = pure $ functionNameFromText x
funName other = throwError $ NotFunctionName other


saveArgs :: Ctx.Assignment Arg init -> Ctx.Assignment (Atom s) init -> CFGParser h s ret ()
saveArgs ctx1 ctx2 =
  let combined = Ctx.zipWith (\(Arg x t) at -> (Const (Pair t (Functor.Pair (Const x) at)))) ctx1 ctx2
  in forMFC_ combined $
       \(Const (Pair t (Functor.Pair (Const x) y))) ->
         with (blockAtoms . at x) $ \case
           Just _ -> throwError $ DuplicateAtom x
           Nothing -> blockAtoms %= Map.insert x (Pair t (AtomExpr y))


functionHeader :: AST s -> CFGParser h s ret (FunctionName, Some (Ctx.Assignment Arg), Some TypeRepr, [AST s])
functionHeader (L (A (Kw Defun) : name : arglist : ret : body)) =
  do fnName <- funName name
     theArgs <- args arglist (Some Ctx.empty)
     ty <- isType ret
     return (fnName, theArgs, ty, body)
functionHeader other = throwError $ NotFunDef other

argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ t) -> t)

newtype BlockFun h s ret tp = BlockFun (Atom s tp -> CFGParser h s ret (Seq.Seq (Posd (Stmt () s)), Posd (TermStmt () ret) ))

-- | An existential dependent triple
data Triple (f :: k -> *) (g :: k -> *) (h :: k -> *) where
  Triple :: f a -> g a -> h a -> Triple f g h

type BlockTodo h s ret =
  (Text, BlockID s,  [AST s])

blocks :: forall h s ret a . [AST s] -> CFGParser h s ret [Block () s ret]
blocks [] = throwError EmptyFunBody
blocks (aBlock:moreBlocks) =
  do startContents <- startBlock aBlock
     todo <- allBlockLabels moreBlocks
     blockDefs <- forM todo $ \(lblName, bid, stmts) ->
       do (stmts', term) <- blockBody stmts
          pure $ mkBlock bid mempty (fakePos <$> Seq.fromList stmts') (fakePos term)
     return blockDefs

  where
    fakePos = Posd (OtherPos "fake position")


    startBlock :: AST s -> CFGParser h s ret [AST s]
    startBlock (L (A (Kw Start) : (A (Lbl l)) : stmts)) =
      do lbl <- newLabel l
         blockLabels %= Map.insert l (NoArgLbl lbl)
         return stmts
    startBlock other = throwError $ FirstBlockMustBeStart other

    allBlockLabels :: [AST s] -> CFGParser h s ret [BlockTodo h s ret]
    allBlockLabels = traverse blockLabel
      where blockLabel :: AST s -> CFGParser h s ret (BlockTodo h s ret)
            blockLabel start@(L (A (Kw Start) : (A (Lbl l)) : blockBody)) =
              throwError $ FirstBlockMustBeStart start
            blockLabel (L (A (Kw DefBlock) : (A (Lbl l)) : blockBody)) =
              do lbls <- use blockLabels
                 case Map.lookup l lbls of
                   Just _ -> throwError $ DuplicateLabel l
                   Nothing ->
                     do theLbl <- newLabel l
                        return (l, LabelID theLbl, blockBody)
            blockLabel (L (A (Kw DefBlock) : (L [(A (Lbl l)), L [A (At x), t]]) : blockBody)) =
              do Some ty <- isType t
                 lbls <- use blockLabels
                 case Map.lookup l lbls of
                   Just _ -> throwError $ DuplicateLabel l
                   Nothing ->
                     do lbl <- newLambdaLabel l x ty
                        let lblInfo = ArgLbl ty lbl
                        blockLabels %= Map.insert l lblInfo
                        argAtom <- pure $ lambdaAtom lbl
                        blockAtoms %= Map.insert x (Pair ty (AtomExpr argAtom))
                        return (l, LambdaID lbl, blockBody)

            blockLabel other = throwError $ NotABlock other

    blockContents :: [AST s] -> WriterT [Stmt () s] (CFGParser h s ret) (TermStmt s ret)
    blockContents [] = throwError $ EmptyBlock
    blockContents [term] =
      lift $ termStmt term
    blockContents (stmt1:stmt2:more) =
      do normStmt stmt1
         blockContents (stmt2:more)

eval :: Expr () s t -> WriterT [Stmt () s] (CFGParser h s ret) (Atom s t)
eval (App e) = freshAtom . EvalApp =<< traverseFC eval e
eval (AtomExpr at) = pure at -- The expression is already evaluated





-- cfg :: AST s -> CFGParser h s ret (ST h (ACFG))
-- cfg defun =
--   do (name, Some (args :: Ctx.Assignment Arg init) , Some ret, body) <- functionHeader defun
--      let ?returnType = ret
--      let thing =
--            do ha <- newHandleAllocator
--               let types = argTypes args
--               handle <- mkHandle' ha name types ret
--               (SomeCFG this, others) <- Gen.defineFunction (OtherPos "cfg in parser internals") handle $
--                 \ (argAtoms :: Ctx.Assignment (Atom s) init) ->
--                   let initState = BlockState () Map.empty Map.empty
--                       act = blocks body
--                   in (initState, goExcept act)
--               pure $ ACFG types ret this others
--      return thing
