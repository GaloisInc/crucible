{-# LANGUAGE GADTs, OverloadedStrings, RankNTypes, LiberalTypeSynonyms, KindSignatures, DataKinds, StandaloneDeriving, FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies, PolyKinds, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances, PartialTypeSignatures, FlexibleContexts, ImplicitParams #-}
-- {-# OPTIONS_GHC -fprint-explicit-kinds -fprint-explicit-foralls #-}
module Lang.Crucible.Syntax.Concrete where

import Prelude hiding (fail)

import Data.Monoid

import Control.Applicative
import Control.Arrow
import Control.Monad.Fail
import Control.Monad.Identity hiding (fail)
import Control.Monad.Reader.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict (StateT(..))
import Control.Monad.Trans.Reader(ReaderT(..))
import Control.Monad.State.Class
import Control.Monad.Except hiding (fail)

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

import Text.Parsec.Text (Parser)
import Text.Parsec.Char (char, string)


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
  deriving (Eq, Ord, Show)

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

kw :: Parser Keyword
kw =  string "defun" $> Defun
  <|> string "defblock" $> DefBlock
  <|> string "unpack" $> Unpack
  <|> string "+" $> Plus
  <|> string "-" $> Minus
  <|> string "*" $> Times
  <|> string "/" $> Div
  <|> string "<" $> Lt
  <|> string "just" $> Just_
  <|> string "nothing" $> Nothing_
  <|> string "from-just" $> FromJust
  <|> string "the" $> The
  <|> string "equal?" $> Equalp
  <|> string "integer?" $> Integerp
  <|> string "Any" $> AnyT
  <|> string "Unit" $> UnitT
  <|> string "Bool" $> BoolT
  <|> string "Nat" $> NatT
  <|> string "Integer" $> IntegerT
  <|> string "Real" $> RealT
  <|> string "ComplexReal" $> ComplexRealT
  <|> string "Char" $> CharT
  <|> string "String" $> StringT
  <|> string "BitVector" $> BitVectorT
  <|> string "if" $> If
  <|> string "pack" $> Pack
  <|> string "not" $> Not_
  <|> string "and" $> And_
  <|> string "or" $> Or_
  <|> string "xor" $> Xor_
  <|> string "mod" $> Mod
  <|> string "jump" $> Jump_
  <|> string "return" $> Return_
  <|> string "print" $> Print_

atom :: Parser Atomic
atom =  Kw <$> kw
    <|> Lbl <$> parseR7RSIdent <* char ':'
    <|> At <$> parseR7RSIdent
    <|> Fn <$> (char '@' *> parseR7RSIdent)
    <|> Rg <$> (char '$' *> parseR7RSIdent)
    <|> Int . fromInteger <$> signedPrefixedNumber
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

deriving instance Show (ExprErr s)
instance Monoid (ExprErr s) where
  mempty = TrivialErr
  mappend = Errs

printExprErr :: ExprErr s -> String
printExprErr = show

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
checkExpr (MaybeRepr expectedT) (L [A (Kw Unpack), package]) =
  do E e <- checkExpr AnyRepr package
     return $ E (App (UnpackAny expectedT e))
checkExpr NatRepr (A (Int i)) =
  if i < 0
    then throwE $ NotANat i
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
       Nothing -> throwE $ TypeError ast expectedT foundT


isType :: AST s -> Except (ExprErr s) (Some TypeRepr)
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
    _ -> throwE $ NotAType t
isType (L [A (Kw BitVectorT), n]) =
  case n of
    A (Int i) ->
      case someNat i of
        Nothing -> throwE $ NotANat i
        Just (Some len) ->
          case testLeq (knownNat :: NatRepr 1) len of
            Nothing -> throwE $ TooSmall len
            Just LeqProof -> return $ Some $ BVRepr len
    other -> throwE $ NotNumeric other NatRepr
-- TODO more types
isType e = throwE $ NotAType e

synthExpr :: AST s -> Except (ExprErr s) (SomeExpr s)
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
           NotBaseType -> throwE $ NotABaseType t1
           AsBaseType bt ->
             return $ SomeExpr BoolRepr (E (App (BaseIsEq bt a' b')))
       Nothing -> throwE $ TypeMismatch a t1 b t2
synthExpr (L [A (Kw If), c, t, f]) =
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
synthExpr ast = throwE $ CantSynth ast


-------------------------------------------------------------------------

data LabelInfo :: * -> * where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . TypeRepr ty -> LambdaLabel s ty -> LabelInfo s

data BlockState s = BlockState { handleAlloc :: () -- TODO delete
                               , blockLabels :: Map Text (LabelInfo s)
                               , blockAtoms :: Map Text (Pair TypeRepr (Expr () s))
                               }

type CFGParser h s ret a = (?returnType :: TypeRepr ret) => Generator () h s BlockState ret a


liftExpr :: MonadFail m => Except (ExprErr s) a -> m a
liftExpr m =
  case runExcept m of
    Left e -> fail $ printExprErr e
    Right x -> return x

newLabel :: Text -> CFGParser h s ret (Label s)
newLabel x =
  do (BlockState ha lbls ats) <- get
     theLbl <- Gen.newLabel
     put (BlockState ha (Map.insert x (NoArgLbl theLbl) lbls) ats)
     return theLbl

newLambdaLabel :: Text -> TypeRepr t -> CFGParser h s ret (LambdaLabel s t)
newLambdaLabel x t =
  do (BlockState ha lbls ats) <- get
     theLbl <- Gen.newLambdaLabel' t
     put (BlockState ha (Map.insert x (ArgLbl t theLbl) lbls) ats)
     return theLbl

getLabel :: Text -> CFGParser h s ret (LabelInfo s)
getLabel x =
  do (BlockState _ lbls _) <- get
     case Map.lookup x lbls of
       Just lbl -> return lbl
       Nothing -> NoArgLbl <$> newLabel x

label :: AST s -> CFGParser h s ret (LabelInfo s)
label (A (Lbl x)) = getLabel x
label other = fail $ "Unknown block label " ++ show other

saveAtom :: Text -> TypeRepr ty -> Expr () s ty -> CFGParser h s ret ()
saveAtom x t e =
  do (BlockState () lbls ats) <- get
     case Map.lookup x ats of
       Nothing -> put $ BlockState () lbls (Map.insert x (Pair t e) ats)
       Just _ -> fail $ "Atom name already taken: " ++ show x


--------------------------------------------------------------------------


-- | Run a generator monad action corresponding to a terminating statement
termStmt :: forall h s ret a . AST s -> CFGParser h s ret a
termStmt (L [A (Kw Jump_), lbl]) =
  do s <- label lbl
     case s of
       NoArgLbl s' -> Gen.jump s'
       ArgLbl ty ll -> fail $ "Can't jump to a lambda label: " ++ show lbl
termStmt (L [A (Kw Jump_), lbl, arg]) =
  do s <- label lbl
     case s of
       NoArgLbl s' -> fail $ "Can't send arguments to a non-lambda label: " ++ show lbl
       ArgLbl ty ll ->
         do E theArg <- liftExpr $ checkExpr ty arg
            Gen.jumpToLambda ll theArg
termStmt (L [A (Kw Return_), at]) =
  do E res <- liftExpr $ checkExpr ?returnType at
     Gen.returnFromFunction res
termStmt e = fail $ "Not a terminating statement" ++ show e


--------------------------------------------------------------------------

-- | Any CFG, regardless of its arguments and return type, with its helpers
data ACFG :: * where
  ACFG :: forall (s :: *) (init :: Ctx CrucibleType) (ret :: CrucibleType) .
          CtxRepr init -> TypeRepr ret ->
          CFG () s init ret ->
          [AnyCFG ()] ->
          ACFG


data Arg t = Arg Text (TypeRepr t)

arg :: MonadFail m => AST s -> m (Some Arg)
arg (L [A (At x), t]) =
  do Some t' <- liftExpr $ isType t
     return $ Some $ Arg x t'
arg other = fail $ "Not an argument: " ++ show other


args :: MonadFail m => AST s -> Some (Ctx.Assignment Arg) -> m (Some (Ctx.Assignment Arg))
args (L []) soFar = return soFar
args (a ::: as) (Some soFar) =
  do Some (Arg x t) <- arg a
     args as (Some $ Ctx.extend soFar (Arg x t))
args other _ = fail $ "Not an argument list: " ++ show other


funName :: MonadFail m => AST s -> m FunctionName
funName (A (Fn x)) = pure $ functionNameFromText x -- TODO separate lexical category?
funName other = fail $ "Not a function name: " ++ show other


saveArgs :: Ctx.Assignment Arg init -> Ctx.Assignment (Atom s) init -> CFGParser h s ret ()
saveArgs ctx1 ctx2 =
  let combined = Ctx.zipWith (\(Arg x t) at -> (Const (Pair t (Functor.Pair (Const x) at)))) ctx1 ctx2
  in forMFC_ combined $
       \(Const (Pair t (Functor.Pair (Const x) y))) ->
         do (BlockState ha lbls ats) <- get
            case Map.lookup x ats of
              Just _ -> fail $ "Argument name " ++ show x ++ "already used as atom name."
              Nothing -> put $ BlockState ha lbls $ Map.insert x (Pair t (AtomExpr y)) ats


functionHeader :: MonadFail m => AST s -> m (FunctionName, Some (Ctx.Assignment Arg), Some TypeRepr, [AST s])
functionHeader (L (A (Kw Defun) : name : arglist : ret : body)) =
  do fnName <- funName name
     theArgs <- args arglist (Some Ctx.empty)
     ty <- liftExpr $ isType ret
     return (fnName, theArgs, ty, body)
functionHeader other = fail $ "Not a function definition: "  ++ show other

argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ t) -> t)

newtype BlockFun h s ret tp = BlockFun (forall a . Expr () s tp -> CFGParser h s ret a)

-- | An existential dependent triple
data Triple (f :: k -> *) (g :: k -> *) (h :: k -> *) where
  Triple :: f a -> g a -> h a -> Triple f g h

type BlockTodo h s ret = (Text, Either (Label s, [AST s]) (Triple TypeRepr (LambdaLabel s) (BlockFun h s ret)))

blocks :: forall h s ret a . [AST s] -> CFGParser h s ret a
blocks [] = fail "Empty function body"
blocks (aBlock:moreBlocks) =
  do startContents <- startBlock aBlock
     todo <- blockLabels moreBlocks
     forM_ todo $ \(lblName, task) ->
       case task of
         Left (lbl, stmts) ->
           Gen.defineBlock lbl (blockContents stmts) --TODO put the call to blockContents where stmts is made
         Right (Triple argTy lbl (BlockFun f)) ->
           Gen.defineLambdaBlock lbl f
     blockContents startContents

  where
    startBlock :: AST s -> CFGParser h s ret [AST s]
    startBlock (L (A (Kw Start) : (A (Lbl l)) : stmts)) =
      do id <- Gen.currentBlockID
         BlockState ha lbls ats <- get
         case Map.lookup l lbls of
           Just _ -> fail $ "Label " ++ show l ++ " already taken."
           Nothing ->
             case id of
               LabelID lbl ->
                 put (BlockState ha (Map.insert l (NoArgLbl lbl) lbls) ats) $>
                 stmts
               LambdaID lbl ->
                 error "The starting block had a lambda label - inconceivable!"
    startBlock other = fail "The first block must be the starting block."

    blockLabels :: [AST s] -> CFGParser h s ret [BlockTodo h s ret]
    blockLabels = traverse blockLabel
      where blockLabel :: AST s -> CFGParser h s ret (BlockTodo h s ret)
            blockLabel (L (A (Kw Start) : (A (Lbl l)) : blockBody)) =
              fail "The start block must come first"
            blockLabel (L (A (Kw DefBlock) : (A (Lbl l)) : blockBody)) =
              do BlockState ha lbls ats <- get
                 case Map.lookup l lbls of
                   Just _ -> fail $ "Label " ++ show l ++ " already taken."
                   Nothing ->
                     do theLbl <- Gen.newLabel
                        put (BlockState ha (Map.insert l (NoArgLbl theLbl) lbls) ats)
                        return (l, Left (theLbl, blockBody))
            blockLabel (L (A (Kw DefBlock) : (L [(A (Lbl l)), L [A (At x), t]]) : blockBody)) =
              do Some ty <- liftExpr $ isType t
                 BlockState ha lbls ats <- get
                 case Map.lookup l lbls of
                   Just _ -> fail $ "Label " ++ show l ++ " already taken."
                   Nothing ->
                     do lbl <- Gen.newLambdaLabel' ty
                        let lblInfo = ArgLbl ty lbl
                        put (BlockState ha (Map.insert l lblInfo lbls) ats)
                        return (l, (Right (Triple ty lbl (BlockFun $ \arg -> do saveAtom x ty arg; blockContents blockBody))))

            blockLabel other = fail $ "Not a block: " ++ show other

    blockContents :: forall b . [AST s] -> CFGParser h s ret b
    blockContents [] = fail "Blocks may not be empty"
    blockContents [term] =
      termStmt term
    blockContents (stmt1:stmt2:more) =
      do normStmt stmt1
         blockContents (stmt2:more)

-- | Build an ordinary statement
normStmt :: AST s -> CFGParser h s ret ()
normStmt (L [A (Kw Print_), e]) =
  do (E e') <- liftExpr $ checkExpr StringRepr e
     Gen.addPrintStmt e'
normStmt other = fail $ "Unknown statement: " ++ show other


cfg :: MonadFail m => AST s -> m (ST h (ACFG))
cfg defun =
  do (name, Some (args :: Ctx.Assignment Arg init) , Some ret, body) <- functionHeader defun
     let ?returnType = ret
     let thing =
           do ha <- newHandleAllocator
              let types = argTypes args
              handle <- mkHandle' ha name types ret
              (SomeCFG this, others) <- Gen.defineFunction (OtherPos "cfg in parser internals") handle $
                \ (argAtoms :: Ctx.Assignment (Atom s) init) ->
                  let initState = BlockState () Map.empty Map.empty
                      act = blocks body
                  in (initState, act)
              pure $ ACFG types ret this others
     return thing
