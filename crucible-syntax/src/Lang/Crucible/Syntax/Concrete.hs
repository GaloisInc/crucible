{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
  , ParserHooks(..)
  , ParsedProgram(..)
  , defaultParserHooks
  , top
  , cfgs
  , prog
  -- * Low level parsing operations
  , SyntaxState(..)
  , atomName
  , freshAtom
  , nat
  , string
  , isType
  , operands
  , BoundedNat(..)
  , PosNat
  , posNat
  , someAssign
  -- * Rules for pretty-printing language syntax
  , printExpr
  )
where

import Prelude hiding (fail)

import Control.Lens hiding (cons, backwards)
import Control.Applicative
import Control.Monad (MonadPlus(..), forM, join)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Identity ()
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader, ReaderT(..))
import Control.Monad.State.Strict (MonadState(..), StateT(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Except (ExceptT(..))
import Control.Monad.Writer.Strict (MonadWriter(..), WriterT(..))

import Lang.Crucible.Types

import qualified Data.BitVector.Sized as BV
import Data.Foldable
import Data.Functor
import qualified Data.Functor.Product as Functor
import Data.Kind (Type)
import Data.Maybe
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Pair (Pair(..))
import Data.Parameterized.TraversableFC
import Data.Parameterized.Classes
import Data.Parameterized.Nonce ( NonceGenerator, Nonce
                                , freshNonce )
import qualified Data.Parameterized.Context as Ctx
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import Numeric.Natural
import qualified Prettyprinter as PP

import Lang.Crucible.Syntax.ExprParse hiding (SyntaxError)
import qualified Lang.Crucible.Syntax.ExprParse as SP
import Lang.Crucible.Syntax.Monad

import What4.ProgramLoc
import What4.FunctionName
import What4.Symbol
import What4.Utils.StringLiteral

import Lang.Crucible.Syntax.ParsedProgram (ParsedProgram(..))
import Lang.Crucible.Syntax.SExpr (Syntax, pattern L, pattern A, toText, PrintRules(..), PrintStyle(..), syntaxPos, withPosFrom, showAtom)
import Lang.Crucible.Syntax.Atoms hiding (atom)

import Lang.Crucible.CFG.Reg hiding (globalName)
import Lang.Crucible.CFG.Expr

import Lang.Crucible.FunctionHandle

import Numeric.Natural ()
import qualified Data.Set as Set

liftSyntaxParse :: (MonadError (ExprErr s) m, MonadIO m)
                  => SyntaxParse Atomic a -> AST s -> m a
liftSyntaxParse p ast =
  liftIO (syntaxParseIO p ast) >>= \case
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

data E ext s t where
  EAtom  :: !(Atom s t) -> E ext s t
  EReg   :: !Position -> !(Reg s t) -> E ext s t
  EGlob  :: !Position -> !(GlobalVar t) -> E ext s t
  EDeref :: !Position -> !(E ext s (ReferenceType t)) -> E ext s t
  EApp   :: !(App ext (E ext s) t) -> E ext s t

data SomeExpr ext s where
  SomeE :: TypeRepr t -> E ext s t -> SomeExpr ext s
  SomeOverloaded :: AST s -> Keyword -> [SomeExpr ext s] -> SomeExpr ext s
  SomeIntLiteral :: AST s -> Integer -> SomeExpr ext s

data SomeBVExpr ext s where
  SomeBVExpr :: (1 <= w) => NatRepr w -> E ext s (BVType w) -> SomeBVExpr ext s

data ExprErr s where
  TrivialErr :: Position -> ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s
  DuplicateAtom :: Position -> AtomName -> ExprErr s
  DuplicateLabel :: Position -> LabelName -> ExprErr s
  EmptyBlock :: Position -> ExprErr s
  NotGlobal :: Position -> AST s -> ExprErr s
  InvalidRegister :: Position -> AST s -> ExprErr s
  SyntaxParseError :: SP.SyntaxError Atomic -> ExprErr s

deriving instance Show (ExprErr s)

instance Semigroup (ExprErr s) where
  (<>) = Errs

instance Monoid (ExprErr s) where
  mempty = TrivialErr (OtherPos "mempty")

instance PP.Pretty (ExprErr s) where
  pretty =
    \case
      TrivialErr p ->
        "Trivial error at" PP.<+> PP.viaShow p
      Errs e1 e2 ->
        PP.vcat ["Multiple errors:" , PP.pretty e1 , PP.pretty e2]
      DuplicateAtom p a ->
        PP.hsep ["Duplicate atom", backticks (PP.pretty a), "at", PP.viaShow p]
      DuplicateLabel p l ->
        PP.hsep ["Duplicate label", backticks (PP.pretty l), "at", PP.viaShow p]
      EmptyBlock p ->
        "Empty block at" PP.<+> PP.viaShow p
      NotGlobal p _ast ->
        "Expected a global at" PP.<+> PP.viaShow p
      InvalidRegister p _ast ->
        "Expected a register at" PP.<+> PP.viaShow p
      SyntaxParseError err ->
        PP.pretty (printSyntaxError err)
    where backticks = PP.enclose "`" "`"

-- | ParserHooks enables support for arbitrary syntax extensions by allowing
-- users to supply their own parsers for types and syntax extensions.
data ParserHooks ext = ParserHooks {
    -- | extensionTypeParser is called for all type specifications and enables
    -- the addition of new types to crucible-syntax.
    extensionTypeParser :: forall m. MonadSyntax Atomic m => m (Some TypeRepr)

    -- | extensionParser is called when parsing statements and let bindings
    -- (everywhere function calls are supported) and enables the addition of
    -- syntax extensions to crucible-syntax.
  , extensionParser
    :: forall s m
     . ( MonadSyntax Atomic m
       , MonadWriter [Posd (Stmt ext s)] m
       , MonadState (SyntaxState s) m
       , MonadIO m
       , IsSyntaxExtension ext
       , ?parserHooks :: ParserHooks ext
       -- ParserHooks instance to use recursively when parsing.
       )
    => m (Some (Atom s))
    -- ^ The atom computed from evaluating the syntax extension.
}

-- | A ParserHooks instance that adds no extensions to the crucible-syntax
-- language.
defaultParserHooks :: ParserHooks ()
defaultParserHooks = ParserHooks empty empty

kw :: MonadSyntax Atomic m => Keyword -> m ()
kw k = describe ("the keyword " <> showAtom (Kw k)) (atom (Kw k))

int :: MonadSyntax Atomic m => m Integer
int = sideCondition "integer literal" numeric atomic
  where numeric (Int i) = Just i
        numeric _ = Nothing

nat :: MonadSyntax Atomic m => m Natural
nat = sideCondition "natural literal" isNat atomic
  where isNat (Int i) | i >= 0 = Just (fromInteger i)
        isNat _ = Nothing

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

roundingMode :: MonadSyntax Atomic m => m RoundingMode
roundingMode = describe "rounding mode" $
        asum [ kw RNE_ $> RNE
             , kw RNA_ $> RNA
             , kw RTP_ $> RTP
             , kw RTN_ $> RTN
             , kw RTZ_ $> RTZ
             ]

fpinfo :: MonadSyntax Atomic m => m (Some FloatInfoRepr)
fpinfo = asum [ kw Half_         $> Some HalfFloatRepr
              , kw Float_        $> Some SingleFloatRepr
              , kw Double_       $> Some DoubleFloatRepr
              , kw Quad_         $> Some QuadFloatRepr
              , kw X86_80_       $> Some X86_80FloatRepr
              , kw DoubleDouble_ $> Some DoubleDoubleFloatRepr
              ]

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

_isBaseType :: ( ?parserHooks :: ParserHooks ext, MonadSyntax Atomic m )
            => m (Some BaseTypeRepr)
_isBaseType =
  describe "base type" $
  do Some tp <- isType
     case asBaseType tp of
       NotBaseType -> empty
       AsBaseType bt -> return (Some bt)

_isFloatingType :: ( ?parserHooks :: ParserHooks ext, MonadSyntax Atomic m )
                => m (Some FloatInfoRepr)
_isFloatingType =
  describe "floating-point type" $
  do Some tp <- isType
     case tp of
       FloatRepr fi -> return (Some fi)
       _ -> empty

data BoundedNat bnd =
  forall w. (bnd <= w) => BoundedNat (NatRepr w)

type PosNat = BoundedNat 1

posNat :: MonadSyntax Atomic m => m PosNat
posNat =
   do i <- sideCondition "positive nat literal" checkPosNat nat
      maybe empty return $ do Some x <- return $ mkNatRepr i
                              LeqProof <- isPosNat x
                              return $ BoundedNat x
  where checkPosNat i | i > 0 = Just i
        checkPosNat _ = Nothing

natRepr :: MonadSyntax Atomic m => m (Some NatRepr)
natRepr = mkNatRepr <$> nat

stringSort :: MonadSyntax Atomic m => m (Some StringInfoRepr)
stringSort =
  later $ describe "string sort" $
    asum [ kw Unicode_ $> Some UnicodeRepr
         , kw Char16_  $> Some Char16Repr
         , kw Char8_   $> Some Char8Repr
         ]

isType :: ( ?parserHooks :: ParserHooks ext, MonadSyntax Atomic m )
       => m (Some TypeRepr)
isType =
  describe "type" $ call
    (atomicType <|> stringT <|> vector <|> seqt <|> ref <|> bv <|> fp <|> fun <|> maybeT <|> var <|> struct <|> (extensionTypeParser ?parserHooks))

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
             ]
    vector = unary VectorT isType <&> \(Some t) -> Some (VectorRepr t)
    seqt   = unary SequenceT isType <&> \(Some t) -> Some (SequenceRepr t)
    ref    = unary RefT isType <&> \(Some t) -> Some (ReferenceRepr t)
    bv :: MonadSyntax Atomic m => m  (Some TypeRepr)
    bv     = do BoundedNat len <- unary BitvectorT posNat
                return $ Some $ BVRepr len

    fp :: MonadSyntax Atomic m => m (Some TypeRepr)
    fp = do Some fpi <- unary FPT fpinfo
            return $ Some $ FloatRepr fpi

    fun :: MonadSyntax Atomic m => m (Some TypeRepr)
    fun = cons (kw FunT) (repUntilLast isType) <&> \((), (args, ret)) -> mkFunRepr args ret

    stringT :: MonadSyntax Atomic m => m (Some TypeRepr)
    stringT = unary StringT stringSort <&> \(Some si) -> Some (StringRepr si)

    maybeT = unary MaybeT isType <&> \(Some t) -> Some (MaybeRepr t)

    var :: MonadSyntax Atomic m => m (Some TypeRepr)
    var = cons (kw VariantT) (rep isType) <&> \((), toCtx -> Some tys) -> Some (VariantRepr tys)

    struct ::  MonadSyntax Atomic m => m (Some TypeRepr)
    struct = cons (kw StructT) (rep isType) <&> \((), toCtx -> Some tys) -> Some (StructRepr tys)

someExprType :: SomeExpr ext s -> Maybe (Some TypeRepr)
someExprType (SomeE tpr _) = Just (Some tpr)
someExprType _ = Nothing


findJointType :: Maybe (Some TypeRepr) -> [SomeExpr ext s] -> Maybe (Some TypeRepr)
findJointType = foldr (\y x -> f x (someExprType y))
 where
 f Nothing y    = y
 f x@(Just _) _ = x

evalOverloaded :: forall m s t ext. MonadSyntax Atomic m => AST s -> TypeRepr t -> Keyword -> [SomeExpr ext s] -> m (E ext s t)
evalOverloaded ast tpr k = withFocus ast .
  case (k, tpr) of
    (Plus, NatRepr)     -> nary NatAdd    (NatLit 0)
    (Plus, IntegerRepr) -> nary IntAdd    (IntLit 0)
    (Plus, RealValRepr) -> nary RealAdd   (RationalLit 0)
    (Plus, BVRepr w)    -> nary (BVAdd w) (BVLit w (BV.zero w))

    (Times, NatRepr)     -> nary NatMul    (NatLit 1)
    (Times, IntegerRepr) -> nary IntMul    (IntLit 1)
    (Times, RealValRepr) -> nary RealMul   (RationalLit 1)
    (Times, BVRepr w)    -> nary (BVMul w) (BVLit w (BV.one w))

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
 u :: (E ext s t -> App ext (E ext s) t) -> [SomeExpr ext s] -> m (E ext s t)
 u f [x] = EApp . f <$> evalSomeExpr tpr x
 u _ _ = later $ describe "one argument" $ empty

 bin :: (E ext s t -> E ext s t -> App ext (E ext s) t) -> [SomeExpr ext s] -> m (E ext s t)
 bin f [x,y] = EApp <$> (f <$> evalSomeExpr tpr x <*> evalSomeExpr tpr y)
 bin _ _ = later $ describe "two arguments" $ empty

 nary :: (E ext s t -> E ext s t -> App ext (E ext s) t) -> App ext (E ext s) t -> [SomeExpr ext s] -> m (E ext s t)
 nary _ z []     = return $ EApp z
 nary _ _ [x]    = evalSomeExpr tpr x
 nary f _ (x:xs) = go f <$> evalSomeExpr tpr x <*> mapM (evalSomeExpr tpr) xs

 go f x (y:ys) = go f (EApp $ f x y) ys
 go _ x []     = x


evalSomeExpr :: MonadSyntax Atomic m => TypeRepr t -> SomeExpr ext s -> m (E ext s t)
evalSomeExpr tpr (SomeE tpr' e)
  | Just Refl <- testEquality tpr tpr' = return e
  | otherwise = later $ describe ("matching types (" <> T.pack (show tpr)
                                  <> " /= " <> T.pack (show tpr') <> ")") empty
evalSomeExpr tpr (SomeOverloaded ast k args) = evalOverloaded ast tpr k args
evalSomeExpr tpr (SomeIntLiteral ast i) = evalIntLiteral ast tpr i

applyOverloaded ::
  MonadSyntax Atomic m => AST s -> Keyword -> Maybe (Some TypeRepr) -> [SomeExpr ext s] -> m (SomeExpr ext s)
applyOverloaded ast k mtp args =
  case findJointType mtp args of
    Nothing -> return $ SomeOverloaded ast k args
    Just (Some tp) -> SomeE tp <$> evalOverloaded ast tp k args

evalIntLiteral :: MonadSyntax Atomic m => AST s -> TypeRepr tpr -> Integer -> m (E ext s tpr)
evalIntLiteral _ NatRepr i | i >= 0 = return $ EApp $ NatLit (fromInteger i)
evalIntLiteral _ IntegerRepr i = return $ EApp $ IntLit i
evalIntLiteral _ RealValRepr i = return $ EApp $ RationalLit (fromInteger i)
evalIntLiteral ast tpr _i =
  withFocus ast $ later $ describe ("literal " <> T.pack (show tpr) <> " value") empty

forceSynth :: MonadSyntax Atomic m => SomeExpr ext s -> m (Pair TypeRepr (E ext s))
forceSynth (SomeE tp e) = return $ Pair tp e
forceSynth (SomeOverloaded ast _ _) =
  withFocus ast $ later (describe "unambiguous expression (add type annotation to disambiguate)" empty)
forceSynth (SomeIntLiteral ast _) =
  withFocus ast $ later (describe "unambiguous numeric literal (add type annotation to disambiguate)" empty)

synth
  :: forall m s ext
   . ( MonadReader (SyntaxState s) m
     , MonadSyntax Atomic m
     , ?parserHooks :: ParserHooks ext )
  => m (Pair TypeRepr (E ext s))
synth = forceSynth =<< synth'

synth' :: forall m s ext
        .  ( MonadReader (SyntaxState s) m
           , MonadSyntax Atomic m
           , ?parserHooks :: ParserHooks ext )
       => m (SomeExpr ext s)
synth' = synthExpr Nothing

synthExpr :: forall m s ext
           . ( MonadReader (SyntaxState s) m
             , MonadSyntax Atomic m
             , ?parserHooks :: ParserHooks ext )
          => Maybe (Some TypeRepr)
          -> m (SomeExpr ext s)
synthExpr typeHint =
  describe "expression" $
    call (the <|> crucibleAtom <|> regRef <|> globRef <|> deref <|>
     bvExpr <|>
     naryBool And_ And True <|> naryBool Or_ Or False <|> naryBool Xor_ BoolXor False <|>
     unaryArith Negate <|> unaryArith Abs <|>
     naryArith Plus <|> binaryArith Minus <|> naryArith Times <|> binaryArith Div <|> binaryArith Mod <|>
     unitCon <|> boolLit <|> stringLit <|> funNameLit <|>
     notExpr <|> equalp <|> lessThan <|> lessThanEq <|>
     toAny <|> fromAny <|> stringAppend <|> stringEmpty <|> stringLength <|> showExpr <|>
     just <|> nothing <|> fromJust_ <|> injection <|> projection <|>
     vecLit <|> vecCons <|> vecRep <|> vecLen <|> vecEmptyP <|> vecGet <|> vecSet <|>
     struct <|> getField <|> setField <|>
     seqNil <|> seqCons <|> seqAppend <|> seqNilP <|> seqLen <|>
     seqHead <|> seqTail <|> seqUncons <|>
     ite <|>  intLit <|> rationalLit <|> intp <|>
     binaryToFp <|> fpToBinary <|> realToFp <|> fpToReal <|>
     ubvToFloat <|> floatToUBV <|> sbvToFloat <|> floatToSBV <|>
     unaryBV BVNonzero_ BVNonzero <|> compareBV BVCarry_ BVCarry <|>
     compareBV BVSCarry_ BVSCarry <|> compareBV BVSBorrow_ BVSBorrow <|>
     compareBV Slt BVSlt <|> compareBV Sle BVSle)

-- Syntactic constructs still to add (see issue #74)

-- BvToInteger, SbvToInteger, BvToNat
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
    the :: m (SomeExpr ext s)
    the = do describe "type-annotated expression" $
               kw The `followedBy`
                 (depCons isType $
                  \(Some t) ->
                    do (e, ()) <- cons (check t) emptyList
                       return $ SomeE t e)

    okAtom theAtoms x =
      case Map.lookup x theAtoms of
        Nothing -> Nothing
        Just (Some anAtom) -> Just $ SomeE (typeOfAtom anAtom) (EAtom anAtom)

    regRef :: m (SomeExpr ext s)
    regRef =
      do Some r <- regRef'
         loc <- position
         return (SomeE (typeOfReg r) (EReg loc r))

    deref :: m (SomeExpr ext s)
    deref =
      do let newhint = case typeHint of
                         Just (Some t) -> Just (Some (ReferenceRepr t))
                         _ -> Nothing
         unary Deref (forceSynth =<< synthExpr newhint) >>= \case
           Pair (ReferenceRepr t') e ->
             do loc <- position
                return (SomeE t' (EDeref loc e))
           Pair notRef _ -> later $ describe ("reference type (provided a " <> T.pack (show notRef) <> ")") empty

    globRef :: m (SomeExpr ext s)
    globRef =
      do Some g <- globRef'
         loc <- position
         return (SomeE (globalType g) (EGlob loc g))

    crucibleAtom :: m (SomeExpr ext s)
    crucibleAtom =
      do theAtoms <- view stxAtoms
         sideCondition "known atom" (okAtom theAtoms) atomName

    unitCon = describe "unit constructor" (emptyList $> SomeE UnitRepr (EApp EmptyApp))

    boolLit = bool <&> SomeE BoolRepr . EApp . BoolLit

    stringLit = string <&> SomeE (StringRepr UnicodeRepr) . EApp . StringLit . UnicodeLiteral

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

    bvExpr :: m (SomeExpr ext s)
    bvExpr =
      do let nathint = case typeHint of Just (Some (BVRepr w)) -> NatHint w; _ -> NoHint
         SomeBVExpr w x <- synthBV nathint
         return $ SomeE (BVRepr w) x

    intp =
      do e <- unary Integerp (check RealValRepr)
         return $ SomeE BoolRepr $ EApp $ RealIsInteger e

    funNameLit =
      do fn <- funName
         fh <- view $ stxFunctions . at fn
         dh <- view $ stxForwardDecs . at fn
         describe "known function name" $
           -- First look for a function with the given name, and failing that,
           -- look for a forward declaration with the given name.
           case fh <|> dh of
             Nothing -> empty
             Just (FunctionHeader _ funArgs ret handle _) ->
               return $ SomeE (FunctionHandleRepr (argTypes funArgs) ret) (EApp $ HandleLit handle)

    notExpr =
      do e <- describe "negation expression" $ unary Not_ (check BoolRepr)
         return $ SomeE BoolRepr $ EApp $ Not e

    matchingExprs ::
      Maybe (Some TypeRepr) -> SomeExpr ext s -> SomeExpr ext s ->
      (forall tp. TypeRepr tp -> E ext s tp -> E ext s tp -> m a) ->
      m a
    matchingExprs h e1 e2 k =
      case findJointType h [e1,e2] of
        Just (Some tp) ->
          do e1' <- evalSomeExpr tp e1
             e2' <- evalSomeExpr tp e2
             k tp e1' e2'
        Nothing ->
          later $ describe ("type annotation required to disambiguate types") empty

    equalp :: m (SomeExpr ext s)
    equalp =
      do (e1, e2) <- describe "equality test" $ binary Equalp synth' synth'
         matchingExprs Nothing e1 e2 $ \tp e1' e2' ->
          case tp of
            FloatRepr _fi ->
              return $ SomeE BoolRepr $ EApp $ FloatEq e1' e2'
            ReferenceRepr rtp ->
              return $ SomeE BoolRepr $ EApp $ ReferenceEq rtp e1' e2'
            NatRepr ->
              return $ SomeE BoolRepr $ EApp $ NatEq e1' e2'
            (asBaseType -> AsBaseType bt) ->
              return $ SomeE BoolRepr $ EApp $ BaseIsEq bt e1' e2'
            _ ->
              later $ describe ("a base type or floating point type or reference type (got " <> T.pack (show tp) <> ")") empty

    compareBV ::
      Keyword ->
      (forall w. (1 <= w) => NatRepr w -> E ext s (BVType w) -> E ext s (BVType w) -> App ext (E ext s) BoolType) ->
      m (SomeExpr ext s)
    compareBV k f =
      do (e1, e2) <- describe "bitvector compaprison" $ binary k synth' synth'
         matchingExprs Nothing e1 e2 $ \tp e1' e2' ->
           case tp of
             BVRepr w ->
               return $ SomeE BoolRepr $ EApp $ f w e1' e2'
             _ ->
               later $ describe ("a bitvector type (got " <> T.pack (show tp) <> ")") empty

    lessThan :: m (SomeExpr ext s)
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

    lessThanEq :: m (SomeExpr ext s)
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

    naryArith :: Keyword -> m (SomeExpr ext s)
    naryArith k =
      do ast <- anything
         args <- followedBy (kw k) (commit *> (rep (synthExpr typeHint)))
         applyOverloaded ast k typeHint args

    binaryArith :: Keyword -> m (SomeExpr ext s)
    binaryArith k =
      do ast <- anything
         (x, y) <- binary k (synthExpr typeHint) (synthExpr typeHint)
         applyOverloaded ast k typeHint [x,y]

    unaryArith :: Keyword -> m (SomeExpr ext s)
    unaryArith k =
      do ast <- anything
         x <- unary k (synthExpr typeHint)
         applyOverloaded ast k typeHint [x]

    unaryBV ::
      Keyword ->
      (forall w. (1 <= w) => NatRepr w -> E ext s (BVType w) -> App ext (E ext s) BoolType) ->
      m (SomeExpr ext s)
    unaryBV k f =
      do Pair t x <- unary k synth
         case t of
           BVRepr w ->return $ SomeE BoolRepr $ EApp $ f w x
           _ -> later $ describe "bitvector argument" empty

    just :: m (SomeExpr ext s)
    just =
      do let newhint = case typeHint of
                         Just (Some (MaybeRepr t)) -> Just (Some t)
                         _ -> Nothing
         Pair t x <- unary Just_ (forceSynth =<< synthExpr newhint)
         return $ SomeE (MaybeRepr t) $ EApp $ JustValue t x

    nothing :: m (SomeExpr ext s)
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

    fromJust_ :: m (SomeExpr ext s)
    fromJust_ =
      do let newhint = case typeHint of
                         Just (Some t) -> Just (Some (MaybeRepr t))
                         _ -> Nothing
         describe "coercion from Maybe (fromJust-expression)" $
           followedBy (kw FromJust) $
           depCons (forceSynth =<< synthExpr newhint) $ \(Pair t e) ->
             case t of
               MaybeRepr elemT ->
                 depCons (check (StringRepr UnicodeRepr)) $ \str ->
                   do emptyList
                      return $ SomeE elemT $ EApp $ FromJustValue elemT e str
               _ -> later $ describe "maybe expression" nothing

    projection :: m (SomeExpr ext s)
    projection =
      do (n, Pair t e) <- describe "projection from variant type" $ binary Proj int synth
         case t of
           VariantRepr ts ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = MaybeRepr (ts ^. ixF' idx)
                    return $ SomeE ty $ EApp $ ProjectVariant ts idx e
           _ -> describe ("variant type (got " <> T.pack (show t) <> ")") empty

    injection :: m (SomeExpr ext s)
    injection =
      do (n, e) <- describe "injection into variant type" $ binary Inj int anything
         case typeHint of
           Just (Some (VariantRepr ts)) ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = view (ixF' idx) ts
                    out <- withProgressStep Rest $ withProgressStep Rest $ withProgressStep First $
                             parse e (check ty)
                    return $ SomeE (VariantRepr ts) $ EApp $ InjectVariant ts idx out
           Just (Some t) ->
             describe ("context expecting variant type (got " <> T.pack (show t) <> ")") empty
           Nothing ->
             describe ("unambiguous variant") empty

    fpToBinary :: m (SomeExpr ext s)
    fpToBinary =
       kw FPToBinary_ `followedBy`
       (depConsCond synth $ \(Pair tp x) ->
         case tp of
           FloatRepr fpi
             | BaseBVRepr w <- floatInfoToBVTypeRepr fpi
             , Just LeqProof <- isPosNat w ->
                 emptyList $> (Right $ SomeE (BVRepr w) $ EApp $ FloatToBinary fpi x)
           _ -> pure $ Left $ "floating-point value")

    binaryToFp :: m (SomeExpr ext s)
    binaryToFp =
       kw BinaryToFP_ `followedBy`
       (depCons fpinfo $ \(Some fpi) ->
        depCons (check (baseToType (floatInfoToBVTypeRepr fpi))) $ \x ->
        emptyList $> (SomeE (FloatRepr fpi) $ EApp $ FloatFromBinary fpi x))

    fpToReal :: m (SomeExpr ext s)
    fpToReal =
       kw FPToReal_ `followedBy`
       (depConsCond synth $ \(Pair tp x) ->
         case tp of
           FloatRepr _fpi -> emptyList $> (Right $ SomeE RealValRepr $ EApp $ FloatToReal x)
           _ -> pure $ Left "floating-point value")

    realToFp :: m (SomeExpr ext s)
    realToFp =
       kw RealToFP_ `followedBy`
       (depCons fpinfo $ \(Some fpi) ->
        depCons roundingMode $ \rm ->
        depCons (check RealValRepr) $ \x ->
        emptyList $> (SomeE (FloatRepr fpi) $ EApp $ FloatFromReal fpi rm x))

    ubvToFloat :: m (SomeExpr ext s)
    ubvToFloat =
       kw UBVToFP_ `followedBy`
       (depCons fpinfo $ \(Some fpi) ->
        depCons roundingMode $ \rm ->
        depConsCond synth $ \(Pair tp x) ->
          case tp of
            BVRepr _w ->
              emptyList $> (Right $ SomeE (FloatRepr fpi) $ EApp $ FloatFromBV fpi rm x)
            _ -> pure $ Left $ "bitvector value"
        )

    sbvToFloat :: m (SomeExpr ext s)
    sbvToFloat =
       kw SBVToFP_ `followedBy`
       (depCons fpinfo $ \(Some fpi) ->
        depCons roundingMode $ \rm ->
        depConsCond synth $ \(Pair tp x) ->
          case tp of
            BVRepr _w ->
              emptyList $> (Right $ SomeE (FloatRepr fpi) $ EApp $ FloatFromSBV fpi rm x)
            _ -> pure $ Left $ "bitvector value"
       )

    floatToUBV :: m (SomeExpr ext s)
    floatToUBV =
       kw FPToUBV_ `followedBy`
       (depCons posNat $ \(BoundedNat w) ->
        depCons roundingMode $ \rm ->
        depConsCond synth $ \(Pair tp x) ->
          case tp of
            FloatRepr _fpi ->
              emptyList $> (Right $ SomeE (BVRepr w) $ EApp $ FloatToBV w rm x)
            _ -> pure $ Left $ "floating-point value")

    floatToSBV :: m (SomeExpr ext s)
    floatToSBV =
       kw FPToSBV_ `followedBy`
       (depCons posNat $ \(BoundedNat w) ->
        depCons roundingMode $ \rm ->
        depConsCond synth $ \(Pair tp x) ->
          case tp of
            FloatRepr _fpi ->
              emptyList $> (Right $ SomeE (BVRepr w) $ EApp $ FloatToSBV w rm x)
            _ -> pure $ Left $ "floating-point value")

    ite :: m (SomeExpr ext s)
    ite =
      do (c, (et, (ef, ()))) <-
           followedBy (kw If) $
           cons (check BoolRepr) $
           cons (synthExpr typeHint) $
           cons (synthExpr typeHint) $
           emptyList
         matchingExprs typeHint et ef $ \tp t f ->
          case tp of
            FloatRepr fi ->
               return $ SomeE tp $ EApp $ FloatIte fi c t f
            NatRepr ->
               return $ SomeE tp $ EApp $ NatIte c t f
            (asBaseType -> AsBaseType bty) ->
               return $ SomeE tp $ EApp $ BaseIte bty c t f
            _ ->
               let msg = T.concat [ "conditional where branches have base or floating point type, but got "
                                  , T.pack (show tp)
                                  ]
               in later $ describe msg empty

    toAny =
      do Pair tp e <- unary ToAny synth
         return $ SomeE AnyRepr (EApp (PackAny tp e))
    fromAny =
      (binary FromAny isType (check AnyRepr)) <&>
        \(Some ty, e) -> SomeE (MaybeRepr ty) (EApp (UnpackAny ty e))

    stringLength :: m (SomeExpr ext s)
    stringLength =
      do unary StringLength_
           (do (Pair ty e) <- forceSynth =<< synthExpr Nothing
               case ty of
                 StringRepr _si -> return $ SomeE IntegerRepr $ EApp (StringLength e)
                 _ -> later $ describe "string expression" empty)

    stringEmpty =
      unary StringEmpty_ stringSort <&> \(Some si) -> SomeE (StringRepr si) $ EApp $ StringEmpty si

    stringAppend :: m (SomeExpr ext s)
    stringAppend =
      do (e1,(e2,())) <-
           followedBy (kw StringConcat_) $
           cons (synthExpr typeHint) $
           cons (synthExpr typeHint) $
           emptyList
         matchingExprs typeHint e1 e2 $ \tp s1 s2 ->
           case tp of
             StringRepr si -> return $ SomeE (StringRepr si) $ EApp $ StringConcat si s1 s2
             _ -> later $ describe "string expressions" empty

    vecRep :: m (SomeExpr ext s)
    vecRep =
      do let newhint = case typeHint of
                         Just (Some (VectorRepr t)) -> Just (Some t)
                         _ -> Nothing
         (n, Pair t e) <-
           binary VectorReplicate_ (check NatRepr) (forceSynth =<< synthExpr newhint)
         return $ SomeE (VectorRepr t) $ EApp $ VectorReplicate t n e

    vecLen :: m (SomeExpr ext s)
    vecLen =
      do Pair t e <- unary VectorSize_ synth
         case t of
           VectorRepr _ -> return $ SomeE NatRepr $ EApp $ VectorSize e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecEmptyP :: m (SomeExpr ext s)
    vecEmptyP =
      do Pair t e <- unary VectorIsEmpty_ synth
         case t of
           VectorRepr _ -> return $ SomeE BoolRepr $ EApp $ VectorIsEmpty e
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecLit :: m (SomeExpr ext s)
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

    vecCons :: m (SomeExpr ext s)
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

    vecGet :: m (SomeExpr ext s)
    vecGet =
      do let newhint = case typeHint of
                         Just (Some t) -> Just (Some (VectorRepr t))
                         _ -> Nothing
         (Pair t e, n) <-
            binary VectorGetEntry_ (forceSynth =<< synthExpr newhint) (check NatRepr)
         case t of
           VectorRepr elemT -> return $ SomeE elemT $ EApp $ VectorGetEntry elemT e n
           other -> later $ describe ("vector (found " <> T.pack (show other) <> ")") empty

    vecSet :: m (SomeExpr ext s)
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

    struct :: m (SomeExpr ext s)
    struct = describe "struct literal" $ followedBy (kw MkStruct_) (commit *>
      do ls <- case typeHint of
                  Just (Some (StructRepr ctx)) ->
                     list (toListFC (\t -> forceSynth =<< synthExpr (Just (Some t))) ctx)
                  Just (Some t) -> later $ describe ("value of type " <> T.pack (show t) <> " but got struct") empty
                  Nothing -> rep (forceSynth =<< synthExpr Nothing)
         pure $! buildStruct ls)

    getField :: m (SomeExpr ext s)
    getField =
      describe "struct field projection" $
      followedBy (kw GetField_) (commit *>
      depCons int (\n ->
      depCons synth (\(Pair t e) ->
         case t of
           StructRepr ts ->
             case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
               Nothing ->
                 describe (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)) empty
               Just (Some idx) ->
                 do let ty = ts ^. ixF' idx
                    return $ SomeE ty $ EApp $ GetStruct e idx ty
           _ -> describe ("struct type (got " <> T.pack (show t) <> ")") empty)))

    setField :: m (SomeExpr ext s)
    setField = describe "update to a struct type" $
      followedBy (kw SetField_) (commit *>
      depConsCond (forceSynth =<< synthExpr typeHint) (\ (Pair tp e) ->
        case tp of
          StructRepr ts -> Right <$>
            depConsCond int (\n ->
              case Ctx.intIndex (fromInteger n) (Ctx.size ts) of
                Nothing -> pure (Left (T.pack (show n) <> " is an invalid index into " <> T.pack (show ts)))
                Just (Some idx) -> Right <$>
                  do let ty = ts ^. ixF' idx
                     (v,()) <- cons (check ty) emptyList
                     pure $ SomeE (StructRepr ts) $ EApp $ SetStruct ts e idx v)
          _ -> pure $ Left $ ("struct type, but got " <> T.pack (show tp))))

    seqNil :: m (SomeExpr ext s)
    seqNil =
      do Some t <- unary SequenceNil_ isType
         return $ SomeE (SequenceRepr t) $ EApp $ SequenceNil t
      <|>
      kw SequenceNil_ *>
      case typeHint of
        Just (Some (SequenceRepr t)) ->
          return $ SomeE (SequenceRepr t) $ EApp $ SequenceNil t
        Just (Some t) ->
          later $ describe ("value of type " <> T.pack (show t)) empty
        Nothing ->
          later $ describe ("unambiguous nil value") empty

    seqCons :: m (SomeExpr ext s)
    seqCons =
      do let newhint = case typeHint of
                         Just (Some (SequenceRepr t)) -> Just (Some t)
                         _ -> Nothing
         (a, d) <- binary SequenceCons_ (later (synthExpr newhint)) (later (synthExpr typeHint))
         let g Nothing = Nothing
             g (Just (Some t)) = Just (Some (SequenceRepr t))
         case join (find isJust [ typeHint, g (someExprType a), someExprType d ]) of
           Just (Some (SequenceRepr t)) ->
             SomeE (SequenceRepr t) . EApp <$> (SequenceCons t <$> evalSomeExpr t a <*> evalSomeExpr (SequenceRepr t) d)
           _ -> later $ describe "unambiguous sequence cons (add a type ascription to disambiguate)" empty

    seqAppend :: m (SomeExpr ext s)
    seqAppend =
      do (x, y) <- binary SequenceAppend_ (later (synthExpr typeHint)) (later (synthExpr typeHint))
         case join (find isJust [ typeHint, someExprType x, someExprType y ]) of
           Just (Some (SequenceRepr t)) ->
             SomeE (SequenceRepr t) . EApp <$>
               (SequenceAppend t <$> evalSomeExpr (SequenceRepr t) x <*> evalSomeExpr (SequenceRepr t) y)
           _ -> later $ describe "unambiguous sequence append (add a type ascription to disambiguate)" empty

    seqNilP :: m (SomeExpr ext s)
    seqNilP =
      do Pair t e <- unary SequenceIsNil_ synth
         case t of
           SequenceRepr t' -> return $ SomeE BoolRepr $ EApp $ SequenceIsNil t' e
           other -> later $ describe ("sequence (found " <> T.pack (show other) <> ")") empty

    seqLen :: m (SomeExpr ext s)
    seqLen =
      do Pair t e <- unary SequenceLength_ synth
         case t of
           SequenceRepr t' -> return $ SomeE NatRepr $ EApp $ SequenceLength t' e
           other -> later $ describe ("sequence (found " <> T.pack (show other) <> ")") empty

    seqHead :: m (SomeExpr ext s)
    seqHead =
      do let newhint = case typeHint of
                         Just (Some (MaybeRepr t)) -> Just (Some (SequenceRepr t))
                         _ -> Nothing
         (Pair t e) <-
            unary SequenceHead_ (forceSynth =<< synthExpr newhint)
         case t of
           SequenceRepr elemT -> return $ SomeE (MaybeRepr elemT) $ EApp $ SequenceHead elemT e
           other -> later $ describe ("sequence (found " <> T.pack (show other) <> ")") empty

    seqTail :: m (SomeExpr ext s)
    seqTail =
      do let newhint = case typeHint of
                         Just (Some (MaybeRepr t)) -> Just (Some t)
                         _ -> Nothing
         (Pair t e) <-
            unary SequenceTail_ (forceSynth =<< synthExpr newhint)
         case t of
           SequenceRepr elemT -> return $ SomeE (MaybeRepr (SequenceRepr elemT)) $ EApp $ SequenceTail elemT e
           other -> later $ describe ("sequence (found " <> T.pack (show other) <> ")") empty

    seqUncons :: m (SomeExpr ext s)
    seqUncons =
      do let newhint = case typeHint of
                         Just (Some (MaybeRepr (StructRepr (Ctx.Empty Ctx.:> t Ctx.:> _)))) ->
                           Just (Some (SequenceRepr t))
                         _ -> Nothing
         (Pair t e) <-
            unary SequenceUncons_ (forceSynth =<< synthExpr newhint)
         case t of
           SequenceRepr elemT ->
             return $ SomeE (MaybeRepr (StructRepr (Ctx.Empty Ctx.:> elemT Ctx.:> SequenceRepr elemT))) $
               EApp $ SequenceUncons elemT e
           other -> later $ describe ("sequence (found " <> T.pack (show other) <> ")") empty

    showExpr :: m (SomeExpr ext s)
    showExpr =
      do Pair t1 e <- unary Show synth
         case t1 of
           FloatRepr fi ->
             return $ SomeE (StringRepr UnicodeRepr) $ EApp $ ShowFloat fi e
           NatRepr ->
             let toint = EApp $ NatToInteger e
                 showint = EApp $ ShowValue BaseIntegerRepr toint
             in return $ SomeE (StringRepr UnicodeRepr) showint
           (asBaseType -> AsBaseType bt) ->
             return $ SomeE (StringRepr UnicodeRepr) $ EApp $ ShowValue bt e
           _ -> later $ describe ("base or floating point type, but got " <> T.pack (show t1)) empty


buildStruct :: [Pair TypeRepr (E ext s)] -> SomeExpr ext s
buildStruct = loop Ctx.Empty Ctx.Empty
  where
    loop :: Ctx.Assignment TypeRepr ctx -> Ctx.Assignment (E ext s) ctx -> [Pair TypeRepr (E ext s)] -> SomeExpr ext s
    loop tps vs [] = SomeE (StructRepr tps) (EApp (MkStruct tps vs))
    loop tps vs (Pair tp x:xs) = loop (tps Ctx.:> tp) (vs Ctx.:> x) xs

data NatHint
  = NoHint
  | forall w. (1 <= w) => NatHint (NatRepr w)

synthBV :: forall m s ext.
  ( MonadReader (SyntaxState s) m
  , MonadSyntax Atomic m
  , ?parserHooks :: ParserHooks ext ) =>
  NatHint ->
  m (SomeBVExpr ext s)
synthBV widthHint =
   bvLit <|> bvConcat <|> bvSelect <|> bvTrunc <|>
   bvZext <|> bvSext <|> boolToBV <|>
   naryBV BVAnd_ BVAnd 1 <|> naryBV BVOr_ BVOr 0 <|> naryBV BVXor_ BVXor 0 <|>
   binaryBV Sdiv BVSdiv <|> binaryBV Smod BVSrem <|>
   binaryBV BVShl_ BVShl <|> binaryBV BVLshr_ BVLshr <|> binaryBV BVAshr_ BVAshr <|>
   unaryBV Negate BVNeg <|> unaryBV BVNot_ BVNot

 where
    bvSubterm :: NatHint -> m (SomeBVExpr ext s)
    bvSubterm hint =
      do let newhint = case hint of
                         NatHint w -> Just (Some (BVRepr w))
                         _ -> Nothing
         (Pair t x) <- forceSynth =<< synthExpr newhint
         case t of
           BVRepr w -> return (SomeBVExpr w x)
           _ -> later $ describe "bitvector expression" $ empty

    bvLit :: m (SomeBVExpr ext s)
    bvLit =
      describe "bitvector literal" $
      do (BoundedNat w, i) <- binary BV posNat int
         return $ SomeBVExpr w $ EApp $ BVLit w (BV.mkBV w i)

    unaryBV :: Keyword
          -> (forall w. (1 <= w) => NatRepr w -> E ext s (BVType w) -> App ext (E ext s) (BVType w))
          -> m (SomeBVExpr ext s)
    unaryBV k f =
      do SomeBVExpr wx x <- unary k (bvSubterm widthHint)
         return $ SomeBVExpr wx $ EApp $ f wx x

    binaryBV :: Keyword
          -> (forall w. (1 <= w) => NatRepr w -> E ext s (BVType w) -> E ext s (BVType w) -> App ext (E ext s) (BVType w))
          -> m (SomeBVExpr ext s)
    binaryBV k f =
      do (SomeBVExpr wx x, SomeBVExpr wy y) <- binary k (bvSubterm widthHint) (bvSubterm widthHint)
         case testEquality wx wy of
           Just Refl -> return $ SomeBVExpr wx $ EApp $ f wx x y
           Nothing -> later $
             describe ("bitwise expression arguments with matching widths (" <>
                       T.pack (show wx) <> " /= " <> T.pack (show wy) <> ")")
                      empty

    naryBV :: Keyword
          -> (forall w. (1 <= w) => NatRepr w -> E ext s (BVType w) -> E ext s (BVType w) -> App ext (E ext s) (BVType w))
          -> Integer
          -> m (SomeBVExpr ext s)
    naryBV k f u =
      do args <- kw k `followedBy` rep (later (bvSubterm widthHint))
         case args of
           [] -> case widthHint of
                   NoHint    -> later $ describe "ambiguous width" empty
                   NatHint w -> return $ SomeBVExpr w $ EApp $ BVLit w (BV.mkBV w u)
           (SomeBVExpr wx x:xs) -> SomeBVExpr wx <$> go wx x xs

     where
     go :: forall w. NatRepr w -> E ext s (BVType w) -> [SomeBVExpr ext s] -> m (E ext s (BVType w))
     go _wx x [] = return x
     go wx x (SomeBVExpr wy y : ys) =
       case testEquality wx wy of
         Just Refl -> go wx (EApp $ f wx x y) ys
         Nothing   -> later $
              describe ("bitwise expression arguments with matching widths (" <>
                        T.pack (show wx) <> " /= " <> T.pack (show wy) <> ")")
                       empty

    boolToBV :: m (SomeBVExpr ext s)
    boolToBV =
      do (BoundedNat w, x) <- binary BoolToBV_ posNat (check BoolRepr)
         return $ SomeBVExpr w $ EApp $ BoolToBV w x

    bvSelect :: m (SomeBVExpr ext s)
    bvSelect =
      do (Some idx, (BoundedNat len, (SomeBVExpr w x, ()))) <-
             followedBy (kw BVSelect_) (commit *> cons natRepr (cons posNat (cons (bvSubterm NoHint) emptyList)))
         case testLeq (addNat idx len) w of
           Just LeqProof -> return $ SomeBVExpr len $ EApp $ BVSelect idx len w x
           _ -> later $ describe ("valid bitvector select") $ empty

    bvConcat :: m (SomeBVExpr ext s)
    bvConcat =
      do (SomeBVExpr wx x, SomeBVExpr wy y) <- binary BVConcat_ (bvSubterm NoHint) (bvSubterm NoHint)
         withLeqProof (leqAdd (leqProof (knownNat @1) wx) wy) $
           return $ SomeBVExpr (addNat wx wy) (EApp $ BVConcat wx wy x y)

    bvTrunc :: m (SomeBVExpr ext s)
    bvTrunc =
      do (BoundedNat r, SomeBVExpr w x) <- binary BVTrunc_ posNat (bvSubterm NoHint)
         case testLeq (incNat r) w of
           Just LeqProof -> return $ SomeBVExpr r (EApp $ BVTrunc r w x)
           _ -> later $ describe "valid bitvector truncation" $ empty

    bvZext :: m (SomeBVExpr ext s)
    bvZext =
      do (BoundedNat r, SomeBVExpr w x) <- binary BVZext_ posNat (bvSubterm NoHint)
         case testLeq (incNat w) r of
           Just LeqProof -> return $ SomeBVExpr r (EApp $ BVZext r w x)
           _ -> later $ describe "valid zero extension" $ empty

    bvSext :: m (SomeBVExpr ext s)
    bvSext =
      do (BoundedNat r, SomeBVExpr w x) <- binary BVSext_ posNat (bvSubterm NoHint)
         case testLeq (incNat w) r of
           Just LeqProof -> return $ SomeBVExpr r (EApp $ BVSext r w x)
           _ -> later $ describe "valid zero extension" $ empty


check :: forall m t s ext
       . ( MonadReader (SyntaxState s) m
         , MonadSyntax Atomic m
         , ?parserHooks :: ParserHooks ext )
       => TypeRepr t -> m (E ext s t)
check t =
  describe ("inhabitant of " <> T.pack (show t)) $
    do Pair t' e <- forceSynth =<< synthExpr (Just (Some t))
       later $ describe ("a " <> T.pack (show t) <> " rather than a " <> T.pack (show t')) $
         case testEquality t t' of
           Nothing -> later empty
           Just Refl -> return e

-------------------------------------------------------------------------

data LabelInfo :: Type -> Type where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . LambdaLabel s ty -> LabelInfo s

data ProgramState s =
  ProgramState { _progFunctions :: Map FunctionName FunctionHeader
               , _progForwardDecs :: Map FunctionName FunctionHeader
               , _progGlobals :: Map GlobalName (Some GlobalVar)
               , _progExterns :: Map GlobalName (Some GlobalVar)
               , _progHandleAlloc :: HandleAllocator
               }

progFunctions :: Simple Lens (ProgramState s) (Map FunctionName FunctionHeader)
progFunctions = lens _progFunctions (\s v -> s { _progFunctions = v })

progForwardDecs :: Simple Lens (ProgramState s) (Map FunctionName FunctionHeader)
progForwardDecs = lens _progForwardDecs (\s v -> s { _progForwardDecs = v })

progGlobals :: Simple Lens (ProgramState s) (Map GlobalName (Some GlobalVar))
progGlobals = lens _progGlobals (\s v -> s { _progGlobals = v })

progExterns :: Simple Lens (ProgramState s) (Map GlobalName (Some GlobalVar))
progExterns = lens _progExterns (\s v -> s { _progExterns = v })

progHandleAlloc :: Simple Lens (ProgramState s) HandleAllocator
progHandleAlloc = lens _progHandleAlloc (\s v -> s { _progHandleAlloc = v })


data SyntaxState s =
  SyntaxState { _stxLabels :: Map LabelName (LabelInfo s)
              , _stxAtoms :: Map AtomName (Some (Atom s))
              , _stxRegisters :: Map RegName (Some (Reg s))
              , _stxNonceGen :: NonceGenerator IO s
              , _stxProgState :: ProgramState s
              }

initProgState :: [(SomeHandle,Position)] -> HandleAllocator -> ProgramState s
initProgState builtIns ha = ProgramState fns Map.empty Map.empty Map.empty ha
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
        ]

initSyntaxState :: NonceGenerator IO s -> ProgramState s -> SyntaxState s
initSyntaxState =
  SyntaxState Map.empty Map.empty Map.empty

stxLabels :: Simple Lens (SyntaxState s) (Map LabelName (LabelInfo s))
stxLabels = lens _stxLabels (\s v -> s { _stxLabels = v })

stxAtoms :: Simple Lens (SyntaxState s) (Map AtomName (Some (Atom s)))
stxAtoms = lens _stxAtoms (\s v -> s { _stxAtoms = v })

stxRegisters :: Simple Lens (SyntaxState s) (Map RegName (Some (Reg s)))
stxRegisters = lens _stxRegisters (\s v -> s { _stxRegisters = v })

stxNonceGen :: Getter (SyntaxState s) (NonceGenerator IO s)
stxNonceGen = to _stxNonceGen

stxProgState :: Simple Lens (SyntaxState s) (ProgramState s)
stxProgState = lens _stxProgState (\s v -> s { _stxProgState = v })

stxFunctions :: Simple Lens (SyntaxState s) (Map FunctionName FunctionHeader)
stxFunctions = stxProgState . progFunctions

stxForwardDecs :: Simple Lens (SyntaxState s) (Map FunctionName FunctionHeader)
stxForwardDecs = stxProgState . progForwardDecs

stxGlobals :: Simple Lens (SyntaxState s) (Map GlobalName (Some GlobalVar))
stxGlobals = stxProgState . progGlobals

stxExterns :: Simple Lens (SyntaxState s) (Map GlobalName (Some GlobalVar))
stxExterns = stxProgState . progExterns

newtype CFGParser s ret a =
  CFGParser { runCFGParser :: (?returnType :: TypeRepr ret)
                           => ExceptT (ExprErr s)
                                (StateT (SyntaxState s) IO)
                                a
            }
  deriving (Functor)

instance Applicative (CFGParser s ret) where
  pure x = CFGParser (pure x)
  (CFGParser f) <*> (CFGParser x) = CFGParser (f <*> x)

instance Alternative (CFGParser s ret) where
  empty = CFGParser $ throwError $ TrivialErr InternalPos
  (CFGParser x) <|> (CFGParser y) = CFGParser (x <|> y)

instance Semigroup (CFGParser s ret a) where
  (<>) = (<|>)

instance Monoid (CFGParser s ret a) where
  mempty = empty

instance Monad (CFGParser s ret) where
  (CFGParser m) >>= f = CFGParser $ m >>= \a -> runCFGParser (f a)

instance MonadError (ExprErr s) (CFGParser s ret) where
  throwError e = CFGParser $ throwError e
  catchError m h = CFGParser $ catchError (runCFGParser m) (\e -> runCFGParser $ h e)

instance MonadState (SyntaxState s) (CFGParser s ret) where
  get = CFGParser get
  put s = CFGParser $ put s

instance MonadIO (CFGParser s ret) where
  liftIO io = CFGParser $ lift $ lift io


freshId :: (MonadState (SyntaxState s) m, MonadIO m) => m (Nonce s tp)
freshId =
  do ng <- use stxNonceGen
     liftIO $ freshNonce ng

freshLabel :: (MonadState (SyntaxState s) m, MonadIO m) => m (Label s)
freshLabel = Label <$> freshId

freshAtom :: ( MonadWriter [Posd (Stmt ext s)] m
             , MonadState (SyntaxState s) m
             , MonadIO m
             , IsSyntaxExtension ext )
          => Position -> AtomValue ext s t -> m (Atom s t)
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



newLabel :: (MonadState (SyntaxState s) m, MonadIO m) => LabelName -> m (Label s)
newLabel x =
  do theLbl <- freshLabel
     stxLabels %= Map.insert x (NoArgLbl theLbl)
     return theLbl

freshLambdaLabel :: (MonadState (SyntaxState s) m, MonadIO m) => TypeRepr tp -> m (LambdaLabel s tp, Atom s tp)
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


lambdaLabelBinding :: ( MonadSyntax Atomic m
                      , MonadState (SyntaxState s) m
                      , MonadIO m
                      , ?parserHooks :: ParserHooks ext )
                   => m (LabelName, Some (LambdaLabel s))
lambdaLabelBinding =
  call $
  depCons uniqueLabel $
  \l ->
    depCons uniqueAtom $
    \x ->
      depCons isType $
      \(Some t) ->
        do (lbl, anAtom) <- freshLambdaLabel t
           stxLabels %= Map.insert l (ArgLbl lbl)
           stxAtoms %= Map.insert x (Some anAtom)
           return (l, Some lbl)

  where uniqueLabel =
          do labels <- use stxLabels
             sideCondition "unique label"
               (\l -> case Map.lookup l labels of
                        Nothing -> Just l
                        Just _ -> Nothing)
               labelName


uniqueAtom :: (MonadSyntax Atomic m, MonadState (SyntaxState s) m) => m AtomName
uniqueAtom =
  do atoms <- use stxAtoms
     sideCondition "unique Crucible atom"
       (\x -> case Map.lookup x atoms of
                Nothing -> Just x
                Just _ -> Nothing)
       atomName

newUnassignedReg :: (MonadState (SyntaxState s) m, MonadIO m) => TypeRepr t -> m (Reg s t)
newUnassignedReg t =
  do i <- freshId
     let fakePos = OtherPos "Parser internals"
     return $! Reg { regPosition = fakePos
                   , regId = i
                   , typeOfReg = t
                   }

regRef' :: (MonadSyntax Atomic m, MonadReader (SyntaxState s) m) => m (Some (Reg s))
regRef' =
  describe "known register name" $
  do rn <- regName
     perhapsReg <- view (stxRegisters . at rn)
     case perhapsReg of
       Just reg -> return reg
       Nothing -> empty

globRef' :: (MonadSyntax Atomic m, MonadReader (SyntaxState s) m) => m (Some GlobalVar)
globRef' =
  describe "known global variable name" $
  do x <- globalName
     perhapsGlobal <- view (stxGlobals . at x)
     perhapsExtern <- view (stxExterns . at x)
     case perhapsGlobal <|> perhapsExtern of
       Just glob -> return glob
       Nothing -> empty



reading :: MonadState r m => ReaderT r m b -> m b
reading m = get >>= runReaderT m

--------------------------------------------------------------------------

atomSetter :: forall m ext s
            . ( MonadSyntax Atomic m
              , MonadWriter [Posd (Stmt ext s)] m
              , MonadState (SyntaxState s) m
              , MonadIO m
              , IsSyntaxExtension ext
              , ?parserHooks :: ParserHooks ext )
           => AtomName -- ^ The name of the atom being set, used for fresh name internals
           -> m (Some (Atom s))
atomSetter (AtomName anText) =
  call ( newref
     <|> emptyref
     <|> fresh
     <|> funcall
     <|> evaluated
     <|> (extensionParser ?parserHooks) )
  where
    fresh, emptyref, newref
      :: ( MonadSyntax Atomic m
         , MonadWriter [Posd (Stmt ext s)] m
         , MonadState (SyntaxState s) m
         , MonadIO m
         , IsSyntaxExtension ext
         )
      => m (Some (Atom s))

    newref =
      do Pair _ e <- reading $ unary Ref synth
         loc <- position
         anAtom <- eval loc e
         anotherAtom <- freshAtom loc (NewRef anAtom)
         return $ Some anotherAtom

    emptyref =
      do Some t' <- reading $ unary EmptyRef isType
         loc <- position
         anAtom <- freshAtom loc (NewEmptyRef t')
         return $ Some anAtom

    fresh =
      do t <- reading (unary Fresh isType)
         -- Note that we are using safeSymbol below to create a What4 symbol
         -- name, which will Z-encode names that aren't legal solver names. This
         -- includes names that include hyphens, which are very common in
         -- S-expression syntax. This is fine to do, since the Z-encoded name
         -- name is only used for solver purposes; the original, unencoded name
         -- is recorded separately.
         let nm = safeSymbol (T.unpack anText)
         loc <- position
         case t of
           Some (FloatRepr fi) ->
             Some <$>
               freshAtom loc (FreshFloat fi (Just nm))
           Some NatRepr ->
             Some <$> freshAtom loc (FreshNat (Just nm))
           Some tp
             | AsBaseType bt <- asBaseType tp ->
                 Some <$> freshAtom loc (FreshConstant bt (Just nm))
             | otherwise -> describe "atomic type" $ empty

    evaluated =
       do Pair _ e' <- reading synth
          loc <- position
          anAtom <- eval loc e'
          return $ Some anAtom

-- | Parse a list of operands (for example, the arguments to a function)
operands :: forall s ext m tps
          . ( MonadState (SyntaxState s) m
            , MonadWriter [Posd (Stmt ext s)] m
            , MonadIO m
            , MonadSyntax Atomic m
            , IsSyntaxExtension ext
            , ?parserHooks :: ParserHooks ext )
            -- ParserHooks to use for syntax extensions
         => Ctx.Assignment TypeRepr tps
         -- ^ Types of the operands
         -> m (Ctx.Assignment (Atom s) tps)
         -- ^ Atoms for the operands
operands args = do
  operandExprs <- backwards $ go $ Ctx.viewAssign args
  traverseFC (\(Rand a ex) -> eval (syntaxPos a) ex) operandExprs
  where
    go :: (MonadState (SyntaxState s) m, MonadSyntax Atomic m)
       => Ctx.AssignView TypeRepr args
       -> m (Ctx.Assignment (Rand ext s) args)
    go Ctx.AssignEmpty = emptyList *> pure Ctx.empty
    go (Ctx.AssignExtend ctx' ty) =
      depCons (reading $ check ty) $ \e ->
        do rest <- go (Ctx.viewAssign ctx')
           this <- anything
           return $ Ctx.extend rest $ Rand this e

funcall
  :: forall ext s m
   . ( MonadSyntax Atomic m
     , MonadWriter [Posd (Stmt ext s)] m
     , MonadState (SyntaxState s) m
     , MonadIO m
     , IsSyntaxExtension ext
     , ?parserHooks :: ParserHooks ext
     )
  => m (Some (Atom s))
funcall =
  followedBy (kw Funcall) $
  depConsCond (reading synth) $
    \x ->
      case x of
        (Pair (FunctionHandleRepr funArgs ret) fun) ->
          do loc <- position
             funAtom <- eval loc fun
             operandAtoms <- operands funArgs
             endAtom <- freshAtom loc $ Call funAtom operandAtoms ret
             return $ Right $ Some endAtom
        _ -> return $ Left "a function"


located :: MonadSyntax atom m => m a -> m (Posd a)
located p = Posd <$> position <*> p

normStmt' :: forall s m ext
           . ( MonadWriter [Posd (Stmt ext s)] m
             , MonadSyntax Atomic m
             , MonadState (SyntaxState s) m
             , MonadIO m
             , IsSyntaxExtension ext
             , ?parserHooks :: ParserHooks ext) =>
             m ()
normStmt' =
  call (printStmt <|> printLnStmt <|> letStmt <|> (void funcall) <|>
        setGlobal <|> setReg <|> setRef <|> dropRef <|>
        assertion <|> assumption <|> breakpoint <|>
        (void (extensionParser ?parserHooks)))

  where
    printStmt, printLnStmt, letStmt, setGlobal, setReg, setRef, dropRef, assertion, breakpoint :: m ()
    printStmt =
      do Posd loc e <- unary Print_ (located $ reading $ check (StringRepr UnicodeRepr))
         strAtom <- eval loc e
         tell [Posd loc (Print strAtom)]

    printLnStmt =
      do Posd loc e <- unary PrintLn_ (located $ reading $ check (StringRepr UnicodeRepr))
         strAtom <- eval loc (EApp (StringConcat UnicodeRepr e (EApp (StringLit "\n"))))
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
              Just (Some var) ->
                do (Posd loc e) <- fst <$> cons (located $ reading $ check $ globalType var) emptyList
                   a <- eval loc e
                   tell [Posd loc $ WriteGlobal var a]
                   return (Right ())

    setReg =
      followedBy (kw SetRegister) $
      depCons (reading regRef') $
      \(Some r) ->
        depCons (reading $ located $ check $ typeOfReg r) $
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
             (located $ reading $ check (StringRepr UnicodeRepr))
         cond' <- eval cLoc cond
         msg' <- eval mLoc msg
         tell [Posd loc $ Assert cond' msg']

    assumption =
      do (Posd loc (Posd cLoc cond, Posd mLoc msg)) <-
           located $
           binary Assume_
             (located $ reading $ check BoolRepr)
             (located $ reading $ check (StringRepr UnicodeRepr))
         cond' <- eval cLoc cond
         msg' <- eval mLoc msg
         tell [Posd loc $ Assume cond' msg']

    breakpoint =
      do (Posd loc (nm, arg_list)) <-
           located $ binary Breakpoint_
             (string <&> BreakpointName)
             (rep ra_value)
         case toCtx arg_list of
           Some args -> tell [Posd loc $ Breakpoint nm args]
      where
        ra_value :: m (Some (Value s))
        ra_value = (reading synth) >>= \case
          Pair _ (EReg _ reg) -> pure $ Some $ RegValue reg
          Pair _ (EAtom atm) -> pure $ Some $ AtomValue atm
          _ -> empty


blockBody' :: forall s ret m ext
            . ( MonadSyntax Atomic m
              , MonadState (SyntaxState s) m
              , MonadIO m
              , IsSyntaxExtension ext
              , ?parserHooks :: ParserHooks ext )
           => TypeRepr ret
           -> m (Posd (TermStmt s ret), [Posd (Stmt ext s)])
blockBody' ret = runWriterT go
 where
 go :: WriterT [Posd (Stmt ext s)] m (Posd (TermStmt s ret))
 go = (fst <$> (cons (later (termStmt' ret)) emptyList)) <|>
      (snd <$> (cons (later normStmt') go))

termStmt' :: forall m s ret ext.
   ( MonadWriter [Posd (Stmt ext s)] m
   , MonadSyntax Atomic m
   , MonadState (SyntaxState s) m
   , MonadIO m
   , IsSyntaxExtension ext
   , ?parserHooks :: ParserHooks ext ) =>
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
             Just (ArgLbl _) -> empty
             Just (NoArgLbl lbl) -> pure lbl

    lambdaLabel :: m (Some (LambdaLabel s))
    lambdaLabel =
      do x <- labelName
         l <- use (stxLabels . at x)
         later $ describe "known label with an argument" $
           case l of
             Nothing -> empty
             Just (ArgLbl lbl) -> pure $ Some lbl
             Just (NoArgLbl _) -> empty

    typedLambdaLabel :: TypeRepr t -> m (LambdaLabel s t)
    typedLambdaLabel t =
      do x <- labelName
         l <- use (stxLabels . at x)
         later $ describe ("known label with an " <> T.pack (show t) <> " argument") $
           case l of
             Nothing -> empty
             Just (ArgLbl lbl) ->
               case testEquality (typeOfAtom (lambdaAtom lbl)) t of
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
      do Posd loc e <- unary Error_ (located (reading (check (StringRepr UnicodeRepr))))
         ErrorStmt <$> eval loc e

    out :: m (TermStmt s ret)
    out = followedBy (kw Output_) $
          do -- commit
             depCons lambdaLabel $
               \(Some lbl) ->
                 depCons (located (reading (check (typeOfAtom (lambdaAtom lbl))))) $
                   \(Posd loc arg) ->
                     emptyList *>
                       (Output lbl <$> eval loc arg)



data Rand ext s t = Rand (AST s) (E ext s t)




--------------------------------------------------------------------------

data Arg t = Arg AtomName Position (TypeRepr t)

someAssign ::
  forall m ext a.
  ( MonadSyntax Atomic m
  , ?parserHooks :: ParserHooks ext
  ) =>
  Text ->
  m (Some a) ->
  m (Some (Ctx.Assignment a))
someAssign desc sub = call (go (Some Ctx.empty))
  where
    go :: Some (Ctx.Assignment a) -> m (Some (Ctx.Assignment a))
    go args@(Some prev) =
      describe desc $
        (emptyList *> pure args) <|>
        (depCons sub $
           \(Some a) ->
             go (Some $ Ctx.extend prev a))

arguments' :: forall m ext
            . ( MonadSyntax Atomic m, ?parserHooks :: ParserHooks ext )
           => m (Some (Ctx.Assignment Arg))
arguments' = someAssign "argument list" oneArg
  where oneArg =
          (describe "argument" $
           located $
           cons atomName (cons isType emptyList)) <&>
          \(Posd loc (x, (Some t, ()))) -> Some (Arg x loc t)


saveArgs :: (MonadState (SyntaxState s) m, MonadError (ExprErr s) m)
         => Ctx.Assignment Arg init
         -> Ctx.Assignment (Atom s) init
         -> m ()
saveArgs ctx1 ctx2 =
  let combined = Ctx.zipWith
                   (\(Arg x p _) argAtom ->
                      (Const (Some (Functor.Pair (Const x) (Functor.Pair (Const p) argAtom)))))
                   ctx1 ctx2
  in forFC_ combined $
       \(Const (Some (Functor.Pair (Const x) (Functor.Pair (Const argPos) y)))) ->
         with (stxAtoms . at x) $
           \case
             Just _ -> throwError $ DuplicateAtom argPos x
             Nothing ->
               do stxAtoms %= Map.insert x (Some y)

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

functionHeader' :: ( MonadSyntax Atomic m, ?parserHooks :: ParserHooks ext )
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

functionHeader :: (?parserHooks :: ParserHooks ext)
               => AST s
               -> TopParser s (FunctionHeader, FunctionSource s)
functionHeader defun =
  do ((fnName, Some theArgs, Some ret, loc), src) <- liftSyntaxParse functionHeader' defun
     ha <- use $ stxProgState  . progHandleAlloc
     handle <- liftIO $ mkHandle' ha fnName (argTypes theArgs) ret
     let header = FunctionHeader fnName theArgs ret handle loc

     saveHeader fnName header
     return $ (header, src)
  where
    saveHeader n h =
      stxFunctions %= Map.insert n h




global :: (?parserHooks :: ParserHooks ext)
       => AST s
       -> TopParser s (Some GlobalVar)
global stx =
  do (var@(GlobalName varName), Some t) <- liftSyntaxParse (call (binary DefGlobal globalName isType)) stx
     ha <- use $ stxProgState  . progHandleAlloc
     v <- liftIO $ freshGlobalVar ha varName t
     let sv = Some v
     stxGlobals %= Map.insert var sv
     return sv

-- | Parse a forward declaration.
declare :: (?parserHooks :: ParserHooks ext)
        => AST t
        -> TopParser s FunctionHeader
declare stx =
  do ((fnName, (Some theArgs, (Some ret, ()))), loc) <-
       liftSyntaxParse (do r <- followedBy (kw Declare) $
                                cons funName $
                                cons arguments' $
                                cons isType emptyList
                           loc <- position
                           pure (r, loc))
                       stx
     ha <- use $ stxProgState . progHandleAlloc
     handle <- liftIO $ mkHandle' ha fnName (argTypes theArgs) ret

     let header = FunctionHeader fnName theArgs ret handle loc
     stxForwardDecs %= Map.insert fnName header
     pure header

-- | Parse an extern.
extern :: (?parserHooks :: ParserHooks ext)
       => AST s
       -> TopParser s (Some GlobalVar)
extern stx =
  do (var@(GlobalName varName), Some t) <- liftSyntaxParse (call (binary Extern globalName isType)) stx
     ha <- use $ stxProgState  . progHandleAlloc
     v <- liftIO $ freshGlobalVar ha varName t
     let sv = Some v
     stxExterns %= Map.insert var sv
     return sv

topLevel :: (?parserHooks :: ParserHooks ext)
         => AST s
         -> TopParser s (Maybe (FunctionHeader, FunctionSource s))
topLevel ast =
  case ast of
    L (A (Kw Defun):_) -> Just <$> functionHeader ast
    L (A (Kw Declare):_) -> declare ast $> Nothing
    L (A (Kw DefGlobal):_) -> global ast $> Nothing
    L (A (Kw Extern):_) -> extern ast $> Nothing
    _ -> do
     loc <- liftSyntaxParse position ast
     throwError (TrivialErr loc)

argTypes :: Ctx.Assignment Arg init -> Ctx.Assignment TypeRepr init
argTypes  = fmapFC (\(Arg _ _ t) -> t)


type BlockTodo s ret =
  (LabelName, BlockID s, Progress, AST s)

blocks :: forall s ret m ext
        . ( MonadState (SyntaxState s) m
          , MonadSyntax Atomic m
          , MonadIO m
          , TraverseExt ext
          , IsSyntaxExtension ext
          , ?parserHooks :: ParserHooks ext )
        => TypeRepr ret
        -> m [Block ext s ret]
blocks ret =
      depCons startBlock' $
      \ startContents ->
        do todo <- rep blockLabel'
           forM (startContents : todo) $ \(_, bid, pr, stmts) ->
             do (term, stmts') <- withProgress (const pr) $ parse stmts (call (blockBody' ret))
                pure $ mkBlock bid mempty (Seq.fromList stmts') term


  where

    startBlock' :: (MonadState (SyntaxState s) m, MonadSyntax Atomic m, MonadIO m) => m (BlockTodo s ret)
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

    blockLabel' :: m (BlockTodo s ret)
    blockLabel' =
      call $
      followedBy (kw DefBlock) $
      simpleBlock <|> argBlock
      where
        simpleBlock, argBlock :: m (BlockTodo s ret)
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
          depConsCond lambdaLabelBinding $
          \ (l, (Some lbl)) ->
            do pr <- progress
               body <- anything
               return $ Right (l, LambdaID lbl, pr, body)

eval :: (MonadWriter [Posd (Stmt ext s)] m, MonadState (SyntaxState s) m, MonadIO m, IsSyntaxExtension ext)
     => Position -> E ext s t -> m (Atom s t)
eval _   (EAtom theAtom)  = pure theAtom -- The expression is already evaluated
eval loc (EApp e)         = freshAtom loc . EvalApp =<< traverseFC (eval loc) e
eval _   (EReg loc reg)   = freshAtom loc (ReadReg reg)
eval _   (EGlob loc glob) = freshAtom loc (ReadGlobal glob)
eval loc (EDeref eloc e)  = freshAtom loc . ReadRef =<< eval eloc e

newtype TopParser s a =
  TopParser { runTopParser :: ExceptT (ExprErr s)
                                (StateT (SyntaxState s) IO)
                                a
            }
  deriving (Functor)

top :: NonceGenerator IO s -> HandleAllocator -> [(SomeHandle,Position)] -> TopParser s a -> IO (Either (ExprErr s) a)
top ng ha builtIns (TopParser (ExceptT (StateT act))) =
  fst <$> act (initSyntaxState ng (initProgState builtIns ha))

instance Applicative (TopParser s) where
  pure x = TopParser (pure x)
  (TopParser f) <*> (TopParser x) = TopParser (f <*> x)

instance Alternative (TopParser s) where
  empty = TopParser $ throwError (TrivialErr InternalPos)
  (TopParser x) <|> (TopParser y) = TopParser (x <|> y)

instance MonadPlus (TopParser s) where
  mzero = empty
  mplus = (<|>)

instance Semigroup (TopParser s a) where
  (<>) = (<|>)

instance Monoid (TopParser s a) where
  mempty = empty

instance Monad (TopParser s) where
  (TopParser m) >>= f = TopParser $ m >>= runTopParser . f

instance MonadError (ExprErr s) (TopParser s) where
  throwError = TopParser . throwError
  catchError m h = TopParser $ catchError (runTopParser m) (runTopParser . h)

instance MonadState (SyntaxState s) (TopParser s) where
  get = TopParser get
  put = TopParser . put

instance MonadIO (TopParser s) where
  liftIO = TopParser . lift . lift


initParser :: forall s m ext
            . ( MonadState (SyntaxState s) m
              , MonadError (ExprErr s) m
              , MonadIO m
              , ?parserHooks :: ParserHooks ext )
           => FunctionHeader
           -> FunctionSource s
           -> m ()
initParser (FunctionHeader _ (funArgs :: Ctx.Assignment Arg init) _ _ _) (FunctionSource regs _) =
  do ng <- use stxNonceGen
     progState <- use stxProgState
     put $ initSyntaxState ng progState
     let types = argTypes funArgs
     inputAtoms <- liftIO $ mkInputAtoms ng (OtherPos "args") types
     saveArgs funArgs inputAtoms
     forM_ regs saveRegister

  where
    saveRegister :: Syntax Atomic -> m ()
    saveRegister (L [A (Rg x), t]) =
      do Some ty <- liftSyntaxParse isType t
         r <- newUnassignedReg ty
         stxRegisters %= Map.insert x (Some r)
    saveRegister other = throwError $ InvalidRegister (syntaxPos other) other

cfgs :: ( IsSyntaxExtension ext
        , ?parserHooks :: ParserHooks ext )
     => [AST s]
     -> TopParser s [AnyCFG ext]
cfgs = fmap parsedProgCFGs <$> prog

prog :: ( TraverseExt ext
        , IsSyntaxExtension ext
        , ?parserHooks :: ParserHooks ext )
     => [AST s]
     -> TopParser s (ParsedProgram ext)
prog defuns =
  do headers <- catMaybes <$> traverse topLevel defuns
     cs <- forM headers $
       \(hdr@(FunctionHeader _ _ ret handle _), src@(FunctionSource _ body)) ->
         do initParser hdr src
            args <- toList <$> use stxAtoms
            let ?returnType = ret
            st <- get
            (theBlocks, st') <- liftSyntaxParse (runStateT (blocks ret) st) body
            put st'
            let vs = Set.fromList [ Some (AtomValue a) | Some a <- args ]
            case theBlocks of
              []       -> error "found no blocks"
              (e:rest) ->
                do let entry = case blockID e of
                                 LabelID lbl -> lbl
                                 LambdaID {} -> error "initial block is lambda"
                       e' = mkBlock (blockID e) vs (blockStmts e) (blockTerm e)
                   return $ AnyCFG (CFG handle entry (e' : rest))
     gs <- use stxGlobals
     externs <- use stxExterns
     fds <- uses stxForwardDecs $ fmap $
              \(FunctionHeader _ _ _ handle _) -> SomeHandle handle
     return $ ParsedProgram
       { parsedProgGlobals = gs
       , parsedProgExterns = externs
       , parsedProgCFGs = cs
       , parsedProgForwardDecs = fds
       }
