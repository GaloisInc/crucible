{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.Syntax.Parser
  ( -- * Errors
    ExprErr(..)

  -- * Parser Monad
  , Parser(..)
  , runParser
  , top

  -- * Parser State
  , LabelInfo(..)
  , ProgramState(..)
  , SyntaxState(..)
  , initProgState
  , initSyntaxState

  -- * Function Types
  , Arg(..)
  , FunctionHeader(..)
  , FunctionSource(..)

  -- * State Lenses
  , progFunctions
  , progForwardDecs
  , progGlobals
  , progExterns
  , progHandleAlloc
  , stxLabels
  , stxAtoms
  , stxRegisters
  , stxNonceGen
  , stxProgState
  , stxFunctions
  , stxForwardDecs
  , stxGlobals
  , stxExterns

  -- * Fresh Name Generation
  , freshId
  , freshLabel
  , newLabel
  , freshLambdaLabel
  , newUnassignedReg

  -- * Utilities
  , with
  )
where

import Control.Lens
import Control.Applicative
import Control.Monad (MonadPlus(..))
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State.Strict (MonadState(..), StateT(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Except (ExceptT(..))

import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Parameterized.Nonce ( NonceGenerator, Nonce, freshNonce )
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some(Some(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Prettyprinter as PP

import Lang.Crucible.Syntax.Atoms
import qualified Lang.Crucible.Syntax.ExprParse as SP
import Lang.Crucible.Syntax.Monad
import Lang.Crucible.Syntax.SExpr (Syntax)
import Lang.Crucible.Types

import Lang.Crucible.CFG.Reg
import Lang.Crucible.FunctionHandle

import What4.FunctionName
import What4.ProgramLoc

-------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------

type AST s = Syntax Atomic

data ExprErr s where
  TrivialErr :: Position -> ExprErr s
  Errs :: ExprErr s -> ExprErr s -> ExprErr s
  DuplicateAtom :: Position -> AtomName -> ExprErr s
  DuplicateLabel :: Position -> LabelName -> ExprErr s
  EmptyBlock :: Position -> ExprErr s
  NotGlobal :: Position -> AST s -> ExprErr s
  InvalidRegister :: Position -> AST s -> ExprErr s
  UnknownTopLevel :: Position -> AST s -> ExprErr s
  SyntaxParseError :: SP.SyntaxError Atomic -> ExprErr s

deriving instance Show (ExprErr s)

instance Semigroup (ExprErr s) where
  (<>) = Errs

instance Monoid (ExprErr s) where
  mempty = TrivialErr (OtherPos "mempty")

-- Note: PP.Pretty instance for ExprErr is in Concrete.hs to avoid circular dependency with printExpr

-------------------------------------------------------------------------
-- Label Info
-------------------------------------------------------------------------

data LabelInfo :: Type -> Type where
  NoArgLbl :: Label s -> LabelInfo s
  ArgLbl :: forall s ty . LambdaLabel s ty -> LabelInfo s

-------------------------------------------------------------------------
-- Program State
-------------------------------------------------------------------------

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

-------------------------------------------------------------------------
-- Syntax State
-------------------------------------------------------------------------

data SyntaxState s =
  SyntaxState { _stxLabels :: Map LabelName (LabelInfo s)
              , _stxAtoms :: Map AtomName (Some (Atom s))
              , _stxRegisters :: Map RegName (Some (Reg s))
              , _stxNonceGen :: NonceGenerator IO s
              , _stxProgState :: ProgramState s
              }

data Arg t = Arg AtomName Position (TypeRepr t)

data FunctionHeader =
  forall args ret .
  FunctionHeader { _headerName :: FunctionName
                 , _headerArgs :: Ctx.Assignment Arg args
                 , _headerRet :: TypeRepr ret
                 , _headerHandle :: FnHandle args ret
                 , _headerPos :: Position
                 }

data FunctionSource s =
  FunctionSource { _functionRegisters :: [AST s]
                 , _functionBody :: AST s
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

-------------------------------------------------------------------------
-- Parser Monad
-------------------------------------------------------------------------

newtype Parser s a =
  Parser { runParser :: ExceptT (ExprErr s) (StateT (SyntaxState s) IO) a }
  deriving (Functor)

instance Applicative (Parser s) where
  pure x = Parser (pure x)
  (Parser f) <*> (Parser x) = Parser (f <*> x)

instance Alternative (Parser s) where
  empty = Parser $ throwError $ TrivialErr InternalPos
  (Parser x) <|> (Parser y) = Parser (x <|> y)

instance Semigroup (Parser s a) where
  (<>) = (<|>)

instance Monoid (Parser s a) where
  mempty = empty

instance Monad (Parser s) where
  (Parser m) >>= f = Parser $ m >>= \a -> runParser (f a)

instance MonadError (ExprErr s) (Parser s) where
  throwError e = Parser $ throwError e
  catchError m h = Parser $ catchError (runParser m) (\e -> runParser $ h e)

instance MonadState (SyntaxState s) (Parser s) where
  get = Parser get
  put s = Parser $ put s

instance MonadIO (Parser s) where
  liftIO io = Parser $ lift $ lift io

instance MonadPlus (Parser s) where
  mzero = empty
  mplus = (<|>)

top :: NonceGenerator IO s -> HandleAllocator -> [(SomeHandle,Position)] -> Parser s a -> IO (Either (ExprErr s) a)
top ng ha builtIns (Parser (ExceptT (StateT act))) =
  fst <$> act (initSyntaxState ng (initProgState builtIns ha))

-------------------------------------------------------------------------
-- Fresh Name Generation
-------------------------------------------------------------------------

freshId :: (MonadState (SyntaxState s) m, MonadIO m) => m (Nonce s tp)
freshId =
  do ng <- use stxNonceGen
     liftIO $ freshNonce ng

freshLabel :: (MonadState (SyntaxState s) m, MonadIO m) => m (Label s)
freshLabel = Label <$> freshId

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

newUnassignedReg :: (MonadState (SyntaxState s) m, MonadIO m) => TypeRepr t -> m (Reg s t)
newUnassignedReg t =
  do i <- freshId
     let fakePos = OtherPos "Parser internals"
     return $! Reg { regPosition = fakePos
                   , regId = i
                   , typeOfReg = t
                   }

-------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------

with :: MonadState s m => Lens' s a -> (a -> m b) -> m b
with l act = do x <- use l; act x

