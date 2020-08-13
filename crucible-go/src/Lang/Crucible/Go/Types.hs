{-|
Module      : Lang.Crucible.Go.Types
Description : Go translation types
Maintainer  : abagnall@galois.com
Stability   : experimental

This file contains various type definitions related to translation of
Go programs to Crucible.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Go.Types where

import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.Identity
import           Control.Monad.State

import           Data.Default.Class
import           Data.HashMap.Strict as HM
import           Data.Maybe (fromJust)
import           Data.Text (Text)

import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some (Some(..))

import           What4.FunctionName (FunctionName)

import           Language.Go.AST
import           Language.Go.Types
import           Lang.Crucible.Go.Encodings

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import           Lang.Crucible.CFG.Extension
import qualified Lang.Crucible.CFG.Generator as Gen
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

----------------------------------------------------------------------
-- | Go extension tag.

newtype Go = Go ()

type instance ExprExtension Go = EmptyExprExtension
type instance StmtExtension Go = EmptyStmtExtension

instance IsSyntaxExtension Go

goIntrinsicTypes :: IntrinsicTypes sym
goIntrinsicTypes = emptyIntrinsicTypes

type Verbosity = Int

-- | A function-local register.
data GoReg s tp where
  GoReg :: TypeRepr tp -> Gen.Reg s (ReferenceType tp) -> GoReg s tp
  deriving Show

type SomeGoReg s = Some (GoReg s)

data GoGlobal where
  GoGlobal :: Gen.GlobalVar tp -- ^ the global variable identifier
           -> (forall s. Gen.Expr Go s tp) -- ^ initial (zero) value
           -> GoGlobal
deriving instance Show GoGlobal

-- | As assignable location. Either a statically known location
-- (reference, global, array offset) or a pointer expression.
data GoLoc s tp where
  GoLocRef :: Gen.Expr Go s (ReferenceType tp)
           -> GoLoc s tp
  GoLocGlobal :: Gen.GlobalVar tp
              -> GoLoc s tp
  GoLocArray :: Gen.Expr Go s (ReferenceType (VectorType tp))
             -> Gen.Expr Go s NatType
             -> GoLoc s tp
  GoLocPointer :: Gen.Expr Go s (PointerType tp)
               -> GoLoc s tp
  deriving Show

-- | Existentially packaged positive natural number.
data PosNat = forall w. PosNat (NatRepr w) (LeqProof 1 w)

intToPosNat :: Int -> Maybe PosNat
intToPosNat i = do
  Some w <- someNat (fromIntegral i)
  LeqProof <- isPosNat w
  return $ PosNat w LeqProof

data AnyGoExpr where
  AnyGoExpr :: (forall s. SomeGoExpr s) -> AnyGoExpr
deriving instance Show AnyGoExpr

-- | A package environment. Note that Go is a "lisp-1" language in the
-- sense that variables and functions share the same namespace, but we
-- keep them separately 1) for convenience and 2) globals can't be
-- embedded in expressions.
data Namespace = Namespace { ns_globals :: HashMap Text GoGlobal
                           , ns_funcs :: HashMap Text SomeHandle
                           }
  deriving Show

insert_global :: Text -> GoGlobal -> Namespace -> Namespace
insert_global name glob ns =
  ns { ns_globals = HM.insert name glob (ns_globals ns) }

insert_function :: Text -> SomeHandle -> Namespace -> Namespace
insert_function name h ns =
  ns { ns_funcs = HM.insert name h (ns_funcs ns) }

instance Default Namespace where
  def = Namespace { ns_globals = HM.empty
                  , ns_funcs = HM.empty }

namespace_union :: Namespace -> Namespace -> Namespace
namespace_union (Namespace g1 f1) (Namespace g2 f2) =
  Namespace { ns_globals = HM.union g1 g2
            , ns_funcs = HM.union f1 f2 }

-- | Translator state.
data TransState =
  TransState
  { machineWordWidth :: PosNat -- ^ Bit width of unqualified "int" and
                               -- "uint" types
  , retRepr :: Some TypeRepr -- ^ Return type of current function
  , namespaces :: HashMap Text Namespace
  , pkgName :: Text -- ^ Name of package curently being translated
  , sng :: Maybe (Some (NonceGenerator IO))
  , halloc :: Maybe HandleAllocator
  , mainFunction :: Maybe (C.AnyCFG Go)
  , globals :: [GoGlobal] -- ^ all globals
  -- | all generated functions
  , functions :: [(Maybe (Text, FunctionName), C.AnyCFG Go)]
  }

instance Default TransState where
  def = TransState { machineWordWidth = fromJust $ intToPosNat 32
                   , retRepr = Some UnitRepr
                   , namespaces = HM.empty
                   , pkgName = ""
                   , sng = Nothing
                   , halloc = Nothing
                   , mainFunction = Nothing
                   , globals = []
                   , functions = []
                   }

addGlobal :: GoGlobal -> TranslateM' ()
addGlobal glob = modify $ \ts -> ts { globals = glob : globals ts }

addFunction :: Maybe (Text, FunctionName)
            -> C.AnyCFG Go
            -> TranslateM' ()
addFunction nm cfg = modify $ \ts -> ts { functions = (nm, cfg) : functions ts }

-- | Our generator user state only contains the local lexical
-- environment. Gamma could be generalized to a stack of nested scopes
-- to enable more efficient translation of assignment statements (not
-- always introducing new variables when they already exist IN THE
-- INNERMOST SCOPE).
data GenState s =
  GenState
  { -- | lexical environment
    gamma :: HashMap Text (SomeGoReg s)
    -- | map from label text to crucible label
  , label_map :: HashMap Text (Gen.Label s)
    -- | stack of loop labels (continue, break)
  , loop_labels :: [(Gen.Label s, Gen.Label s)]
    -- | map from loop label to continue and break crucible labels
  , loop_label_map :: HashMap Text (Gen.Label s, Gen.Label s)
    -- | set when translating a labeled statement
  , current_label :: Maybe Ident
  }

instance Default (GenState s) where
  def = GenState { gamma = HM.empty
                 , label_map = HM.empty
                 , loop_labels = []
                 , loop_label_map = HM.empty
                 , current_label = Nothing }

-- | The type of Go generator actions.
type GoGenerator s ret a = Gen.Generator Go s GenState ret IO a
data SomeGoGenerator s a =
  forall ret. SomeGoGenerator (TypeRepr ret) (GoGenerator s ret a)
instance Show (SomeGoGenerator s a) where
  show = const "<SomeGoGenerator>"

-- | A GoExpr is a value expression, possibly accompanied by a
-- corresponding assignable location (where the value lives).
data GoExpr s tp where
  GoExpr :: Maybe (GoLoc s tp)
         -> Gen.Expr Go s tp
         -> GoExpr s tp
  deriving Show
instance C.ShowF (GoExpr s) where
  showF = show
type SomeGoExpr s = Some (GoExpr s)

-- | Create a GoExpr with no location.
mkGoExpr :: Gen.Expr Go s tp -> GoExpr s tp
mkGoExpr = GoExpr Nothing

mkSomeGoExpr :: Gen.Expr Go s tp -> SomeGoExpr s
mkSomeGoExpr = Some . mkGoExpr

mkSomeGoExpr' :: C.App Go (Gen.Expr Go s) tp -> SomeGoExpr s
mkSomeGoExpr' = mkSomeGoExpr . Gen.App

goExpr :: GoExpr s tp -> Gen.Expr Go s tp
goExpr (GoExpr _loc e) = e

goExprType :: GoExpr a tp -> TypeRepr tp
goExprType (GoExpr _loc e) = exprType e

-- | Pair of things with the same type index.
data PairIx (f :: * -> CrucibleType -> *) s tp where
  PairIx :: forall f s tp. f s tp -> f s tp -> PairIx f s tp

-- | Pair of things with the same type index.
type SomePairIx f s = Some (PairIx f s)
type SomeGoPair s = Some (PairIx GoExpr s)
type SomeExprPair s = Some (PairIx (Gen.Expr Go) s)


-- | The translator monad.
type TranslateM' a = StateT TransState (ExceptT String IO) a

-- | A newtype around TranslateM' indexed by NodeTypes so it can be
-- used as a functor in recursion constructions (see
-- Lang.Crucible.Go.Rec).
newtype TranslateM (tp :: NodeType) =
  TranslateM { runTranslateM :: TranslateM' (Translated tp) }

liftIO' :: IO a -> TranslateM' a
liftIO' = lift . lift


-- | The type of results produced by translator computations, indexed
-- by NodeType. The constructors roughly correspond to the AST
-- constructors, but with some syntactic classes of constructors
-- collapsed into one or a small number of constructors (e.g., all AST
-- nodes indexed by Stmt result in a TranslatedStmt, all nodes indexed
-- by Expr result in a TranslatedExpr or TranslatedType).
data Translated (tp :: NodeType) where

  -- | The top-level result of translating a Go program.
  TranslatedMain ::
       Translated Package
    -> [Translated Package]
    -> C.SomeCFG Go EmptyCtx UnitType-- ^ initializer
    -> Maybe (C.AnyCFG Go) -- ^ the main function
    -> [GoGlobal] -- ^ all globals
    -> [(Maybe (Text, FunctionName), C.AnyCFG Go)] -- ^ all generated functions
    -> HandleAllocator -- ^ the allocator used
    -> Translated Main

  TranslatedPackage :: Text -- ^ package name
                    -> Text -- ^ package path
                    -> [Text] -- ^ paths of imports
                    -> [Text] -- ^ source file absolute paths
                    -> [Translated File] -- ^ translated source files
                    -> (forall s. SomeGoGenerator s ()) -- ^ package initializer
                    -> Translated Package

  TranslatedFile :: Text
                 -> Ident
                 -> [Translated Decl]
                 -> [Translated Decl]
                 -> Translated File

  TranslatedStmt :: (forall s. SomeGoGenerator s ())
                 -> Translated Stmt

  TranslatedExpr :: (forall s. SomeGoGenerator s (SomeGoExpr s))
                 -> Translated Expr

  TranslatedUnbound :: Ident -- ^ qualifier
                    -> Ident -- ^ name
                    -> Translated Expr

  TranslatedType :: Some TypeRepr
                 -> Translated Expr

  TranslatedFuncDecl :: Ident
                     -> C.AnyCFG Go
                     -> Translated Decl

  TranslatedGenDecl :: [Translated Spec]
                    -> Translated Decl

  TranslatedField :: [Ident]
                  -> Some TypeRepr
                  -> Translated Field

  TranslatedImportSpec :: Translated Spec

  TranslatedVarSpec :: [Ident] -- ^ names
                    -> Maybe (Translated Expr) -- ^ type
                    -> [Translated Expr] -- ^ initial values
                    -> Translated Spec

  TranslatedTypeSpec :: Translated Spec

  TranslatedBinding :: Ident
                    -> Translated Expr
                    -> Translated Bind

  TranslatedBlock :: (forall s. SomeGoGenerator s ())
                  -> Translated Block

-- deriving instance Show (Translated tp)

packageInit :: Translated Package -> SomeGoGenerator s ()
packageInit (TranslatedPackage _ _ _ _ _  ini) = ini
