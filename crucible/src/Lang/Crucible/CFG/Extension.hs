{- |
Module           : Lang.Crucible.CFG.Extension
Description      : Support infrastructure for syntax extensions
Copyright        : (c) Galois, Inc 2017
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>

This module provides basic definitions necessary for handling syntax extensions
in Crucible.  Syntax extensions provide a mechanism for users of the Crucible library
to add new syntactic forms to the base control-flow-graph representation of programs.

Syntax extensions are more flexible and less tedious for some use cases than other
extension methods (e.g., override functions).
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.CFG.Extension
( ExprExtension
, StmtExtension
, IsSyntaxExtension
, PrettyApp(..)
, TypeApp(..)
, PrettyExt
, TraverseExt

  -- * Empty extension
, EmptyExprExtension
, EmptyStmtExtension
) where

import           Data.Kind (Type)
import           Data.Parameterized.TraversableFC
import           Text.PrettyPrint.ANSI.Leijen (Doc)

import           Lang.Crucible.Types


class PrettyApp (app :: (k -> Type) -> k -> Type) where
  ppApp :: (forall x. f x -> Doc) -> (forall x. app f x -> Doc)

class TypeApp (app :: (CrucibleType -> Type) -> CrucibleType -> Type) where
  appType :: app f x -> TypeRepr x

type family ExprExtension (ext :: Type) :: (CrucibleType -> Type) -> (CrucibleType -> Type)
type family StmtExtension (ext :: Type) :: (CrucibleType -> Type) -> (CrucibleType -> Type)

type PrettyExt ext =
  ( PrettyApp (ExprExtension ext)
  , PrettyApp (StmtExtension ext)
  )

type TraverseExt ext =
  ( TraversableFC (ExprExtension ext)
  , TraversableFC (StmtExtension ext)
  )

-- | This class captures all the grungy technical capabilities
--   that are needed for syntax extensions.  These capabilities
--   allow syntax to be tested for equality, ordered, put into
--   hashtables, traversed and printed, etc.
--
--   The actual meat of implementing the semantics of syntax
--   extensions is left to a later phase.  See the @ExtensionImpl@
--   record defined in "Lang.Crucible.Simulator.ExecutionTree".
class
   ( OrdFC (ExprExtension ext)
   , TraversableFC (ExprExtension ext)
   , PrettyApp (ExprExtension ext)
   , TypeApp (ExprExtension ext)
   --
   , TraversableFC (StmtExtension ext)
   , PrettyApp (StmtExtension ext)
   , TypeApp (StmtExtension ext)
   ) =>
   IsSyntaxExtension ext

-- | The empty expression syntax extension, which adds no new syntactic forms.
data EmptyExprExtension :: (CrucibleType -> Type) -> (CrucibleType -> Type)

deriving instance Show (EmptyExprExtension f tp)

type instance ExprExtension () = EmptyExprExtension

-- | The empty statement syntax extension, which adds no new syntactic forms.
data EmptyStmtExtension :: (CrucibleType -> Type) -> (CrucibleType -> Type) where

deriving instance Show (EmptyStmtExtension f tp)

type instance StmtExtension () = EmptyStmtExtension

instance ShowFC EmptyExprExtension where
  showsPrecFC _ _ = \case
instance TestEqualityFC EmptyExprExtension where
  testEqualityFC _ = \case
instance OrdFC EmptyExprExtension where
  compareFC _ = \case
instance HashableFC EmptyExprExtension where
  hashWithSaltFC _ _ = \case
instance FunctorFC EmptyExprExtension where
  fmapFC _ = \case
instance FoldableFC EmptyExprExtension where
  foldMapFC _ = \case
instance TraversableFC EmptyExprExtension where
  traverseFC _ = \case
instance PrettyApp EmptyExprExtension where
  ppApp _ = \case
instance TypeApp EmptyExprExtension where
  appType = \case

instance ShowFC EmptyStmtExtension where
  showsPrecFC _ _ = \case
instance TestEqualityFC EmptyStmtExtension where
  testEqualityFC _ = \case
instance OrdFC EmptyStmtExtension where
  compareFC _ = \case
instance HashableFC EmptyStmtExtension where
  hashWithSaltFC _ _ = \case
instance FunctorFC EmptyStmtExtension where
  fmapFC _ = \case
instance FoldableFC EmptyStmtExtension where
  foldMapFC _ = \case
instance TraversableFC EmptyStmtExtension where
  traverseFC _ = \case
instance PrettyApp EmptyStmtExtension where
  ppApp _ = \case
instance TypeApp EmptyStmtExtension where
  appType = \case

instance IsSyntaxExtension ()
