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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.CFG.Extension
( ExprExtension
, IsSyntaxExtension
, PrettyApp(..)
, TypeApp(..)
  -- * Empty extension
, EmptyExprExtension
) where

import           Text.PrettyPrint.ANSI.Leijen (Doc)
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.Types


class PrettyApp (app :: (k -> *) -> k -> *) where
  ppApp :: (forall x. f x -> Doc) -> (forall x. app f x -> Doc)

class TypeApp (app :: (CrucibleType -> *) -> CrucibleType -> *) where
  appType :: app f x -> TypeRepr x

type family ExprExtension (ext :: *) :: (CrucibleType -> *) -> (CrucibleType -> *)

class
   ( ShowFC (ExprExtension ext)
   , TestEqualityFC (ExprExtension ext)
   , OrdFC (ExprExtension ext)
   , HashableFC (ExprExtension ext)
   , TraversableFC (ExprExtension ext)
   , PrettyApp (ExprExtension ext)
   , TypeApp (ExprExtension ext)
   ) =>
   IsSyntaxExtension ext

-- | The empty expression syntax extension, which adds no new syntacitic
--   forms.
data EmptyExprExtension :: (CrucibleType -> *) -> (CrucibleType -> *) where
type instance ExprExtension () = EmptyExprExtension

instance ShowFC EmptyExprExtension where
  showFC _ = \case
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

instance IsSyntaxExtension ()