{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Combo
  (
    Combo(..)
  , ComboPointerType(..)
  )
where

import           Data.Data ( Data )
import           Data.Kind ( Type )
import           Data.Text (Text, pack, unpack)
import           Data.Typeable ( Typeable )
import           GHC.Generics ( Generic, Generic1 )
import           GHC.TypeLits
import           Prettyprinter ( pretty, (<+>), viaShow )

import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.CFG.Common ( GlobalVar )
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types


data Combo
  deriving (Data, Eq, Generic, Ord, Typeable)

type instance ExprExtension Combo = ComboExtensionExpr
type instance StmtExtension Combo = ComboStmt

instance IsSyntaxExtension Combo

----------------------------------------------------------------------

data ComboPointerType = ComboPointerType
data ComboMem

data ComboExtensionExpr :: (CrucibleType -> Type) -> (CrucibleType -> Type) where
  Combo_FooExpr :: Int -> ComboExtensionExpr f RealValType

data ComboStmt (f :: CrucibleType -> Type) :: CrucibleType -> Type where
  Combo_PushFrame :: !Text -> !(GlobalVar UnitType) -> ComboStmt f UnitType

$(return [])

instance TypeApp ComboExtensionExpr where
  appType = \case
    Combo_FooExpr _ -> knownRepr

instance PrettyApp ComboExtensionExpr where
  ppApp pp = \case
    Combo_FooExpr v -> "a combo foo expr @ " <> pretty v

instance TestEqualityFC ComboExtensionExpr where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|ComboExtensionExpr|]
      [
        (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
      ])

instance OrdFC ComboExtensionExpr where
  compareFC testSubterm =
    $(U.structuralTypeOrd [t|ComboExtensionExpr|]
      [
        (U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
      , (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
      ])

instance FunctorFC ComboExtensionExpr where
  fmapFC = fmapFCDefault

instance FoldableFC ComboExtensionExpr where
  foldMapFC = foldMapFCDefault

instance TraversableFC ComboExtensionExpr where
  traverseFC = $(U.structuralTraversal [t|ComboExtensionExpr|]
                [
                ])

instance PrettyApp ComboStmt where
  ppApp pp = \case
    Combo_PushFrame nm mvar -> "cO.pushFrame" <+> pretty nm <+> viaShow mvar

instance TypeApp ComboStmt where
  appType = \case
    Combo_PushFrame{} -> knownRepr

instance FunctorFC ComboStmt where
  fmapFC = fmapFCDefault

instance FoldableFC ComboStmt where
  foldMapFC = foldMapFCDefault

instance TraversableFC ComboStmt where
  traverseFC = $(U.structuralTraversal [t|ComboStmt|]
                [
                ])
