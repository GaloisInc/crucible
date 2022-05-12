{-
Module           : UCCrux.LLVM.View.Util
Description      : Orphan and utility instances; see "UCCrux.LLVM.View".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}

-- Orphans for Alignment, ICmpOp
-- TODO(lb): consider newtypes
{-# OPTIONS_GHC -fno-warn-orphans #-}

module UCCrux.LLVM.View.Util
  ( Width(..)
  , Unsigned(..)
  , GlobalVarName(..)
  , FuncName(..)
  , TypeName(..)
  )
where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson (toJSONKeyText)
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Text (Text)
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import qualified Text.LLVM.AST as L

import           Lang.Crucible.LLVM.DataLayout (Alignment)

-- | Formerly the width of a bitvector
newtype Width = Width { getWidth :: Natural }
  deriving (Eq, Generic, Ord, Show)

-- | Formerly an unsigned bitvector
newtype Unsigned = Unsigned { getUnsigned :: Natural }
  deriving (Eq, Generic, Ord, Show)

-- | The name of an LLVM global variable
newtype GlobalVarName
  = GlobalVarName { getGlobalVarName :: Text }
  deriving (Eq, Ord, Show, Generic)

instance Aeson.ToJSONKey GlobalVarName where
  toJSONKey = Aeson.toJSONKeyText getGlobalVarName

instance Aeson.FromJSONKey GlobalVarName where
  fromJSONKey = Aeson.FromJSONKeyText GlobalVarName

-- | The name of an LLVM global variable
newtype FuncName
  = FuncName { getFuncName :: Text }
  deriving (Eq, Ord, Show, Generic)

instance Aeson.ToJSONKey FuncName where
  toJSONKey = Aeson.toJSONKeyText getFuncName

instance Aeson.FromJSONKey FuncName where
  fromJSONKey = Aeson.FromJSONKeyText FuncName

-- | The name of an LLVM type
newtype TypeName
  = TypeName { getTypeName :: Text }
  deriving (Eq, Ord, Show, Generic)

instance Aeson.ToJSONKey TypeName where
  toJSONKey = Aeson.toJSONKeyText getTypeName

instance Aeson.FromJSONKey TypeName where
  fromJSONKey = Aeson.FromJSONKeyText TypeName

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''Alignment)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''Width)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''Unsigned)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''GlobalVarName)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''FuncName)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''TypeName)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''L.ICmpOp)
