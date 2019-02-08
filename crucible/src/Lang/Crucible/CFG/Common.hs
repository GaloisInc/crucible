{- |
Module           : Lang.Crucible.CFG.Common
Description      : Common CFG datastructure definitions
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Data structures and operations that are common to both the
registerized and the SSA form CFG representations.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
module Lang.Crucible.CFG.Common
  ( -- * Global variables
    GlobalVar(..)
  , freshGlobalVar
  ) where

import           Control.Monad.ST
import           Data.Text (Text)
import qualified Data.Text as Text
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce.Unsafe

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- GlobalVar

-- | A global variable.
data GlobalVar (tp :: CrucibleType)
   = GlobalVar { globalNonce :: {-# UNPACK #-} !(Nonce tp)
               , globalName  :: !Text
               , globalType  :: !(TypeRepr tp)
               }

instance TestEquality GlobalVar where
  x `testEquality` y = globalNonce x `testEquality` globalNonce y

instance OrdF GlobalVar where
  x `compareF` y = globalNonce x `compareF` globalNonce y

instance Show (GlobalVar tp) where
  show = Text.unpack . globalName

instance ShowF GlobalVar

instance Pretty (GlobalVar tp) where
  pretty  = text . show


freshGlobalVar :: HandleAllocator s
               -> Text
               -> TypeRepr tp
               -> ST s (GlobalVar tp)
freshGlobalVar halloc nm tp = do
  nonce <- freshNonce (haCounter halloc)
  return GlobalVar
         { globalNonce = nonce
         , globalName  = nm
         , globalType  = tp
         }
