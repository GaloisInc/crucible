{-
Module           : Lang.Crucible.CFG.Common
Copyright        : (c) Galois, Inc 2014-2016
Maintainer       : Joe Hendrix <jhendrix@galois.com>
License          : BSD3

Data structures and operations that are common to both the
registerized and the SSA form CFG representations.
-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
module Lang.Crucible.CFG.Common
  ( -- * Global variables
    GlobalVar(..)
  , freshGlobalVar
    -- * MATLAB Switch statements
  , MSwitch(..)
  , constMSwitch
  , zipSwitchWith
  , ppMSwitch
  ) where

import           Control.Monad.ST
import           Data.Text (Text)
import qualified Data.Text as Text
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce.Unsafe
import           Data.Parameterized.TraversableF

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- GlobalVar

-- | A global variable.
data GlobalVar tp
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


------------------------------------------------------------------------
-- MSwitch

-- | Data structure for a type-case switch.  A switch is used to
--   unpack an arbitrary matlab value, jumping to one of the given
--   switch targets, depending on the runtime type of a value to be examined.
data MSwitch tgt
   = MSwitch { matchRealArray      :: tgt CplxArrayType
             , matchIntArray       :: tgt MatlabIntArrayType
             , matchUIntArray      :: tgt MatlabUIntArrayType
             , matchLogicArray     :: tgt LogicArrayType
             , matchCharArray      :: tgt CharArrayType
             , matchCellArray      :: tgt CellArrayType
             , matchStructArray    :: tgt MatlabStructArrayType
             , matchHandle         :: tgt MatlabHandleType
             , matchSymLogicArray  :: tgt SymLogicArrayType
             , matchSymRealArray   :: tgt SymRealArrayType
             , matchSymCplxArray   :: tgt SymCplxArrayType
             , matchSymIntArray    :: tgt MatlabSymbolicIntArrayType
             , matchSymUIntArray   :: tgt MatlabSymbolicUIntArrayType
             , matchObjectArray    :: tgt MatlabObjectArrayType
             }

constMSwitch :: (forall tp . tgt tp) -> MSwitch tgt
constMSwitch v =
  MSwitch { matchRealArray      = v
          , matchIntArray       = v
          , matchUIntArray      = v
          , matchLogicArray     = v
          , matchCharArray      = v
          , matchCellArray      = v
          , matchStructArray    = v
          , matchHandle         = v
          , matchSymLogicArray  = v
          , matchSymRealArray   = v
          , matchSymCplxArray   = v
          , matchSymIntArray    = v
          , matchSymUIntArray   = v
          , matchObjectArray    = v
          }

instance ShowF tgt => Show (MSwitch tgt) where
  show (MSwitch {..}) =
     unwords [ "(MSwitch"
             , showF matchRealArray
             , showF matchIntArray
             , showF matchUIntArray
             , showF matchLogicArray
             , showF matchCharArray
             , showF matchCellArray
             , showF matchStructArray
             , showF matchHandle
             , showF matchSymLogicArray
             , showF matchSymRealArray
             , showF matchSymCplxArray
             , showF matchSymIntArray
             , showF matchSymUIntArray
             , showF matchObjectArray
             , ")"]

instance FunctorF MSwitch where
  fmapF = fmapFDefault

instance FoldableF MSwitch where
  foldMapF = foldMapFDefault

instance TraversableF MSwitch where
  traverseF f m = do
    MSwitch
      <$> f (matchRealArray m)
      <*> f (matchIntArray m)
      <*> f (matchUIntArray m)
      <*> f (matchLogicArray m)
      <*> f (matchCharArray m)
      <*> f (matchCellArray m)
      <*> f (matchStructArray m)
      <*> f (matchHandle m)
      <*> f (matchSymLogicArray m)
      <*> f (matchSymRealArray m)
      <*> f (matchSymCplxArray m)
      <*> f (matchSymIntArray m)
      <*> f (matchSymUIntArray m)
      <*> f (matchObjectArray m)

zipSwitchWith :: (forall tp. f tp -> g tp -> h tp) -> MSwitch f -> MSwitch g -> MSwitch h
zipSwitchWith f m1 m2 =
  MSwitch
  { matchRealArray   = f (matchRealArray m1)    (matchRealArray m2)
  , matchIntArray    = f (matchIntArray m1)     (matchIntArray m2)
  , matchUIntArray   = f (matchUIntArray m1)    (matchUIntArray m2)
  , matchLogicArray  = f (matchLogicArray m1)   (matchLogicArray m2)
  , matchCharArray   = f (matchCharArray m1)    (matchCharArray m2)
  , matchCellArray   = f (matchCellArray m1)    (matchCellArray m2)
  , matchStructArray = f (matchStructArray m1)  (matchStructArray m2)
  , matchHandle      = f (matchHandle m1)       (matchHandle m2)
  , matchSymLogicArray = f (matchSymLogicArray m1) (matchSymLogicArray m2)
  , matchSymRealArray  = f (matchSymRealArray m1)  (matchSymRealArray m2)
  , matchSymCplxArray  = f (matchSymCplxArray m1)  (matchSymCplxArray m2)
  , matchSymIntArray   = f (matchSymIntArray m1)   (matchSymIntArray m2)
  , matchSymUIntArray  = f (matchSymUIntArray m1)  (matchSymUIntArray m2)
  , matchObjectArray   = f (matchObjectArray m1)   (matchObjectArray m2)
  }

ppMSwitch :: (forall tp . String -> tgt tp -> Doc) -> MSwitch tgt -> [Doc]
ppMSwitch pp (MSwitch {..})
  = [ pp "R"       matchRealArray
    , pp "I"       matchIntArray
    , pp "U"       matchUIntArray
    , pp "Ch"      matchLogicArray
    , pp "L"       matchCharArray
    , pp "Cell"    matchCellArray
    , pp "S"       matchStructArray
    , pp "H"       matchHandle
    , pp "symL"    matchSymLogicArray
    , pp "symR"    matchSymRealArray
    , pp "symCplx" matchSymCplxArray
    , pp "symI"    matchSymIntArray
    , pp "symU"    matchSymUIntArray
    , pp "O"       matchObjectArray
    ]
