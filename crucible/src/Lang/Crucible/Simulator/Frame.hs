{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Lang.Crucible.Simulator.Frame
  ( SimFrame(..)
  , CrucibleLang
  , OverrideLang
  , OverrideFrame(..)
  , overrideSimFrame
  ) where

import Control.Lens

import Lang.Crucible.FunctionName
import Lang.Crucible.Simulator.CallFrame
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Types

------------------------------------------------------------------------
-- CrucibleLang

-- | Nominal type for identifying override frames.
data CrucibleLang (blocks :: Ctx (Ctx CrucibleType)) (ret :: CrucibleType)

------------------------------------------------------------------------
-- OverrideLang

-- | Nominal type for identifying override frames.
data OverrideLang (args :: Ctx CrucibleType) (ret :: CrucibleType)

------------------------------------------------------------------------
-- OverrideFrame

-- | Frame in call to override.
data OverrideFrame sym (ret :: CrucibleType) args
   = OverrideFrame { override :: !FunctionName
                   , overrideRegMap :: !(RegMap sym args)
                     -- ^ Arguments to override.
                   }

------------------------------------------------------------------------
-- SimFrame

data SimFrame sym ext l (args :: Maybe (Ctx CrucibleType)) where
  OF :: !(OverrideFrame sym ret args)
     -> SimFrame sym ext (OverrideLang args ret) 'Nothing
  MF :: !(CallFrame sym ext blocks ret args)
     -> SimFrame sym ext (CrucibleLang blocks ret) ('Just args)
  RF :: !(RegEntry sym ret)
     -> SimFrame sym ext (CrucibleLang blocks ret) 'Nothing

overrideSimFrame :: Lens (SimFrame sym ext (OverrideLang a r) 'Nothing)
                         (SimFrame sym ext (OverrideLang a r) 'Nothing)
                         (OverrideFrame sym r a)
                         (OverrideFrame sym r a)
overrideSimFrame f (OF g) = OF <$> f g
