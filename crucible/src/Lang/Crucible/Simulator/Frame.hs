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
  , crucibleSimFrame
  , fromCallFrame
  , fromReturnFrame
  ) where

import Control.Lens

import What4.FunctionName
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
data OverrideLang (ret :: CrucibleType)

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

{- An alternate idea we could try to save a few indirections...
type family SimFrame sym ext l args :: * where
  SimFrame sym ext (OverrideLang ret)        ('Just args) = OverrideFrame sym ret args
  SimFrame sym ext (CrucibleLang blocks ret) ('Just args) = CallFrame sym ext blocks ret args
  SimFrame sym ext (CrucibleLang blocks ret) ('Nothing)   = RegEntry sym ret
-}

data SimFrame sym ext l (args :: Maybe (Ctx CrucibleType)) where
  -- | Custom code to execute, typically for "overrides"
  OF :: !(OverrideFrame sym ret args)
     -> SimFrame sym ext (OverrideLang ret) ('Just args)

  -- | We are executing some Crucible instructions
  MF :: !(CallFrame sym ext blocks ret args)
     -> SimFrame sym ext (CrucibleLang blocks ret) ('Just args)

  -- | We should return this value.
  RF :: !(RegEntry sym ret)
     -> SimFrame sym ext (CrucibleLang blocks ret) 'Nothing

overrideSimFrame :: Lens (SimFrame sym ext (OverrideLang r) ('Just args))
                         (SimFrame sym ext (OverrideLang r') ('Just args'))
                         (OverrideFrame sym r args)
                         (OverrideFrame sym r' args')
overrideSimFrame f (OF g) = OF <$> f g

crucibleSimFrame :: Lens (SimFrame sym ext (CrucibleLang blocks r) ('Just args))
                         (SimFrame sym ext (CrucibleLang blocks' r') ('Just args'))
                         (CallFrame sym ext blocks r args)
                         (CallFrame sym ext blocks' r' args')
crucibleSimFrame f (MF c) = MF <$> f c


fromCallFrame :: SimFrame sym ext (CrucibleLang b r) ('Just a)
              -> CallFrame sym ext b r a
fromCallFrame (MF x) = x

fromReturnFrame :: SimFrame sym ext (CrucibleLang b r) 'Nothing
                -> RegEntry sym r
fromReturnFrame (RF x) = x
