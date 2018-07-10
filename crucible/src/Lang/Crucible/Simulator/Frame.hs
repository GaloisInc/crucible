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
  , fromJustCallFrame
  , fromNothingCallFrame
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

  -- | Custom code to execute, typically for "overrides"
  OF :: !(OverrideFrame sym ret args)
     -> SimFrame sym ext (OverrideLang args ret) 'Nothing

  -- | We are executing some Crucible instructions
  MF :: !(CallFrame sym ext blocks ret args)
     -> SimFrame sym ext (CrucibleLang blocks ret) ('Just args)

  -- | We should return this value.
  RF :: !(RegEntry sym ret)
     -> SimFrame sym ext (CrucibleLang blocks ret) 'Nothing

overrideSimFrame :: Lens (SimFrame sym ext (OverrideLang a r) 'Nothing)
                         (SimFrame sym ext (OverrideLang a r) 'Nothing)
                         (OverrideFrame sym r a)
                         (OverrideFrame sym r a)
overrideSimFrame f (OF g) = OF <$> f g

crucibleSimFrame :: Lens (SimFrame sym ext (CrucibleLang blocks r) ('Just args))
                         (SimFrame sym ext (CrucibleLang blocks r) ('Just args'))
                         (CallFrame sym ext blocks r args)
                         (CallFrame sym ext blocks r args')
crucibleSimFrame f (MF c) = MF <$> f c



fromJustCallFrame :: SimFrame sym ext (CrucibleLang b r) ('Just a)
                  -> CallFrame sym ext b r a
fromJustCallFrame (MF x) = x

fromNothingCallFrame :: SimFrame sym ext (CrucibleLang b r) 'Nothing
                     -> RegEntry sym r
fromNothingCallFrame (RF x) = x


