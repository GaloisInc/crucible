------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Options
-- Description      : Definition of options that affect LLVM overrides
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
module Lang.Crucible.LLVM.Intrinsics.Options
  ( IntrinsicsOptions(..)
  , AbnormalExitBehavior(..)
  , defaultIntrinsicsOptions
  ) where

-- | Should Crucible fail when simulating a function which triggers an abnormal
-- exit, such as @abort()@?
data AbnormalExitBehavior
  = AlwaysFail
    -- ^ Functions which trigger an abnormal exit will always cause Crucible
    --   to fail.
  | OnlyAssertFail
    -- ^ The @__assert_fail()@ function will cause Crucible to fail, while
    --   other functions which triggern an abnormal exit will not cause
    --   failures. This option is primarily useful for SV-COMP.
  | NeverFail
    -- ^ Functions which trigger an abnormal exit will never cause Crucible
    --   to fail. This option is primarily useful for SV-COMP.
  deriving Eq

-- | This datatype encodes a variety of tweakable settings that to LLVM
--   overrides.
newtype IntrinsicsOptions
  = IntrinsicsOptions
    { abnormalExitBehavior :: AbnormalExitBehavior
      -- ^ Should Crucible fail when simulating a function which triggers an
      --   abnormal exit, such as @abort()@?
    }

-- | The default translation options:
--
-- * Functions which trigger an abnormal exit will always cause Crucible
--   to fail.
defaultIntrinsicsOptions :: IntrinsicsOptions
defaultIntrinsicsOptions =
  IntrinsicsOptions
  { abnormalExitBehavior = AlwaysFail
  }
