{-| Operations over related to the Mir Ty AST -}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}
module Mir.MirTy where

import GHC.Stack(HasCallStack)

import Mir.Mir

---------------------------------------------------------------------------------------------

-- | Convert field to type. Perform the corresponding substitution if field is a type param.
fieldToTy :: HasCallStack => Field -> Ty
fieldToTy (Field _ t _subst) = t
