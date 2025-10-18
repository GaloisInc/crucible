{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module Mir.Pass (
    Pass,
    rewriteCollection
) where


import GHC.Stack

import Mir.Mir
import Mir.Pass.AllocateEnum ( passAllocateEnum )

type Pass = (?debug::Int, HasCallStack) => Collection -> Collection

--------------------------------------------------------------------------------------
infixl 0 |>
(|>) :: a -> (a -> b) -> b
x |> f = f x
--------------------------------------------------------------------------------------

rewriteCollection :: Pass
rewriteCollection col =
  col
    |> passAllocateEnum

--------------------------------------------------------------------------------------
