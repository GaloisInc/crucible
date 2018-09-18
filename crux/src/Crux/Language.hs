{-# Language ExistentialQuantification #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ScopedTypeVariables #-}

module Crux.Language where

import System.Console.GetOpt
import Lang.Crucible.Simulator
import Lang.Crucible.Types
import qualified Lang.Crucible.CFG.Core as C

import qualified What4.InterpretedFloatingPoint        as W4
import           Lang.Crucible.Backend
import qualified What4.Interface                       as W4

import Data.Typeable(Typeable)

type Verbosity = Int

class (Typeable a) => Language a where

  -- name of the language
  name :: String

  -- commandline options for this language
  -- (a data family, so must be instantiated by a data type declaration in each instance)
  data LangOptions a :: *
  defaultOptions :: LangOptions a

  options :: [OptDescr (LangOptions a -> LangOptions a)]
  addOpt  :: (String, String) -> LangOptions a -> LangOptions a
  
  -- how to display language-specfic errors during simulation
  type LangError a ::  *
  formatError :: LangError a -> String

  -- simulation function
  simulate :: (IsBoolSolver sym, W4.IsSymExprBuilder sym, W4.IsInterpretedFloatSymExprBuilder sym,
      W4.SymInterpretedFloatType sym W4.SingleFloat ~ C.BaseRealType,
      W4.SymInterpretedFloatType sym W4.DoubleFloat ~ C.BaseRealType) =>    
    LangOptions a -> sym -> p -> Verbosity -> String -> IO (ExecResult p sym a (RegEntry sym UnitType))

-- Trivial instance of the class

data Trivial = Trivial

instance Language Trivial where
  name = "trivial"
  type LangError Trivial = ()
  formatError _ = "()"
  data LangOptions Trivial = TrivialOptions
  defaultOptions = TrivialOptions
  options = []
  addOpt _ = id
  simulate _opts _sym _verb _s = error "TRIVIAL"

