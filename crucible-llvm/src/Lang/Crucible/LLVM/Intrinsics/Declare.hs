-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Declare
-- Description      : Function declarations
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}

module Lang.Crucible.LLVM.Intrinsics.Declare
  ( Declare(..)
  , SomeDeclare(SomeDeclare)
  , fromHandle
  , fromSomeHandle
  , fromLLVM
  , fromLLVMWithWarnings
  ) where

import qualified Control.Monad.Fail as Fail
import           Control.Monad.IO.Class (liftIO)
import qualified Data.Maybe as Maybe
import qualified Data.Text as Text
import           Data.Traversable (for)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import qualified What4.FunctionName as WFN

import qualified Lang.Crucible.FunctionHandle as CFH
import           Lang.Crucible.Simulator.OverrideSim (OverrideSim)
import qualified Lang.Crucible.Types as CT
import           Lang.Crucible.Utils.MonadVerbosity (getLogFunction)

import           Lang.Crucible.LLVM.MemModel.Pointer (HasPtrWidth)
import           Lang.Crucible.LLVM.Translation.Types (llvmDeclToFunHandleRepr')
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

-- | The declaration of a function.
--
-- Used primarily for matching LLVM overrides to the declarations in LLVM
-- modules or S-expression programs.
data Declare args ret
  = Declare
    { decName :: L.Symbol
    , decArgs :: Ctx.Assignment CT.TypeRepr args
    , decRet :: CT.TypeRepr ret
    }
  deriving Show

data SomeDeclare = forall args ret. SomeDeclare (Declare args ret)

fromHandle :: CFH.FnHandle args ret -> Declare args ret
fromHandle hdl =
  Declare
  { decName = L.Symbol (Text.unpack (WFN.functionName (CFH.handleName hdl)))
  , decArgs = CFH.handleArgTypes hdl
  , decRet = CFH.handleReturnType hdl
  }

fromSomeHandle :: CFH.SomeHandle -> SomeDeclare
fromSomeHandle (CFH.SomeHandle hdl) = SomeDeclare (fromHandle hdl)

fromLLVM ::
  ( ?lc :: TypeContext
  , HasPtrWidth wptr
  , Fail.MonadFail m
  ) =>
  L.Declare ->
  m SomeDeclare
fromLLVM decl =
  llvmDeclToFunHandleRepr' decl $ \args ret ->
    pure $
      SomeDeclare $
        Declare
        { decName = L.decName decl
        , decArgs = args
        , decRet = ret
        }

-- | Internal, for 'Fail.MonadFail' instance
newtype EitherString a = EitherString (Either String a)
  deriving (Applicative, Functor, Monad)

instance Fail.MonadFail EitherString where
  fail = EitherString . Left

-- | Apply 'fromLLVM' in a loop, warning on failures
fromLLVMWithWarnings ::
  ( ?lc :: TypeContext
  , HasPtrWidth wptr
  ) =>
  [L.Declare] ->
  OverrideSim p sym ext rtp l a [SomeDeclare]
fromLLVMWithWarnings decls =
  fmap Maybe.catMaybes $
    for decls $ \decl -> do
      case fromLLVM decl of
        EitherString (Left err) -> do
          logFn <- getLogFunction
          let msg = unlines ["Unliftable LLVM declaration", show decl, show err]
          liftIO $ logFn 3 msg
          pure Nothing
        EitherString (Right d) ->
          pure (Just d)
