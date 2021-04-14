{-
Module       : UCCrux.LLVM.Setup.Assume
Description  : Assume a set of constraints
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Setup.Assume
  ( assume,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Exception (displayException, try)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable (for_)
import           Data.Text (Text)
import qualified Data.Text as Text

import           Data.Parameterized.Some (Some(Some))

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified What4.ProgramLoc as What4
import qualified What4.FunctionName as What4

import qualified Lang.Crucible.Backend as Crucible

import           UCCrux.LLVM.Constraints (ppConstraint)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Setup (SetupAssumption(SetupAssumption))
{- ORMOLU_ENABLE -}

-- | Add assumptions, handling and reporting errors appropriately.
assume ::
  Crucible.IsBoolSolver sym =>
  -- | Function name
  Text ->
  sym ->
  [SetupAssumption m sym] ->
  IO ()
assume funName sym assumptions =
  for_
    assumptions
    ( \(SetupAssumption (Some constraint) predicate) ->
        do
          maybeException <-
            liftIO $
              try $
                Crucible.addAssumption
                  sym
                  ( Crucible.GenericAssumption
                      ( What4.mkProgramLoc
                          (What4.functionNameFromText funName)
                          What4.InternalPos
                      )
                      "constraint"
                      predicate
                  )
          case maybeException of
            Left e@(Crucible.AssertionFailure _) ->
              panic
                "classify"
                [ "Concretely false assumption",
                  Text.unpack $
                    PP.renderStrict
                      ( PP.layoutPretty
                          PP.defaultLayoutOptions
                          (ppConstraint constraint)
                      ),
                  displayException e
                ]
            Left e ->
              panic
                "classify"
                [ "Unknown issue while adding assumptions",
                  Text.unpack $
                    PP.renderStrict
                      ( PP.layoutPretty
                          PP.defaultLayoutOptions
                          (ppConstraint constraint)
                      ),
                  displayException e
                ]
            Right value -> pure value
    )
