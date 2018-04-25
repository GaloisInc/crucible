{-# Language DataKinds #-}
{-# Language TemplateHaskell #-}
{-# Language Rank2Types #-}
module Model where

import Control.Lens(makeLenses, (<&>), (^.), (&), (.~), Lens')

import Lang.Crucible.Types(BaseBVType)
import Lang.Crucible.Solver.SimpleBuilder(Elt)

data Model scope = Model
  { _model_i8 :: Vars scope (BaseBVType 8)
  }

emptyModel :: Model scope
emptyModel = Model { _model_i8 = emptyVars }


data Vars scope ty = Vars
  { nextVar       :: !Int
  , generatedVars :: [ Elt scope ty ]
  }

emptyVars :: Vars scope ty
emptyVars = Vars { nextVar = 0, generatedVars = [] }

makeLenses ''Model

newVar ::
  Functor m =>
  (Int -> m (Elt scope ty)) ->
  Vars scope ty -> m (Elt scope ty, Vars scope ty)
newVar mk v =
  mk var <&> \elt -> ( elt
                     , v { nextVar = var + 1
                         , generatedVars = elt : generatedVars v
                         }
                      )
  where var = nextVar v

modelNewVar ::
  Functor m =>
  Lens' (Model scope) (Vars scope ty) ->
  (Int -> m (Elt scope ty)) ->
  Model scope -> m (Elt scope ty, Model scope)
modelNewVar l mk m = newVar mk (m ^. l) <&> \(e,v1) -> (e, m & l .~ v1)


