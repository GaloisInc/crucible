{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
module Lang.Crucible.Analysis.Taint where

import Lang.Crucible.Analysis.Fixpoint

--data Taint = Tainted | Untainted

-- type family Tainted a
-- type instance T

-- data Tainted = forall (a :: CrucibleType). Tainted | Untainted

-- taintDomain = Domain {domTop = Untainted
--                      ,domBottom = Tainted
--                      ,domJoin = \t1 t2 -> case (t1, t2) of
--                          (Tainted, _) -> Tainted
--                          (_, Tainted) -> Tainted
--                          _            -> Untainted
--                      } 
