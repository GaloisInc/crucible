{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
module What4.Utils.Util
    (
      withRounding
    , fromJust'
    , makeSymbol
    , SomeSome(..)
    ) where

import           Data.Kind
import           Text.Printf ( printf )
import           Data.Maybe ( fromMaybe )
import           What4.BaseTypes
import           What4.Utils.Log
import qualified What4.Interface as S
import           What4.Symbol ( SolverSymbol, userSymbol )

-- | Like 'Data.Parameterized.Some.Some', but for doubly-parameterized types.
data SomeSome (f :: k1 -> k2 -> Type) = forall x y. SomeSome (f x y)

-- | Try converting any 'String' into a 'SolverSymbol'. If it is an invalid
-- symbol, then error.
makeSymbol :: String -> SolverSymbol
makeSymbol name = case userSymbol sanitizedName of
                    Right symbol -> symbol
                    Left _ -> error $ printf "tried to create symbol with bad name: %s (%s)"
                                             name sanitizedName
  where
    sanitizedName = map (\c -> case c of ' ' -> '_'; '.' -> '_'; _ -> c) name

-- | Traceback-friendly fromJust alternative.
fromJust' :: (HasCallStack) => String -> Maybe a -> a
fromJust' label x =
    let msg = "fromJust': got Nothing (" ++ label ++ ")"
    in fromMaybe (error msg) x

withRounding
  :: forall sym tp
   . S.IsExprBuilder sym
  => sym
  -> S.SymBV sym 2
  -> (S.RoundingMode -> IO (S.SymExpr sym tp))
  -> IO (S.SymExpr sym tp)
withRounding sym r action = do
  cRNE <- roundingCond S.RNE
  cRTZ <- roundingCond S.RTZ
  cRTP <- roundingCond S.RTP
  S.iteM S.baseTypeIte sym cRNE
    (action S.RNE) $
    S.iteM S.baseTypeIte sym cRTZ
      (action S.RTZ) $
      S.iteM S.baseTypeIte sym cRTP (action S.RTP) (action S.RTN)
 where
  roundingCond :: S.RoundingMode -> IO (S.Pred sym)
  roundingCond rm =
    S.bvEq sym r =<< S.bvLit sym knownNat (roundingModeToBits rm)

roundingModeToBits :: S.RoundingMode -> Integer
roundingModeToBits = \case
  S.RNE -> 0
  S.RTZ -> 1
  S.RTP -> 2
  S.RTN -> 3
  S.RNA -> error $ "unsupported rounding mode: " ++ show S.RNA
