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
    , asyncLinked
    , withAsyncLinked
    ) where

import qualified Control.Exception as E
import           Data.Kind
import           Text.Printf ( printf )
import           Data.Maybe ( fromMaybe )
import           What4.BaseTypes
import           What4.Utils.Log
import qualified What4.Interface as S
import           What4.Symbol ( SolverSymbol, userSymbol )
import qualified UnliftIO as U

----------------------------------------------------------------
-- * Async

-- | Fork an async action that is linked to the parent thread, but can
-- be safely 'U.cancel'd without also killing the parent thread.
--
-- Note that if your async doesn't return unit, then you probably want
-- to 'U.wait' for it instead, which eliminates the need for linking
-- it. Also, if you plan to cancel the async near where you fork it,
-- then 'withAsyncLinked' is a better choice than using this function
-- and subsequently canceling, since it ensures cancellation.
--
-- See https://github.com/simonmar/async/issues/25 for a perhaps more
-- robust, but also harder to use version of this. The linked version
-- is harder to use because it requires a special version of @cancel@.
asyncLinked :: (U.MonadUnliftIO m) => m () -> m (U.Async ())
asyncLinked action = do
  -- We use 'U.mask' to avoid a race condition between starting the
  -- async and running @action@. Without 'U.mask' here, an async
  -- exception (e.g. via 'U.cancel') could arrive after
  -- @handleUnliftIO@ starts to run but before @action@ starts.
  U.mask $ \restore -> do
  a <- U.async $ handleUnliftIO (\E.ThreadKilled -> return ()) (restore action)
  restore $ do
  U.link a
  return a

-- | A version of 'U.withAsync' that safely links the child. See
-- 'asyncLinked'.
withAsyncLinked :: (U.MonadUnliftIO m) => m () -> (U.Async () -> m a) -> m a
withAsyncLinked child parent = do
  U.mask $ \restore -> do
  U.withAsync (handleUnliftIO (\E.ThreadKilled -> return ()) $ restore child) $ \a -> restore $ do
  U.link a
  parent a

-- A 'U.MonadUnliftIO' version of 'Control.Exception.handle'.
--
-- The 'U.handle' doesn't catch async exceptions, because the
-- @unliftio@ library uses the @safe-execeptions@ library, not
-- @base@, for it exception handling primitives. This is very
-- confusing if you're not expecting it!
handleUnliftIO :: (U.MonadUnliftIO m, U.Exception e)
               => (e -> m a) -> m a -> m a
handleUnliftIO h a = U.withUnliftIO $ \u ->
  E.handle (U.unliftIO u . h) (U.unliftIO u a)

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
