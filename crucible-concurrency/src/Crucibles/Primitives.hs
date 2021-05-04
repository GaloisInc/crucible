{- |
Module           : Crucibles.Primitives
Description      : Interface between source languages and the scheduler
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

This module defines the interface by which source languages teach the scheduler
to recognize relevant events: thread spawns, resource acceses, and the like.

The module also exports an example of this for crucible-syntax programs (via
'crucibleSyntaxPrims').
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Crucibles.Primitives
 ( -- principal API:
   ExplorePrimMatch(..)
 , ExplorePrimitiveMatcher
 , ExplorePrimitives
 , ExplorePrimitive(..)
 , YieldSpec(..)
 , matchPrimitive
 , retrieveTypedArg
 , retrieveType

 -- Evaluating globals
 , findGlobalVar
 , evalGlobalPred

 -- Crucible-syntax primitives:
 , mkExplorePrims
 , crucibleSyntaxPrims
 ) where

import           Control.Applicative
import           Control.Lens.Getter
import           Data.Text (Text)
import qualified Data.Set as S
import qualified Data.Vector as V

import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (fmapFC)

import           What4.Interface
import           What4.ProgramLoc
import           What4.Utils.StringLiteral

import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator
import           Lang.Crucible.Simulator.RegMap
import qualified Lang.Crucible.CFG.Generator as Gen
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.Analysis.Postdom (postdomInfo)
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.Utils.MuxTree (viewMuxTree)
import           What4.FunctionName (FunctionName)
import           Data.Parameterized.Pair
import           Lang.Crucible.Simulator.ExecutionTree (stateGlobals, SomeSimState(..))
import           Data.Maybe (catMaybes)
import           Lang.Crucible.Simulator.GlobalState (lookupGlobal)

-- | A target language needs to provide a list of matchers of this type
newtype ExplorePrimMatch p sym ext = Match { runMatch :: ExplorePrimitiveMatcher p sym ext }

type ExplorePrimitiveMatcher p sym ext =
  forall args blocks ret r.
  [Pair C.TypeRepr GlobalVar] {-^ Program globals in scope -} ->
  FunctionName {-^ The function being called -} ->
  C.CtxRepr args {-^ The arguments passed to the function being called -} ->
  CallFrame sym ext blocks ret args  {-^ The function callframe -} ->
  SomeSimState p sym ext r {-^ The SimState in which the function is being called -} ->
  Maybe (ExplorePrimitive p sym ext)

-- | A list of primitive matchers
type ExplorePrimitives p sym ext = [ExplorePrimMatch p sym ext]


data ExplorePrimitive p sym ext =
    -- | The join primitive, which blocks until the thread with the given ID has
    -- terminated.
    ThreadJoin
      !Int

  -- | A 'yield' indicates an access to some global resource that has some
  -- significance to the scheduler: generally nothing more than a literal read
  -- or write of a variable, a release or acquire of a lock, etc.
  | ThreadYield
      !YieldSpec  -- ^ What caused the yield
      ![Text]     -- ^ The relevant resources
      !Bool       -- ^ True => MUST Read only, False => MAY Write

  -- | The thread has exited with the given value
  | ThreadFinish
      !(C.Some (RegEntry sym))

  -- | A thread is being spawned
  | forall ty retTy spawnRetTy.
    ThreadCreate
      !(C.TypeRepr ty) -- ^ Argument type to new thread
      !(C.TypeRepr retTy) -- ^ Return type of new thread
      !(C.TypeRepr spawnRetTy) -- ^ Value to return to the thread responsible
                               -- for spawning this threadresponsible for
                               -- spawning this thread.
      !(FnHandle (Ctx.EmptyCtx Ctx.::> ty) retTy) -- ^ Handle of the function to spawn
      !(RegValue sym ty) -- ^ The value to pass to the new thread
      !(sym -> Int -> IO (RegValue sym spawnRetTy))

  -- TODO: Fold these into ThreadYield?
  -- | Effectively pthread_cond_wait
  | ThreadCondWait
      !Text -- ^ Condition variable
      !Text -- ^ Mutex

  -- | Effectively pthread_cond_notify
  | ThreadCondSignal
      !Text


-- | A @YieldSpec@ explains how a thread is modifying some global resource. This
-- lets the scheduler decide if the thread should be preempted as well as how
-- and when the thread should be resumed.
data YieldSpec =
    SimpleYield
  | GlobalPred !Text -- ^ Wait for some global (boolean) variable to become True
  | Acquire   !Text -- ^ Acquire a lock
  | Release   !Text -- ^ Release a lock

-- | Run a list of matches in order, stopping with the first success.
matchPrimitive ::
  (IsSymInterface sym) =>
  [ExplorePrimMatch p sym ext] ->
  [Pair C.TypeRepr GlobalVar] ->
  FunctionName ->
  C.CtxRepr args ->
  CallFrame sym ext blocks ret args ->
  SomeSimState p sym ext r ->
  Maybe (ExplorePrimitive p sym ext)
matchPrimitive prims globs fnm args cf st = go prims
  where
    go []         = Nothing
    go (p:prims') = case runMatch p globs fnm args cf st of
                      Just match -> Just match
                      Nothing    -> go prims'


type EffectType          = Ctx.EmptyCtx Ctx.::> C.StringType C.Unicode
type EffectMultiType     = Ctx.EmptyCtx Ctx.::> C.VectorType (C.StringType C.Unicode)
type EffectMultiCondType = Ctx.EmptyCtx
                   Ctx.::> C.StringType C.Unicode {- Global Variable to block on -}
                   Ctx.::> C.VectorType (C.StringType C.Unicode) {- modified resources -}

type RefEffectType   = Ctx.EmptyCtx Ctx.::> C.AnyType

type SpawnType  = Ctx.EmptyCtx Ctx.::> C.FunctionHandleType (Ctx.EmptyCtx Ctx.::> C.AnyType) C.UnitType
                               Ctx.::> C.AnyType
type JoinType   = Ctx.EmptyCtx Ctx.::> C.IntegerType
type CondType   = Ctx.EmptyCtx Ctx.::> C.StringType C.Unicode {- The condition var -}
                               Ctx.::> C.StringType C.Unicode {- The mutex -}
type SignalType = Ctx.EmptyCtx Ctx.::> C.StringType C.Unicode {- The condition var -}

pattern EffectRepr :: () => (EffectType ~ args) => C.CtxRepr args
pattern EffectRepr = Ctx.Empty Ctx.:> C.StringRepr C.UnicodeRepr

pattern EffectMultiRepr :: () => (EffectMultiType ~ args) => C.CtxRepr args
pattern EffectMultiRepr = Ctx.Empty Ctx.:> C.VectorRepr (C.StringRepr C.UnicodeRepr)

pattern EffectMultiCondRepr :: () => (EffectMultiCondType ~ args) => C.CtxRepr args
pattern EffectMultiCondRepr = Ctx.Empty Ctx.:> C.StringRepr C.UnicodeRepr
                                        Ctx.:> C.VectorRepr (C.StringRepr C.UnicodeRepr)

pattern RefEffectRepr :: () => (RefEffectType ~ args) => C.CtxRepr args
pattern RefEffectRepr = Ctx.Empty Ctx.:> C.AnyRepr

pattern SpawnRepr :: () => (SpawnType ~ args) => C.CtxRepr args
pattern SpawnRepr = Ctx.Empty Ctx.:> C.FunctionHandleRepr (Ctx.Empty Ctx.:> C.AnyRepr) C.UnitRepr
                              Ctx.:> C.AnyRepr

pattern CondRepr :: () => (CondType ~ args) => C.CtxRepr args
pattern CondRepr = Ctx.Empty Ctx.:> C.StringRepr C.UnicodeRepr Ctx.:> C.StringRepr C.UnicodeRepr

pattern SignalRepr :: () => (SignalType ~ args) => C.CtxRepr args
pattern SignalRepr = Ctx.Empty Ctx.:> C.StringRepr C.UnicodeRepr

pattern JoinRepr :: () => (JoinType ~ args) => C.CtxRepr args
pattern JoinRepr = Ctx.Empty Ctx.:> C.IntegerRepr

type WaitArgs = Ctx.EmptyCtx Ctx.::> C.StringType C.Unicode Ctx.::> C.StringType C.Unicode

matchJoin :: IsSymInterface sym => ExplorePrimitiveMatcher p sym ext
matchJoin _ "join" JoinRepr cf _ =
  case joinThread cf of
    Just i  -> Just $ ThreadJoin (fromInteger i)
    Nothing -> error "join on symbolic thread ID"
matchJoin _ _ _ _ _ = Nothing

matchYield :: IsSymInterface sym => ExplorePrimitiveMatcher p sym ext
matchYield globals nm args cf (SomeSimState st)
  | nm `elem` ["write_effect", "read_effect"]
  , Just Refl <- testEquality args EffectRepr =
      ThreadYield SimpleYield . pure <$> effectVar cf <*> pure (nm == "read_effect")
  | nm == "write_effect_set"
  , Just Refl <- testEquality args EffectMultiRepr =
      pure $! ThreadYield SimpleYield (S.toList $ effectVarSet cf) False
  | nm == "write_effect_ref"
  , Just Refl <- testEquality args RefEffectRepr =
      let stGlobals = view stateGlobals st
          refCells  = effectPtr cf
          refGlobs  = referencedGlobals stGlobals globals refCells
      in pure $! ThreadYield SimpleYield refGlobs False
  | nm == "write_effect_cond_set"
  , Just Refl  <- testEquality args EffectMultiCondRepr =
      case effectCondPredVar cf of
        Just pr -> pure $! ThreadYield (GlobalPred pr) (S.toList (effectCondVarSet cf)) False
        Nothing -> error "symbolic condition variable"
  | otherwise = Nothing

matchCondWait :: IsSymInterface sym => ExplorePrimitiveMatcher p sym ext
matchCondWait _ nm CondRepr cf _
  | nm == "__cond_wait" =
    case (waitCondVar cf, waitMutVar cf) of
      (Just cv, Just mv) -> pure $! ThreadCondWait cv mv
      _ -> error "cond_wait: symbolic cond/mut resource"
matchCondWait _ _ _ _ _ = Nothing

matchCondSignal :: IsSymInterface sym => ExplorePrimitiveMatcher p sym ext
matchCondSignal _ nm SignalRepr cf _
  | nm == "cond_signal" =
    case effectVar cf of
      Just cv -> pure $! ThreadCondSignal cv
      _ -> error "cond_signal: symbolic cond/mut resource"
matchCondSignal _ _ _ _ _ = Nothing


matchSpawn :: IsSymInterface sym => ExplorePrimitiveMatcher p sym ext
matchSpawn _ nm args cf _
  | nm == "spawn"
  , Just Refl <- testEquality args SpawnRepr
  = case spawnHdl cf of
      HandleFnVal fh ->
        let mkRet sym v = intLit sym (fromIntegral v)
        in pure $! ThreadCreate C.AnyRepr C.UnitRepr C.IntegerRepr fh (spawnArg cf) mkRet
      _ ->
        error "non HandleFnVal arg to spawn"
  | otherwise
  = Nothing

retrieveTypedArg :: C.CtxRepr args -> CallFrame sym ext blocks ret args -> C.TypeRepr tp -> Int -> Maybe (RegValue sym tp)
retrieveTypedArg ctx cf ty intIndex
  | Just (C.Some idx) <- Ctx.intIndex intIndex ctxSize
  , Just Refl         <- testEquality (ctx Ctx.! idx) ty
  = Just (regVal (cf ^. frameRegs) (C.Reg idx))
  | otherwise
  = Nothing
  where
    ctxSize = Ctx.size ctx

retrieveType :: C.CtxRepr args -> Int -> Maybe (C.Some C.TypeRepr)
retrieveType ctx intIndex
  | Just (C.Some idx) <- Ctx.intIndex intIndex ctxSize
  = Just (C.Some (ctx Ctx.! idx))
  | otherwise
  = Nothing
  where
    ctxSize = Ctx.size ctx


retrieveArg :: C.CtxRepr args -> CallFrame sym ext blocks ret args -> Int -> Maybe (C.Some (RegEntry sym))
retrieveArg ctx cf intIndex
  | Just (C.Some idx) <- Ctx.intIndex intIndex ctxSize
  = Just (C.Some (regVal' (cf ^. frameRegs) (C.Reg idx)))
  | otherwise
  = Nothing
  where
    ctxSize = Ctx.size ctx

joinThread ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret JoinType ->
  Maybe Integer
joinThread = asInteger . reg @0 . view frameRegs

effectVar ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret EffectType ->
  Maybe Text
effectVar = fmap fromUnicodeLit . asString . reg @0 . view frameRegs

effectVarSet ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret EffectMultiType ->
  S.Set Text
effectVarSet cf =
  S.fromList [ t | Just t <- toText <$> vec ]
  where
    vec = V.toList $ reg @0 (cf ^. frameRegs)
    toText = fmap fromUnicodeLit . asString

effectCondVarSet ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret EffectMultiCondType ->
  S.Set Text
effectCondVarSet cf =
  S.fromList [ t | Just t <- toText <$> vec ]
  where
    vec = V.toList $ reg @1 (cf ^. frameRegs)
    toText = fmap fromUnicodeLit . asString

effectCondPredVar ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret EffectMultiCondType ->
  Maybe Text
effectCondPredVar =
  fmap fromUnicodeLit . asString . reg @0 . view frameRegs


effectPtr ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret RefEffectType ->
  [C.Some RefCell]
effectPtr cf =
  case reg @0 (cf ^. frameRegs) of
    v | Just ts <- unwrapAny v -> ts
    AnyValue (C.VectorRepr C.AnyRepr) vec
      | Just tss <- sequence (unwrapAny <$> V.toList vec) ->
        concat tss
    _ -> error "effect_ref not applied to a pointer"
  where
    unwrapAny :: AnyValue sym -> Maybe [C.Some RefCell]
    unwrapAny (AnyValue (C.ReferenceRepr _) muxTr) =
      Just (C.Some . fst <$> viewMuxTree muxTr)
    unwrapAny _ = Nothing


waitCondVar ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret CondType ->
  Maybe Text
waitCondVar = fmap fromUnicodeLit . asString . reg @0 . view frameRegs

waitMutVar ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret CondType ->
  Maybe Text
waitMutVar = fmap fromUnicodeLit . asString . reg @1 . view frameRegs

signalCondVar ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret SignalType ->
  Maybe Text
signalCondVar = fmap fromUnicodeLit . asString . reg @0 . view frameRegs

spawnHdl ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret SpawnType ->
  FnVal sym (Ctx.EmptyCtx Ctx.::> C.AnyType) C.UnitType
spawnHdl = reg @0 . view frameRegs

spawnArg ::
  IsSymInterface sym =>
  CallFrame sym ext blocks ret SpawnType ->
  RegValue sym C.AnyType
spawnArg = reg @1 . view frameRegs

crucibleSyntaxPrims ::
  (IsSymInterface sym, IsExprBuilder sym) => ExplorePrimitives p sym ()
crucibleSyntaxPrims =
  [ Match matchJoin
  , Match matchYield
  , Match matchSpawn
  , Match matchCondWait
  , Match matchCondSignal
  ]

referencedGlobals :: SymGlobalState sym -> [Pair C.TypeRepr GlobalVar] -> [Some RefCell] -> [Text]
referencedGlobals gs globs refs =
  catMaybes
  [ case testEquality tp (refType rc) of
      Just Refl
        | referencesGlobal gs gv rc -> Just $ globalName gv
      _ -> Nothing
  | Pair (C.ReferenceRepr tp) gv <- globs, C.Some rc <- refs ]

referencesGlobal :: SymGlobalState sym -> GlobalVar (C.ReferenceType a) -> RefCell a -> Bool
referencesGlobal gs gv ref =
  case lookupGlobal gv gs of
    Just ref' -> ref `elem` (fst <$> viewMuxTree ref')
    Nothing -> False

findGlobalVar :: [Pair C.TypeRepr GlobalVar] -> Text -> C.TypeRepr ty -> Maybe (GlobalVar ty)
findGlobalVar globals gvName gvType =
  case matches of
    Pair ty gv:_
      | Just Refl <- testEquality gvType ty ->
          Just gv
    _   -> Nothing
  where
    matches =
      [ Pair ty gv | Pair ty gv <- globals
                   , globalName gv == gvName ]

evalGlobalPred ::
  IsSymInterface sym =>
  GlobalVar C.BoolType ->
  SymGlobalState sym ->
  Bool
evalGlobalPred gv st =
  case lookupGlobal gv st of
    Just ref | Just t <- asConstantPred ref -> t
             | otherwise -> error $ "TODO: symbolic global pred"
    Nothing -> error $ "Global " ++ show (globalName gv) ++ " not found."


nullDefinition ::
  (Monad m, IsSyntaxExtension ext) =>
  C.Some (NonceGenerator m) ->
  FnHandle init C.UnitType -> m (Gen.SomeCFG ext init C.UnitType)
nullDefinition ng fh =
  fst <$> Gen.defineFunction InternalPos ng fh def
  where
    def _ = (Const (), Gen.returnFromFunction (Gen.App EmptyApp))


condWaitDefinition ::
  (Monad m, IsSyntaxExtension ext) =>
  C.Some (NonceGenerator m) ->
  Bool ->
  FnHandle WaitArgs C.UnitType ->
  FnHandle WaitArgs C.UnitType ->
  m (Gen.SomeCFG ext WaitArgs C.UnitType)
condWaitDefinition ng pedantic fh fhInternal =
  fst <$> Gen.defineFunction InternalPos ng fh (condDefinition pedantic fhInternal)

condDefinition ::
  (Monad m, IsSyntaxExtension ext) =>
  Bool ->
  FnHandle WaitArgs C.UnitType ->
  Gen.FunctionDef ext (Const ()) WaitArgs C.UnitType m
condDefinition pedantic fhInternal args
  | not pedantic =
    ( Const ()
    , do _ <- Gen.call (Gen.App (HandleLit fhInternal)) (fmapFC Gen.AtomExpr args)
         Gen.returnFromFunction (Gen.App EmptyApp)
    )
  -- This allows spurious wakeups that are not triggered by a signal
  | otherwise =
    ( Const ()
    , do l1 <- Gen.defineBlockLabel $
           do _ <- Gen.call (Gen.App (HandleLit fhInternal)) (fmapFC Gen.AtomExpr args)
              Gen.returnFromFunction (Gen.App EmptyApp)

         l2 <- Gen.defineBlockLabel $
           Gen.returnFromFunction (Gen.App EmptyApp)

         v <- Gen.mkFresh C.BaseBoolRepr Nothing
         Gen.branch (Gen.AtomExpr v) l1 l2
    )

mkPrimDef ::
  IsSyntaxExtension ext =>
  HandleAllocator ->
  FunctionName ->
  C.CtxRepr args ->
  C.TypeRepr ret ->
  (FnHandle args ret -> IO (Gen.SomeCFG ext args ret)) ->
  IO (FnHandle args ret, FnBinding p sym ext)
mkPrimDef ha nm args retTy mkDef =
  do handle <- mkHandle' ha nm args retTy
     def    <- mkBinding <$> mkDef handle
     return (handle, def)
  where
    mkBinding (Gen.SomeCFG g) =
      case toSSA g of
        C.SomeCFG ssa ->
          FnBinding (Gen.cfgHandle g) (UseCFG ssa (postdomInfo ssa))


mkExplorePrims ::
  IsSyntaxExtension ext =>
  HandleAllocator -> Bool -> C.Some (NonceGenerator IO) -> IO [FnBinding p sym ext]
mkExplorePrims ha pedantic ng =
  do -- These do not do anything interesting
     notifyDef        <- snd <$> mkNull "cond_signal" SignalRepr
     writeDef         <- snd <$> mkNull "write_effect" EffectRepr
     writeRefDef      <- snd <$> mkNull "write_effect_ref" RefEffectRepr
     writeManyDef     <- snd <$> mkNull "write_effect_set" EffectMultiRepr
     writeManyCondDef <- snd <$> mkNull "write_effect_cond_set" EffectMultiCondRepr
     readDef          <- snd <$> mkNull "read_effect" EffectRepr
     joinDef          <- snd <$> mkNull "join" JoinRepr

     spawnDef     <- snd <$> mkPrimDef ha "spawn" SpawnRepr C.IntegerRepr mkSpawnDefinition

     (waitHandleInternal, waitIntDef) <- mkNull "__cond_wait" CondRepr

     (_ , waitDef)  <-
       mkPrimDef ha "cond_wait" CondRepr C.UnitRepr $ \waitHandle ->
         condWaitDefinition ng pedantic waitHandle waitHandleInternal

     return [ spawnDef
            , writeDef
            , writeRefDef
            , readDef
            , joinDef
            , waitIntDef
            , waitDef
            , notifyDef
            , writeManyDef
            , writeManyCondDef
            ]
  where
    mkNull :: IsSyntaxExtension ext => FunctionName -> C.CtxRepr args -> IO (FnHandle args C.UnitType, FnBinding p sym ext)
    mkNull nm args =
      mkPrimDef ha nm args C.UnitRepr $ nullDefinition ng

    mkSpawnDefinition fh =
      fst <$> Gen.defineFunction InternalPos ng fh def
      where
        def _ = (Const (), Gen.returnFromFunction (Gen.App (IntLit 0)))
