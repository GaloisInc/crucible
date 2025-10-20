{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
module Mir.Concurrency where

import           Control.Lens
import qualified Data.BitVector.Sized as BV
import qualified Data.Text as Text

import qualified Data.Parameterized.Context            as Ctx

-- crucible
import qualified Lang.Crucible.Simulator.CallFrame     as C
import qualified Lang.Crucible.Simulator.RegMap        as C
import qualified Lang.Crucible.CFG.Core                as C
import qualified Lang.Crucible.FunctionHandle          as C
import qualified Lang.Crucible.Backend                 as C

-- what4
import qualified What4.Interface                       as W4
import qualified What4.FunctionName                    as W4

-- crucible-concurrency
import           Crucibles.Primitives

import           Mir.Intrinsics ( MIR
                                , pattern MirReferenceRepr
                                , MirReferenceMux(..)
                                , MirReference(..)
                                , MirReferencePath(..) )
import           Mir.FancyMuxTree (viewFancyMuxTree)
import           Mir.DefId (textId, getTraitName, DefId)
import Data.Parameterized.Context (indexVal)

mirExplorePrimitives ::
  (C.IsSymInterface sym, W4.IsExprBuilder sym) => ExplorePrimitives p sym MIR
mirExplorePrimitives =
  [ Match mirLock
  , Match mirAtomic
  , Match mirJoin
  , Match mirSpawn
  , Match mirExit
  ]

mirJoin :: C.IsSymInterface sym => ExplorePrimitiveMatcher p sym MIR
mirJoin _ nm args cf _
  | matchGeneric "core::crucible::concurrency::join" nm
  = do bv <- retrieveTypedArg args cf (C.BVRepr (W4.knownNat @64)) 0
       case W4.asBV bv of
         Just (BV.BV i) -> pure $! ThreadJoin (fromIntegral i)
         Nothing        -> error "crucible_join: symbolic thread ID"
  | otherwise = Nothing

mirAtomic :: C.IsSymInterface sym => ExplorePrimitiveMatcher p sym MIR
mirAtomic _ nm ctx cf _
  | matchGeneric "core::crucible::concurrency::sched_yield" nm
  , Ctx.Empty Ctx.:> C.BoolRepr Ctx.:> MirReferenceRepr <- ctx
  = do isRO <- W4.asConstantPred =<< retrieveTypedArg ctx cf C.BoolRepr 0
       tr   <- retrieveTypedArg ctx cf MirReferenceRepr 1
       let refs = mirRefName tr
       pure $! ThreadYield SimpleYield refs isRO
  | otherwise = Nothing

mirLock :: C.IsSymInterface sym => ExplorePrimitiveMatcher p sym MIR
mirLock _ nm ctx cf _
  | matchGeneric "core::crucible::concurrency::mutex_lock" nm
  , Ctx.Empty Ctx.:> MirReferenceRepr <- ctx
  = do arg <- retrieveTypedArg ctx cf MirReferenceRepr 0
       let refs = mirRefName arg
       case refs of
         [ref] ->
           pure $! ThreadYield (Acquire ref) refs False
         _ -> error "TODO: Muxed mutex lock"
  | matchGeneric "core::crucible::concurrency::mutex_unlock" nm
  , Ctx.Empty Ctx.:> MirReferenceRepr <- ctx
  = do arg <- retrieveTypedArg ctx cf MirReferenceRepr 0
       let refs = mirRefName arg
       case refs of
         [ref] ->
           pure $! ThreadYield (Release ref) refs False
         _ -> error "TODO: Muxed mutex unlock"
  | otherwise = Nothing

mutexName :: BV.BV 32 -> Text.Text
mutexName bv = Text.pack ("resource-" ++ show bv)

mirSpawn :: C.IsSymInterface sym => ExplorePrimitiveMatcher p sym MIR
mirSpawn _ nm ctx cf@C.CallFrame { C._frameCFG = cfg } _
  | matchGeneric "core::crucible::concurrency::spawn_internal" nm =
  -- We use this as both the spawned thread and the function that returns the
  -- spawned thread's ID. See the note in our libstd/thread/mod.rs
    do C.Some ty <- retrieveType ctx 0
       arg       <- retrieveTypedArg ctx cf ty 0
       let hdl    = C.cfgHandle cfg
           tpr    = C.BVRepr (W4.knownNat @32)
           mkRet sym v = W4.bvLit sym W4.knownRepr (BV.mkBV BV.knownNat (fromIntegral v))
       let check = ( W4.testEquality ctx (Ctx.Empty Ctx.:> ty)
                   , W4.testEquality (C.handleArgTypes hdl) ctx
                   , W4.testEquality (C.handleReturnType hdl) tpr
                   )
       case check of
         (Just Refl, Just Refl, Just Refl) ->
           return $ ThreadCreate ty tpr tpr hdl arg mkRet
         _ ->
           error $ "crucible_spawn_internal: unexpected signature "
                ++ show (ctx, C.handleArgTypes hdl, C.handleReturnType hdl)
  | otherwise = Nothing

mirExit :: C.IsSymInterface sym => ExplorePrimitiveMatcher p sym MIR
mirExit _ nm ctx cf _
  | matchGeneric "core::crucible::concurrency::spawn::thread_exit" nm =
    do (C.Some idx) <- Ctx.intIndex 0 (Ctx.size ctx)
       return $ ThreadFinish $ C.Some (C.regVal' (cf ^. C.frameRegs) (C.Reg idx))
  | otherwise
  = Nothing

mirRefName :: C.IsSymInterface sym => MirReferenceMux sym -> [Text.Text]
mirRefName t =
  case t of
    MirReferenceMux tree ->
       let refs = fst <$> viewFancyMuxTree tree
           extr r =
             case r of
               MirReference _ root p ->
                 Text.pack (show root ++ mirPathName p)
               -- If std::sys::crux::Mutex becomes zero sized, then we might
               -- actually hit this case, as the compiler will be free to choose
               -- any integer to serve as an address. We can probably just get
               -- away with using this intger as the address, but the results might be
               -- strange if distinct mutexes are assigned the same address.
               MirReference_Integer {} ->
                 error "Unexpected MirReference_Integer in mirRefName"
       in (extr <$> refs)

mirPathName :: C.IsSymInterface sym => MirReferencePath sym tpr t -> String
mirPathName p =
  case p of
    Empty_RefPath -> ""
    Field_RefPath _ p' idx -> mirPathName p' ++ "." ++ show (indexVal idx)
    Variant_RefPath _ _ p' idx -> mirPathName p' ++ "." ++ show (indexVal idx)
    Index_RefPath _ p' _ -> mirPathName p'
    Just_RefPath _ p' -> mirPathName p'
    VectorAsMirVector_RefPath _ p' -> mirPathName p'
    ArrayAsMirVector_RefPath _ p' -> mirPathName p'
    AgElem_RefPath _ _ _ p' -> mirPathName p'

-- | Match a the name of a polymorphic method with a possible instance by
-- dropping the last segment
matchGeneric :: DefId -> W4.FunctionName -> Bool
matchGeneric poly instNm =
  getTraitName (textId (W4.functionName instNm)) == poly
