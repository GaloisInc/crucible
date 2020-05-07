---------------------------------------------------------------------------
-- |
-- Module          : Lang.Crucible.CFG.ExtractSubgraph
-- Description     : Allows for construction of a function based off a subgraph
--                   of an SSA-form function, subject to certain constraints
-- Copyright       : (c) Galois, Inc 2015
-- License         : BSD3
--
---------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.CFG.ExtractSubgraph
  ( extractSubgraph
  ) where

import           Control.Lens
import qualified Data.Bimap as Bimap
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map as MapF
import           Data.Set as S
import qualified Data.Map as Map
import           Debug.Trace

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.ProgramLoc

-- | Given a CFG @cfg@, a set of blocks @cuts@ that take the return type as their sole
-- argument, and a block @bi@ that takes the CFG's init type as its sole argument,
-- construct a CFG that is a maximal subgraph starting at @bi@ and not entering any
-- block in @cuts@.  If the original graph would enter a block in @cuts@, the value
-- passed to that block is returned.  If @bi `member` cuts@, then whenever the subgraph
-- would transition to @bi@, it returns the value that would be passed to @bi@ instead.
extractSubgraph :: (KnownCtx TypeRepr init, KnownRepr TypeRepr ret)
                => CFG ext blocks init ret
                -> Set (BlockID blocks (EmptyCtx ::> ret))
                -> BlockID blocks init
                -> HandleAllocator
                -> IO (Maybe (SomeCFG ext init ret))
extractSubgraph (CFG{cfgBlockMap = orig, cfgBreakpoints = breakpoints}) cuts bi halloc =
  extractSubgraphFirst orig cuts MapF.empty zeroSize bi $
    \(SubgraphIntermediate finalMap finalInitMap _sz entryID cb) -> do
        hn <- mkHandle halloc startFunctionName
        return $ do
          bm <- cb finalMap finalInitMap Ctx.empty
          return $ SomeCFG $ CFG
            { cfgBlockMap = bm
            , cfgEntryBlockID = entryID
            , cfgHandle = hn
            , cfgBreakpoints = Bimap.fromList $ Map.toList $
                Map.mapMaybe (viewSome $ \bid -> Some <$> MapF.lookup bid finalMap) $
                Bimap.toMap breakpoints
            }

-- | Type for carrying intermediate results through subraph extraction
-- the interesting field is the final one - it holds a callback for transforming
-- the result of the previous portion of the subgraph extraction into the result
-- of this subgraph extraction.
data SubgraphIntermediate ext old ret init soFar new where
  SubgraphIntermediate :: MapF (BlockID old) (BlockID new)
                       -> MapF (BlockID old) (BlockID new)
                       -> Size new
                       -> BlockID new init
                       -> (forall all. (MapF (BlockID old) (BlockID all)
                                        -> MapF (BlockID old) (BlockID all)
                                        -> Assignment (Block ext all ret) soFar
                                        -> Maybe (Assignment (Block ext all ret) new)))
                       -> SubgraphIntermediate ext old ret init soFar new


-- | The inner loop of subgraph extraction
--   produces a callback with an existential type, in order to hide new
extractSubgraph' :: KnownRepr TypeRepr ret
                 => BlockMap ext old ret
                 -> Set (BlockID old (EmptyCtx ::> ret))
                 -> MapF (BlockID old) (BlockID soFar)
                 -> MapF (BlockID old) (BlockID soFar)
                 -> Size soFar
                 -> BlockID old init
                 -> BlockID soFar args
                 -> forall r . (forall new. SubgraphIntermediate ext old ret args soFar new -> r)
                 -> r
extractSubgraph' orig cuts mapF initMap sz bi ident f =
  let block = getBlock bi orig
  in  withBlockTermStmt block $ (\_ t ->
        (case t of
          Jump (JumpTarget bi' _ _) -> \sgi -> visitChildNode orig cuts bi' sgi f
          Br _ (JumpTarget bi1 _ _) (JumpTarget bi2 _ _) -> \sgi1 ->
            visitChildNode orig cuts bi1 sgi1
              $ \sgi2 -> visitChildNode orig cuts bi2 sgi2 f
          Return _ -> f
          _ -> error "extractSubgraph': unexpected case!")
                (SubgraphIntermediate
                  (MapF.insert bi (BlockID $ nextIndex sz) (MapF.map extendBlockID mapF))
                  (MapF.map extendBlockID initMap)
                  (incSize sz)
                  (extendBlockID ident)
                  (\finalMap _finalInitMap assn ->
                    fmap (extend assn) (do
                      finalID <- MapF.lookup bi finalMap
                      cloneBlock finalMap finalID block))))

-- code duplication... but the types need to be different between iterations
-- FIXME: write a generic version that this and extractSubgraph' can be wrappers
-- around
extractSubgraphFirst :: KnownRepr TypeRepr ret
                     => BlockMap ext old ret
                     -> Set (BlockID old (EmptyCtx ::> ret))
                     -> MapF (BlockID old) (BlockID soFar)
                     -> Size soFar
                     -> BlockID old init
                     -> forall r . (forall new. SubgraphIntermediate ext old ret init soFar new -> r)
                     -> r
extractSubgraphFirst orig cuts mapF sz bi f =
  let block = getBlock bi orig
  in  withBlockTermStmt block $ (\_ t ->
        (case t of
          Jump (JumpTarget bi' _ _) -> \sgi -> visitChildNode orig cuts bi' sgi f
          Br _ (JumpTarget bi1 _ _) (JumpTarget bi2 _ _) -> \sgi1 ->
            visitChildNode orig cuts bi1 sgi1
              $ \sgi2 -> visitChildNode orig cuts bi2 sgi2 f
          Return _ -> f
          _ -> error "extractSubgraphFirst: unexpected case!")
                (SubgraphIntermediate
                  (if case S.minView cuts of
                      Just (bi', _) -> case testEquality (blockInputs block) (blockInputs $ orig Ctx.! blockIDIndex bi') of
                        Just Refl -> bi `S.member` cuts
                        Nothing -> False
                      Nothing -> False
                    then MapF.map extendBlockID mapF
                    else MapF.insert bi (BlockID $ nextIndex sz) (MapF.map extendBlockID mapF))
                  (MapF.insert bi (BlockID $ nextIndex sz) (MapF.map extendBlockID mapF))
                  (incSize sz)
                  (BlockID $ nextIndex sz)
                  (\finalMap finalInitMap assn -> fmap (extend assn) (do
                      finalID <- MapF.lookup bi finalInitMap
                      cloneBlock finalMap finalID block))))

-- does the building of a new node - mutually recursive with exrtactSubgraph'
visitChildNode :: KnownRepr TypeRepr ret
               => BlockMap ext old ret
               -> Set (BlockID old (EmptyCtx ::> ret))
               -> BlockID old init
               -> SubgraphIntermediate ext old ret args soFar prev
               -> (forall r. (forall new . SubgraphIntermediate ext old ret args soFar new -> r)
               -> r)
visitChildNode orig cuts bi (SubgraphIntermediate sgMap initMap sz ident cb) f=
  case MapF.lookup bi sgMap of
    Just _bi' -> f $ SubgraphIntermediate sgMap initMap sz ident cb
    Nothing -> case S.minView cuts of
      Just (cut, _)
        | Just Refl <- testEquality (blockInputs $ orig Ctx.! blockIDIndex bi) (blockInputs $ orig Ctx.! blockIDIndex cut)
        , S.member bi cuts ->
            f $ SubgraphIntermediate
              (MapF.insert bi (BlockID $ nextIndex sz) (MapF.map extendBlockID sgMap))
              (MapF.map extendBlockID initMap)
              (incSize sz)
              (extendBlockID ident)
              (\finalMap finalCutMap assn -> do
                assn' <- cb finalMap finalCutMap assn
                newBlock <- mkRetBlock finalMap orig bi
                return $ extend assn' newBlock)
      _ -> extractSubgraph' orig cuts sgMap initMap sz bi ident
            (\ (SubgraphIntermediate sgMap' initMap' sz' ident' ccb) ->
              f $ SubgraphIntermediate sgMap' initMap' sz' ident'
                (\finalMap finalCutMap assn ->
                  ccb finalMap finalCutMap  =<< cb finalMap finalCutMap assn))


mkRetBlock :: MapF (BlockID old) (BlockID new)
           -> BlockMap ext old ret
           -> BlockID old (EmptyCtx ::> ret)
           -> Maybe (Block ext new ret (EmptyCtx ::> ret))
mkRetBlock mapF bm ident =
  case MapF.lookup ident mapF of
    Just id' ->
      let block = bm Ctx.! blockIDIndex ident
      in Just $
           let name = plFunction (blockLoc block)
               term = Return lastReg
              in Block{ blockID       = id'
                      , blockInputs   = blockInputs block
                      , _blockStmts   = TermStmt (mkProgramLoc name InternalPos) term
                      }
    Nothing -> trace ("could not lookup return block id " ++ show (blockIDIndex ident)) Nothing


cloneBlock :: MapF (BlockID old) (BlockID new)
           -> BlockID new ctx -> Block ext old ret ctx -> Maybe (Block ext new ret ctx)
cloneBlock mapF newID b = do
  stmts' <- cloneStmtSeq mapF (b^.blockStmts)
  return Block{ blockID       = newID
              , blockInputs   = blockInputs b
              , _blockStmts   = stmts'
              }

cloneStmtSeq :: MapF (BlockID old) (BlockID new) -> StmtSeq ext old ret ctx -> Maybe (StmtSeq ext new ret ctx)
cloneStmtSeq mapF (ConsStmt loc stmt rest) = do
  rest' <- cloneStmtSeq mapF rest
  return $ ConsStmt loc stmt rest'
cloneStmtSeq mapF (TermStmt loc term) = do
  term' <- cloneTerm mapF term
  return $ TermStmt loc term'

cloneTerm :: MapF (BlockID old) (BlockID new) -> TermStmt old ret ctx -> Maybe (TermStmt new ret ctx)
cloneTerm mapF (Jump jt) = fmap Jump $ cloneJumpTarget mapF jt
cloneTerm mapF (Br reg jt1 jt2) = do
  jt1' <- cloneJumpTarget mapF jt1
  jt2' <- cloneJumpTarget mapF jt2
  return $ Br reg jt1' jt2'
cloneTerm _mapF (Return reg) = Just $ Return reg
cloneTerm _ _ = error "cloneTerm: unexpected case!"

cloneJumpTarget :: MapF (BlockID blocks1) (BlockID blocks2)
                -> JumpTarget blocks1 t
                -> Maybe (JumpTarget blocks2 t)
cloneJumpTarget mapF (JumpTarget ident args assn) = do
  case MapF.lookup ident mapF of
    Just id' -> Just $ JumpTarget id' args assn
    Nothing -> trace ("could not lookup jump target id " ++ show (blockIDIndex ident)) Nothing
