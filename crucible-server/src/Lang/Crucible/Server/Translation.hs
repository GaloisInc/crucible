-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.Translations
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Operations for translating between the protocol-buffer representations
-- and the internal Crucible representations of control-flow graphs.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.Server.Translation
  ( unpackCFG
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Lens
import           Control.Monad
import qualified Data.Foldable as Fold
import qualified Control.Monad.Catch as X
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Map as Map
import           Data.IORef
import           Data.Maybe
import Data.Parameterized.Nonce ( Nonce, NonceGenerator
                                , freshNonce, newIONonceGenerator )
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Data.Parameterized.Context as Ctx


import           Data.HPB
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import           What4.ProgramLoc
import           What4.Utils.StringLiteral

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.CFG.Reg as R
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import           Lang.Crucible.Types
import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Server.ValueConv
import           Lang.Crucible.Server.Encoding
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.TypeConv

------------------------------------------------------------------------
-- UseCFG request

newtype Gen s (ret :: CrucibleType) a =
  Gen { unGen :: ReaderT (NonceGenerator IO s) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadFail
           )

newAtomIdx :: Gen s ret (Nonce s (tp :: CrucibleType))
newAtomIdx = do
  ng <- Gen $ ask
  Gen $ lift (freshNonce ng)

genBlockID :: P.Block -- ^ Block to generate label for.
           -> Gen s ret (R.BlockID s)
genBlockID b
  | b^.P.block_is_lambda = do
     Some tp <- fromProtoType (b^.P.block_lambda_type)
     idx <- newAtomIdx
     r_idx <- newAtomIdx
     let a = R.Atom { R.atomPosition = plSourceLoc $ fromProtoPos (b^.P.block_pos)
                    , R.atomId = r_idx
                    , R.atomSource = R.LambdaArg l
                    , R.typeOfAtom = tp
--                    , R.regSource = R.LambdaArg l
--                    , R.typeOfReg = tp
                    }
         l = R.LambdaLabel idx a
     return $ R.LambdaID l
  | otherwise = R.LabelID . R.Label <$> newAtomIdx

type RegVector s = V.Vector (Some (R.Reg s))
type StmtResultMap s = Map.Map (Word64, Word64) (Some (R.Atom s))

-- | Get type of result returned by statement.
genStmtResultType :: RegVector s -> P.Statement -> Gen s ret (Maybe (Some TypeRepr))
genStmtResultType rv s =
  case s^.P.statement_code of
    P.ExecPrimitive -> do
      Just <$> fromProtoType (s^.P.statement_result_type)
    P.Call -> do
      Just <$> fromProtoType (s^.P.statement_result_type)
    P.Print  -> return Nothing
    P.Assert -> return Nothing
    P.ReadReg -> do
      case rv V.!? fromIntegral (s^.P.statement_reg) of
        Just (Some r) -> return $ Just $ Some (R.typeOfReg r)
        Nothing -> fail $ "Read reg given illegal index."
    P.WriteReg -> do
      return Nothing
    -- TODO: Support globals
    _ -> fail $ "Could not interpret statement."

mkStmtResultMap :: forall s ret . RegVector s -> [P.Block] -> Gen s ret (StmtResultMap s)
mkStmtResultMap rv blocks = do
  let mkStmtResult :: Word64
                   -> Word64
                   -> P.Statement
                   -> Gen s ret (Maybe ((Word64, Word64),Some (R.Atom s)))
      mkStmtResult block_idx stmt_idx s = do
        mtp <- genStmtResultType rv s
        case mtp of
          Nothing -> return Nothing
          Just (Some tp) -> do
            r_idx <- newAtomIdx
            let a = R.Atom { R.atomPosition = plSourceLoc $ fromProtoPos (s^.P.statement_pos)
                           , R.atomId     = r_idx
                           , R.atomSource = R.Assigned
                           , R.typeOfAtom = tp
                           }
            return $ Just ((block_idx, stmt_idx), Some a)

      f :: Word64 -> P.Block -> Gen s ret [((Word64, Word64),Some (R.Atom s))]
      f block_idx b = do
        let stmts = Fold.toList (b^.P.block_statements)
        catMaybes <$> zipWithM (mkStmtResult block_idx) [0..] stmts
  Map.fromList . concat <$> zipWithM f [0..] blocks

------------------------------------------------------------------------
-- Translation

data TransState s = TransState { blockLabelMap :: !(Map.Map Word64 (R.BlockID s))
                               , handleMap :: !(Map.Map Word64 SomeHandle)
                               , argVec :: !(V.Vector (Some (R.Atom s)))
                               , regVec :: !(V.Vector (Some (R.Reg s)))
                               , nonceGen :: NonceGenerator IO s
                               , stmtResultMap :: !(StmtResultMap s)
                               }

newtype Trans s (ret :: CrucibleType) a = Trans { unTrans :: StateT (TransState s) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadFail
           , MonadState (TransState s)
           , X.MonadThrow
           , MonadIO
           )

getBlockID :: Word64 -> Trans s ret (R.BlockID s)
getBlockID w = do
   m <- gets blockLabelMap
   case Map.lookup w m of
     Nothing -> fail $ "Illegal block index: " ++ show w
     Just b -> return b

getBlockLabel :: Word64 -> Trans s ret (R.Label s)
getBlockLabel w = do
  b <- getBlockID w
  case b of
    R.LabelID l -> return l
    R.LambdaID{} -> fail $ "Block label refers to lambda."

getLambdaLabel :: Word64 -> TypeRepr tp -> Trans s ret (R.LambdaLabel s tp)
getLambdaLabel w tp = do
  b <- getBlockID w
  case b of
    R.LabelID{} -> fail $ "Lambda label refers to block."
    R.LambdaID l -> do
      case testEquality (R.typeOfAtom (R.lambdaAtom l)) tp of
        Just Refl -> return l
        Nothing -> fail $ "Lambda label has incorrect type."

getFnArg :: Word64 -- ^ Index of argument
         -> Trans s ret (Some (R.Atom s))
getFnArg arg_idx = do
  v <- gets argVec
  case v V.!? fromIntegral arg_idx of
    Nothing -> fail $ "Could not find argument at " ++ show arg_idx ++ "."
    Just e -> return e

getLambdaArg :: Word64 -- ^ Index of block
             -> Trans s ret (Some (R.Atom s))
getLambdaArg block_idx = do
  b <- getBlockID block_idx
  case b of
    R.LabelID{} -> fail $ "Lambda arg refers to block."
    R.LambdaID l -> return (Some (R.lambdaAtom l))

getReg :: Word64 -> Trans s ret (Some (R.Reg s))
getReg reg_idx = do
  v <- gets regVec
  case v V.!? fromIntegral reg_idx of
    Nothing -> fail $ "Could not find register at " ++ show reg_idx ++ "."
    Just r -> return r

getStmtResult :: Word64 -> Word64 -> Trans s ret (Some (R.Atom s))
getStmtResult block_idx stmt_idx = do
  m <- gets stmtResultMap
  case Map.lookup (block_idx, stmt_idx) m of
    Nothing -> do
      fail $ "Could not find statement at " ++ show (block_idx, stmt_idx) ++ "."
    Just r -> return r

getRegWithType :: Word64 -> TypeRepr tp -> Trans s ret (R.Reg s tp)
getRegWithType w tp = do
  Some r <- getReg w
  case testEquality (R.typeOfReg r) tp of
    Just Refl -> return r
    Nothing -> fail $ "Register does not match type."

getStmtResultWithType :: Word64 -> Word64 -> TypeRepr tp -> Trans s ret (R.Atom s tp)
getStmtResultWithType block_idx stmt_idx tp = do
  Some r <- getStmtResult block_idx stmt_idx
  case testEquality (R.typeOfAtom r) tp of
    Just Refl -> return r
    Nothing -> fail $ "Statement result does not match type."

transNatExpr :: MonadFail m => P.Expr -> m (Some NatRepr)
transNatExpr pe = do
  case pe^.P.expr_code of
    P.NatExpr -> do
      let i = decodeUnsigned (pe^.P.expr_data)
      case someNat i of
        Just rep -> return rep
        Nothing -> fail "improper nat value in parseNatRepr"
    _ -> fail "expected Nat value in parseNatRepr"


data BlockState s = BlockState { blockPos :: !Position
                               , blockStmts :: ![Posd (R.Stmt () s)]
                               }

type StmtTrans s r = StateT (BlockState s) (Trans s r)

setPos :: Position -> StmtTrans s r ()
setPos p = do
  s <- get
  put $! s { blockPos = p }

addStmt :: R.Stmt () s -> StmtTrans s r ()
addStmt stmt = seq stmt $ do
  s <- get
  let pstmt = Posd (blockPos s) stmt
  seq pstmt $ do
  let l = pstmt : blockStmts s
  put $! s { blockStmts = l }

addAppStmt :: App () (R.Atom s) tp -> StmtTrans s r (R.Atom s tp)
addAppStmt app = do
  ng <- lift $ gets nonceGen
  i <- liftIO $ freshNonce ng
  p <- gets blockPos
  let a = R.Atom { R.atomPosition = p
                 , R.atomId = i
                 , R.atomSource = R.Assigned
                 , R.typeOfAtom = appType app
                 }
  addStmt $ R.DefineAtom a (R.EvalApp app)
  return $! a

-- | Translate a protocol buffer expression into either a constant or a known atom.
transExpr :: P.Expr -> StmtTrans s ret (Some (R.Atom s))
transExpr pe = do
  case pe^.P.expr_code of
    P.TrueExpr -> do
      fmap Some $ addAppStmt $ BoolLit True
    P.FalseExpr -> do
      fmap Some $ addAppStmt $ BoolLit False
    P.NatExpr -> do
      let i = decodeUnsigned (pe^.P.expr_data)
      fmap Some $ addAppStmt $ NatLit (fromInteger i)
    P.IntegerExpr -> do
      let i = decodeSigned (pe^.P.expr_data)
      fmap Some $ addAppStmt $ IntLit i
    P.RationalExpr -> do
      r <- decodeRational (pe^.P.expr_data)
      fmap Some $ addAppStmt $ RationalLit r
    P.BitvectorExpr -> do
      case someNat (toInteger (pe^.P.expr_width)) of
        Just (Some w) -> do
          case isPosNat w of
            Nothing -> fail $ "Zero width bitvector."
            Just LeqProof -> do
              let i = decodeSigned (pe^.P.expr_data)
              fmap Some $ addAppStmt $ BVLit w (BV.mkBV w i)
        Nothing -> fail "Width is too large"
    P.StringExpr -> do
      let s = pe^.P.expr_string_lit
      fmap Some $ addAppStmt $ StringLit $ UnicodeLiteral s
    P.UnitExpr -> do
      fmap Some $ addAppStmt $ EmptyApp
    P.FnHandleExpr -> do
      m <- lift $ gets handleMap
      let idx = pe^.P.expr_index
      case Map.lookup idx m of
        Just (SomeHandle h) ->
          fmap Some $ addAppStmt $ HandleLit h
        Nothing -> fail $ "Could not find handle with index " ++ show idx ++ "."
    P.FunctionArgExpr -> do
      lift $ getFnArg (pe^.P.expr_index)
    P.LambdaArgExpr -> do
      lift $ getLambdaArg (pe^.P.expr_block_id)
    P.StatementResultExpr -> do
      lift $ getStmtResult (pe^.P.expr_block_id) (pe^.P.expr_index)
    P.UnknownExpr -> fail $ "Could not parse expression."

transExprWithType :: P.Expr
                  -> TypeRepr tp
                  -> StmtTrans s ret (R.Atom s tp)
transExprWithType pe tp = do
  Some a <- transExpr pe
  case testEquality (R.typeOfAtom a) tp of
    Just Refl -> return a
    Nothing -> fail "Expression does not match expected type."

transExprSeqWithTypes :: Seq P.Expr
                      -> CtxRepr ctx
                      -> StmtTrans s ret (Ctx.Assignment (R.Atom s) ctx)
transExprSeqWithTypes s0 c0 =
  case Ctx.viewAssign c0 of
    Ctx.AssignEmpty -> do
      when (not (Seq.null s0)) $ do
        fail $ "More expressions than expected."
      return $ Ctx.empty
    Ctx.AssignExtend c tp -> do
      case Seq.viewr s0 of
        Seq.EmptyR -> fail $ "Fewer expressions than expected."
        s Seq.:> pe -> do
          (Ctx.:>) <$> transExprSeqWithTypes s c
                   <*> transExprWithType pe tp

------------------------------------------------------------------------

transStmt :: Word64 -- ^ Index of block
          -> Word64 -- ^ Index of statement
          -> P.Statement
          -> StmtTrans s ret ()
transStmt block_idx stmt_idx s = do
  setPos (plSourceLoc (fromProtoPos (s^.P.statement_pos)))
  let exprs  = s^.P.statement_exprs
  case (s^.P.statement_code, Fold.toList exprs) of
    (P.ExecPrimitive, _) -> do
      let prim_op = s^.P.statement_prim_op
      let res_type = s^.P.statement_result_type
      Some a <- convertToCrucibleApp transExpr transNatExpr prim_op exprs res_type
      res <- lift $ getStmtResultWithType block_idx stmt_idx (appType a)
      addStmt $ R.DefineAtom res (R.EvalApp a)
    (P.Call,  pf:pargs) -> do
      Some f <- transExpr pf
      case R.typeOfAtom f of
        FunctionHandleRepr argTypes ret -> do
          args <- transExprSeqWithTypes (Seq.fromList pargs) argTypes
          res <- lift $ getStmtResultWithType block_idx stmt_idx ret
          addStmt $ R.DefineAtom res (R.Call f args ret)
        _ -> fail $ "Call given non-function."
    (P.Print, [pmsg]) -> do
      msg <- transExprWithType pmsg (StringRepr UnicodeRepr)
      addStmt $ R.Print msg
    (P.Assert, [pc, pmsg]) -> do
      c   <- transExprWithType pc   BoolRepr
      msg <- transExprWithType pmsg (StringRepr UnicodeRepr)
      addStmt $ R.Assert c msg
    (P.ReadReg, []) -> do
      Some r <- lift $ getReg (s^.P.statement_reg)
      res <- lift $ getStmtResultWithType block_idx stmt_idx (R.typeOfReg r)
      addStmt $ R.DefineAtom res (R.ReadReg r)
    (P.WriteReg, [pv]) -> do
      Some v <- transExpr pv
      r <- lift $ getRegWithType (s^.P.statement_reg) (R.typeOfAtom v)
      addStmt $ R.SetReg r v
    -- TODO: Support globals
    _ -> fail $ "Could not interpret statement."

transTermStmt' :: TypeRepr ret -> P.TermStmt -> StmtTrans s ret (R.TermStmt s ret)
transTermStmt' retType t = do

  let exprs  = Fold.toList $ t^.P.termStmt_exprs
  let blocks = Fold.toList $ t^.P.termStmt_blocks
  case (t^.P.termStmt_code, exprs, blocks) of
    (P.JumpTermStmt, [], [b_id]) -> do
      lift $ do
      b <- getBlockLabel b_id
      return $ R.Jump b
    (P.BranchTermStmt, [pc], [x_id, y_id]) -> do
      c <- transExprWithType pc BoolRepr
      lift $ do
      x <- getBlockLabel x_id
      y <- getBlockLabel y_id
      return $ R.Br c x y
    (P.ReturnTermStmt, [pe], []) -> do
      e <- transExprWithType pe retType
      return $ R.Return e
    (P.ErrorTermStmt, [pe], []) -> do
      e <- transExprWithType pe (StringRepr UnicodeRepr)
      return $ R.ErrorStmt e
    (P.TailCallTermStmt, (pf:pargs), []) -> do
      Some f <- transExpr pf
      case R.typeOfAtom f of
        FunctionHandleRepr argTypes ret -> do
          case testEquality ret retType of
            Just Refl -> do
              args <- transExprSeqWithTypes (Seq.fromList pargs) argTypes
              return $ R.TailCall f argTypes args
            Nothing -> fail "Tail call returns incorrect value."
        _ -> fail $ "Tail call given non-function."
    (P.SwitchMaybeTermStmt, [pe], [pj,pn]) -> do
      Some e <- transExpr pe
      case R.typeOfAtom e of
        MaybeRepr tp -> lift $ do
          j <- getLambdaLabel pj tp
          n <- getBlockLabel  pn
          return $ R.MaybeBranch tp e j n
        _ -> fail "MaybeBranch given bad expression."
    _ -> do
      fail $ "Could not parse term stmt."

transTermStmt :: TypeRepr ret -> P.TermStmt -> StmtTrans s ret (Posd (R.TermStmt s ret))
transTermStmt retType t = do
  let p = plSourceLoc $ fromProtoPos (t^.P.termStmt_pos)
  setPos p
  Posd p <$> transTermStmt' retType t

transBlock :: TypeRepr ret
           -> Word64  -- ^ Index of block (0 is first index).
           -> P.Block -- ^ Block to write to.
           -> Trans s ret (R.Block () s ret)
transBlock retType idx b = do
  block_id <- getBlockID idx
  v <- gets argVec
  let inputs | idx == 0 = Set.fromList $ V.toList (fmap (mapSome R.AtomValue) v)
             | otherwise = Set.empty
  let block_state = BlockState { blockPos = plSourceLoc $ fromProtoPos (b^.P.block_pos)
                               , blockStmts = []
                               }
  flip evalStateT block_state $ do
    zipWithM_ (transStmt idx) [0..] (Fold.toList (b^.P.block_statements))
    term <- transTermStmt retType (b^.P.block_termStmt)
    stmts <- gets blockStmts
    return $ R.mkBlock block_id inputs (Seq.fromList (reverse stmts)) term

mkRegs :: forall s ctx
        . Position
       -> NonceGenerator IO s
       -> CtxRepr ctx
       -> IO (V.Vector (Some (R.Reg s)))
mkRegs p ng argTypes = V.mapM (mapSomeM f) v
  where v = V.fromList (Fold.toList (ctxReprToSeq argTypes))
        f :: TypeRepr tp -> IO (R.Reg s tp)
        f tp = do
          i <- freshNonce ng
          return $ R.Reg { R.regPosition = p
                         , R.regId = i
--                       , R.regSource = R.Assigned
                         , R.typeOfReg = tp
                         }

        mapSomeM :: Functor m
                 => (forall (x :: CrucibleType). a x -> m (b x))
                 -> Some a -> m (Some b)
        mapSomeM h (Some x) = Some <$> h x

unpackCFG :: IsSymInterface sym
          => Simulator p sym
          -> P.Cfg
          -> (forall s init ret. R.CFG () s init ret -> IO a)
          -> IO a
unpackCFG sim pg cont = do
  let h_index   = pg^.P.cfg_handle_id
  Some reg_types <- fromProtoTypeSeq (pg^.P.cfg_registers)
  let pblocks   = Fold.toList $ pg^.P.cfg_blocks
  SomeHandle h <- getHandleBinding sim h_index

  handle_map <- readIORef (handleCache sim)

  let argTypes = handleArgTypes h
  let retType  = handleReturnType h

  let p = plSourceLoc $ fromProtoPos $ pg^.P.cfg_pos

  Some ng <- newIONonceGenerator
  argRegs <- V.fromList . toListFC Some <$> R.mkInputAtoms ng p argTypes
  regRegs <- mkRegs p ng reg_types

  initState <- flip runReaderT ng $ unGen $ do
    block_ids <- mapM genBlockID pblocks
    let block_map = Map.fromList (zip [0..] block_ids)
    stmt_result_map <- mkStmtResultMap regRegs pblocks
    return TransState { blockLabelMap = block_map
                      , handleMap = handle_map
                      , argVec = argRegs
                      , regVec = regRegs
                      , nonceGen = ng
                      , stmtResultMap = stmt_result_map
                      }

  (blocks,_finalSt) <- flip runStateT initState $ unTrans $
                         zipWithM (transBlock retType) [0..] pblocks

  let entryLabel = case R.blockID (head blocks) of
        R.LabelID lbl -> lbl
        R.LambdaID {} -> error "entry block has lambda label"

  let g = R.CFG { R.cfgHandle = h
                , R.cfgEntryLabel = entryLabel
                , R.cfgBlocks = blocks
                }
  cont g
