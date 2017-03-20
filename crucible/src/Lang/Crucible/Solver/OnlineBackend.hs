-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.OnlineBackend
-- Description      : Solver backend that maintains a persistent
--                    connection to Yices
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------

{-# LANGUAGE EmptyDataDecls #-}
module Lang.Crucible.Solver.OnlineBackend
  ( -- * OnlineBackend
    OnlineBackend
  , withOnlineBackend
    -- * OnlineBackendState
  , OnlineBackendState
  , appendAssertion
  , appendAssertions
  , programLoc
  , getYicesProcess
  , Yices.YicesProcess(..)
  , setConfig
  , getConfig
  , yicesOnlineAdapter
  ) where

import           Control.Exception
import           Control.Lens
import           Control.Monad.State
import           Data.Bits
import           Data.Foldable
import           Data.IORef
import qualified Data.Map as Map
import           Data.Parameterized.Nonce
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           System.Exit
import           System.IO
import           System.Process

import qualified Lang.Crucible.Config as CFG
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.MSSim (SimConfig)
import           Lang.Crucible.Simulator.SimError
import qualified Lang.Crucible.Simulator.Utils.Environment as Env
import           Lang.Crucible.Solver.Adapter
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import           Lang.Crucible.Solver.SimpleBackend.SMTWriter
  ( WriterConn
  , assumeFormula
  , mkFormula
  )
import qualified Lang.Crucible.Solver.SimpleBackend.Yices as Yices
import qualified Lang.Crucible.Solver.SimpleBuilder as SB

type OnlineBackend t = SB.SimpleBuilder t OnlineBackendState

yicesOnlineAdapter :: SolverAdapter OnlineBackendState
yicesOnlineAdapter =
   Yices.yicesAdapter
   { solver_adapter_check_sat = \sym _ _ p cont -> do
        yproc <- getYicesProcess sym
        let c = Yices.yicesConn yproc

        -- build the formula outside the frame to
        -- preserve intermediate cache results
        p_smtformula <- mkFormula c p

        Yices.inFreshFrame c $ do
          assumeFormula c p_smtformula
          res <- Yices.checkAndGetModel yproc
          cont (fmap (\x -> (x, Nothing)) res)
   }

------------------------------------------------------------------------
-- OnlineBackendState

data YicesOnline

startYicesProcess :: Monad m => CFG.Config m -> IO (Yices.YicesProcess t s)
startYicesProcess cfg = do
  yices_prepath <- CFG.getConfigValue Yices.yicesPath cfg
  yices_path <- Env.findExecutable =<< Env.expandEnvironmentPath Map.empty yices_prepath

  let args = ["--mode=push-pop"]

  let create_proc
        = (proc yices_path args)
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          , cwd = Nothing
          }

  let startProcess = do
        x <- createProcess create_proc
        case x of
          (Just in_h, Just out_h, Just err_h, ph) -> return (in_h,out_h,err_h,ph)
          _ -> fail "Internal error in startYicesProcess: Failed to create handle."

  (in_h,out_h,err_h,ph) <- startProcess

  --void $ forkIO $ logErrorStream err_stream (logLn 2)
  -- Create new connection for sending commands to yices.
  let features = useLinearArithmetic
             .|. useBitvectors
             .|. useSymbolicArrays
             .|. useComplexArithmetic
             .|. useStructs
  conn <- Yices.newConnection in_h features SB.emptySymbolVarBimap
  Yices.setYicesParams conn cfg
  err_reader <- Yices.startHandleReader err_h
  return $! Yices.YicesProcess { Yices.yicesConn   = conn
                               , Yices.yicesStdin  = in_h
                               , Yices.yicesStdout = out_h
                               , Yices.yicesStderr = err_reader
                               , Yices.yicesHandle = ph
                               }

shutdownYicesProcess :: Yices.YicesProcess t s -> IO ()
shutdownYicesProcess yices = do
  -- Close input stream.
  hClose (Yices.yicesStdin yices)
  -- Log outstream as error messages.

  --logLn 2 "Waiting for yices to terminate"
  ec <- waitForProcess (Yices.yicesHandle yices)
  case ec of
    ExitSuccess -> return () --logLn 2 "Yices terminated."
    ExitFailure x ->
       fail $ "yices exited with unexpected code: "++show x

type OnlineConfig t = SimConfig (OnlineBackend t)

type AssertionSeq t = Seq (Assertion (SB.BoolElt t))

type PrevAssertionLevel t =  (AssertionSeq t, SB.BoolElt t)

levelPreds :: Simple Traversal (PrevAssertionLevel t) (SB.BoolElt t)
levelPreds f (s,c) = (,) <$> (traverse . assertPred) f s <*> f c

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data OnlineBackendState t
   = OnlineBackendState { _prevAssertionLevels :: !(Seq (PrevAssertionLevel t))
                        , _curAssertionLevel   :: !(AssertionSeq t)
                        , _proofObligs :: Seq (Seq (SB.BoolElt t), Assertion (SB.BoolElt t))
                        , _programLoc  :: !ProgramLoc
                          -- ^ Number of times we have pushed
                        , yicesProc    :: !(IORef (Maybe (Yices.YicesProcess t YicesOnline)))
                        , config       :: !(Maybe (OnlineConfig t))
                        }

-- | Returns an initial execution state.
initialOnlineBackendState :: IO (OnlineBackendState t)
initialOnlineBackendState = do
  procref <- newIORef Nothing
  return $! OnlineBackendState
              { _prevAssertionLevels = Seq.empty
              , _curAssertionLevel   = Seq.empty
              , _proofObligs = Seq.empty
              , _programLoc = initializationLoc
              , yicesProc = procref
              , config = Nothing
              }

-- | The sequence of accumulated assertion obligations
proofObligs :: Simple Lens (OnlineBackendState t) (Seq (Seq (SB.BoolElt t), Assertion (SB.BoolElt t)))
proofObligs = lens _proofObligs (\s v -> s { _proofObligs = v })

-- | The assertions from previous levels
prevAssertionLevels :: Simple Lens (OnlineBackendState t) (Seq (PrevAssertionLevel t))
prevAssertionLevels = lens _prevAssertionLevels (\s v -> s { _prevAssertionLevels = v })

-- | The current assertion level
curAssertionLevel :: Simple Lens (OnlineBackendState t) (AssertionSeq t)
curAssertionLevel = lens _curAssertionLevel (\s v -> s { _curAssertionLevel = v })

-- | The current location in the program.
programLoc :: Simple Lens (OnlineBackendState t) ProgramLoc
programLoc = lens _programLoc (\s v -> s { _programLoc = v })

appendAssertion :: ProgramLoc
                -> SB.BoolElt t
                -> SimErrorReason
                -> OnlineBackendState t
                -> OnlineBackendState t
appendAssertion l p m s =
  let ast = Assertion l p (Just m) in
  s & appendAssertions (Seq.singleton ast)
    & proofObligs %~ (Seq.|> (hyps, ast))
 where hyps = join (fmap lvlHyps (s^.prevAssertionLevels)) Seq.>< fmap (^.assertPred) (s^.curAssertionLevel)
       lvlHyps (hs,c) = (fmap (^.assertPred) hs) Seq.|> c

appendAssumption :: ProgramLoc
                -> SB.BoolElt t
                -> OnlineBackendState t
                -> OnlineBackendState t
appendAssumption l p s =
  s & appendAssertions (Seq.singleton (Assertion l p Nothing))

-- | Append assertions to path state.
appendAssertions :: Seq (Assertion (SB.BoolElt t))
                 -> OnlineBackendState t
                 -> OnlineBackendState t
appendAssertions pairs = curAssertionLevel %~ (Seq.>< pairs)


instance HasProgramLoc (OnlineBackendState t) where
  setProgramLoc = set programLoc

setConfig :: OnlineBackend t -> OnlineConfig t -> IO ()
setConfig sym cfg = do
  st <- readIORef (SB.sbStateManager sym)
  writeIORef (SB.sbStateManager sym) $! st { config = Just cfg }

getConfig :: OnlineBackend t -> IO (OnlineConfig t)
getConfig sym = do
  st <- readIORef (SB.sbStateManager sym)
  case config st of
    Nothing -> fail "Online backend has not been configured!"
    Just cfg -> return cfg

getYicesProcess :: OnlineBackend t -> IO (Yices.YicesProcess t YicesOnline)
getYicesProcess sym = do
  st <- readIORef (SB.sbStateManager sym)
  mproc <- readIORef (yicesProc st)
  case mproc of
    Just p -> do
      return p
    Nothing -> do
      cfg <- getConfig sym
      p <- startYicesProcess cfg
      -- set up Yices parameters
      Yices.setYicesParams (Yices.yicesConn p) cfg
      writeIORef (yicesProc st) (Just p)
      return p

withOnlineBackend :: NonceGenerator IO t
                  -> (OnlineBackend t -> IO a)
                  -> IO a
withOnlineBackend gen action = do
  st <- initialOnlineBackendState
  sym <- SB.newSimpleBuilder st gen
  r <- try $ action sym
  mp <- readIORef (yicesProc st)
  case mp of
   Nothing -> return ()
   Just p -> shutdownYicesProcess p
  case r of
   Left e -> throwIO (e :: SomeException)
   Right x -> return x

checkSatisfiable
    :: OnlineBackend t
    -> SB.BoolElt t
    -> IO (SatResult ())
checkSatisfiable sym p = do
   yproc <- getYicesProcess sym
   let c = Yices.yicesConn yproc

   p_smtexpr <- mkFormula c p
   Yices.inFreshFrame c $ do
     assumeFormula c p_smtexpr
     Yices.check yproc


-- | Get the assertion level of a onlinebackend state backend.
assertionLevel :: OnlineBackendState t -> Int
assertionLevel s = Seq.length $ s^.prevAssertionLevels

-- | Backtract to a given assertion level
backtrackToLevel :: OnlineBackend t -> Int -> IO ()
backtrackToLevel sym prev_lvl = do
  -- Get height of current stack
  cur_lvl <- assertionLevel <$> readIORef (SB.sbStateManager sym)
  -- Execute pop command
  curYicesProcess <- getYicesProcess sym
  let conn = Yices.yicesConn curYicesProcess
  assert (cur_lvl >= prev_lvl) $ do
  replicateM_ (cur_lvl - prev_lvl) $ Yices.pop conn

checkedDropSeq :: Int -> Seq.Seq a -> Seq.Seq a
checkedDropSeq cnt s
  | cnt <= Seq.length s = Seq.drop cnt s
  | otherwise = error $ "internal error: checkedDropSeq given bad length"

-- | Get assertions to push
assertionsToPush :: OnlineBackendState t
                 -> Int -- ^ Current level
                 -> Int -- ^ Assertions already added in current level
                 -> (AssertionSeq t, [(SB.BoolElt t, AssertionSeq t)])
assertionsToPush s cur_lvl assert_cnt =
  case Seq.viewl (Seq.drop cur_lvl (s^.prevAssertionLevels)) of
    Seq.EmptyL -> (checkedDropSeq assert_cnt (s^.curAssertionLevel), [])
    (a0,p0) Seq.:< l0 -> (checkedDropSeq assert_cnt a0, go p0 l0)
      where go p l =
              case Seq.viewl l of
                Seq.EmptyL -> [(p,s^.curAssertionLevel)]
                (a,p') Seq.:< l' -> (p,a) : go p' l'

assertToYices :: WriterConn t (Yices.Connection YicesOnline) -> AssertionSeq t -> IO ()
assertToYices conn = traverse_ (\a -> Yices.assume conn (a^.assertPred))

assertionPreds :: Simple Traversal (OnlineBackendState t) (SB.BoolElt t)
assertionPreds f s =
  (\p c -> s & prevAssertionLevels .~ p
             & curAssertionLevel   .~ c)
    <$> (traverse . levelPreds) f (s^.prevAssertionLevels)
    <*> (traverse . assertPred) f (s^.curAssertionLevel)

instance SB.IsSimpleBuilderState OnlineBackendState where
  sbAddAssertion sym p m =
    case asConstantPred p of
      Just True ->
        return ()
      Just False -> do
        loc <- getCurrentProgramLoc sym
        throw (SimError loc m)
      Nothing -> do
        conn <- Yices.yicesConn <$> getYicesProcess sym
        loc <- getCurrentProgramLoc sym
        -- Send assertion to yices
        Yices.assume conn p
        -- Record list of  assertions
        modifyIORef' (SB.sbStateManager sym) $ appendAssertion loc p m

  sbAddAssumption sym p =
    case asConstantPred p of
      Just True ->
        return ()
      _ -> do
        conn <- Yices.yicesConn <$> getYicesProcess sym
        loc <- getCurrentProgramLoc sym
        -- Send assertion to yices
        Yices.assume conn p
        -- Record list of  assertions
        modifyIORef' (SB.sbStateManager sym) $ appendAssumption loc p

  sbAppendAssertions sym a = do
    -- Tell Yices of assertions
    conn <- Yices.yicesConn <$> getYicesProcess sym
    assertToYices conn a
    -- Add assertions to list
    modifyIORef' (SB.sbStateManager sym) $ appendAssertions a

  sbAssertionsBetween old cur = a0 Seq.>< mconcat (snd <$> toList rest)
    where old_lvl = assertionLevel $ old
          old_last_assert = Seq.length $ old^.curAssertionLevel
          (a0,rest) = assertionsToPush cur old_lvl old_last_assert

  sbAllAssertions sym = do
    s <- readIORef (SB.sbStateManager sym)
    andAllOf sym assertionPreds s

  sbEvalBranch sym p = do
    case asConstantPred p of
      Just True  -> return $ NoBranch True
      Just False -> return $ NoBranch False
      Nothing -> do
       notP <- notPred sym p

       p_res    <- checkSatisfiable sym p
       notp_res <- checkSatisfiable sym notP
       case (p_res, notp_res) of
         (Unsat, Unsat) -> return InfeasibleBranch
         (Unsat, _ )    -> return $ NoBranch False
         (_    , Unsat) -> return $ NoBranch True
         (_    , _)     -> return $ SymbolicBranch True

  sbPushBranchPred sym p = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    Yices.push conn
    Yices.assume conn p
    modifyIORef' (SB.sbStateManager sym) $ \cur_ops ->
      let cur_asserts = cur_ops^.curAssertionLevel
       in cur_ops & prevAssertionLevels %~ (Seq.|> (cur_asserts, p))
                  & curAssertionLevel   .~ Seq.empty

  sbBacktrackToState sym prev_state = do
    let prev_lvl = assertionLevel $ prev_state^.SB.pathState
    backtrackToLevel sym prev_lvl

  sbGetProofObligations sym = do
    s <- readIORef (SB.sbStateManager sym)
    return $ s^.proofObligs

  sbSetProofObligations sym obligs = do
    modifyIORef' (SB.sbStateManager sym) (set proofObligs obligs)

  sbSwitchToState sym prev_state next_state = do
    let prev_lvl = assertionLevel $ prev_state^.SB.pathState
    backtrackToLevel sym prev_lvl
    let last_lvl_cnt = Seq.length $ prev_state^.SB.pathState^.curAssertionLevel

    let (a0,l) = assertionsToPush (next_state^.SB.pathState) prev_lvl last_lvl_cnt
    conn <- Yices.yicesConn <$> getYicesProcess sym
    assertToYices conn a0
    forM_ l $ \(p, a) -> do
      Yices.push conn
      Yices.assume conn p
      assertToYices conn a
