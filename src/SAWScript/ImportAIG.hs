{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.ImportAIG
  ( readAIGexpect
  , readAIG
  ) where

import Control.Applicative
import Control.Exception
import Control.Lens
import Control.Monad
import Control.Monad.Error
import Control.Monad.State.Strict
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))

import qualified Data.AIG as AIG
import qualified Data.ABC.GIA as ABC

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

type TypeParser s = StateT (V.Vector (SharedTerm s)) (ErrorT String IO)

runTypeParser :: V.Vector (SharedTerm s)
              -> TypeParser s a
              -> ErrorT String IO (a, V.Vector (SharedTerm s))
runTypeParser v m = runStateT m v

bitblastSharedTerm :: SharedContext s
                   -> SharedTerm s -- ^ Term for input variable
                   -> SharedTerm s -- ^ Term for type.
                   -> TypeParser s ()
bitblastSharedTerm _ v (asBoolType -> Just ()) = do
  modify (`V.snoc` v)
bitblastSharedTerm sc v (asBitvectorType -> Just w) = do
  inputs <- liftIO $ do
    getFn <- scApplyPreludeGet sc
    wt <- scNat sc w
    boolType <- scPreludeBool sc
    V.generateM (fromIntegral w) $ \i -> do
      getFn wt boolType v =<< scFinConst sc (fromIntegral i) w
  modify (V.++ inputs)
bitblastSharedTerm _ _ tp = fail $ show $
  text "Could not parse AIG input type:" <$$>
  indent 2 (scPrettyTermDoc tp)

parseAIGResultType :: SharedContext s
                   -> SharedTerm s -- ^ Term for type
                   -> TypeParser s (SharedTerm s)
parseAIGResultType _ (asBoolType -> Just ()) = do
  outputs <- get
  when (V.length outputs == 0) $ do
    fail "Not enough output bits for Bool result."
  put (V.drop 1 outputs)
  -- Return remaining as a vector.
  return (outputs V.! 0)
parseAIGResultType sc (asBitvectorType -> Just w) = do
  outputs <- get
  when (fromIntegral (V.length outputs) < w) $ do
    fail "Not enough output bits for type."
  let (base,remaining) = V.splitAt (fromIntegral w) outputs
  put remaining
  -- Return remaining as a vector.
  liftIO $ do
    boolType <- scPreludeBool sc
    scVector sc boolType (V.toList base)
parseAIGResultType _ _ = fail "Could not parse AIG output type."


-- |
networkAsSharedTerms
    :: AIG.IsAIG l g
    => g x
    -> SharedContext s
    -> V.Vector (SharedTerm s) -- ^ Input terms for AIG
    -> V.Vector (l x) -- ^ Outputs
    -> IO (V.Vector (SharedTerm s))
networkAsSharedTerms ntk sc inputTerms outputLits = do
  -- Get evaluator
  scNot <- scApplyPreludeNot sc
  scAnd <- scApplyPreludeAnd sc
  scOr <- scApplyPreludeOr sc
  scImpl <- scApplyPreludeImplies sc
  scFalse <- scApplyPreludeFalse sc

  -- Left is nonnegated, Right is negated
  let viewAnd inj _ (Left x)  (Left y)  = fmap inj $ scAnd x y
      viewAnd _ inj (Left x)  (Right y) = fmap inj $ scImpl x y
      viewAnd _ inj (Right x) (Left y)  = fmap inj $ scImpl y x
      viewAnd _ inj (Right x) (Right y) = fmap inj $ scOr x y

  let viewFinish (Left x)  = return x
      viewFinish (Right x) = scNot x

  let viewFn (AIG.And x y)    = viewAnd Left  Right x y
      viewFn (AIG.NotAnd x y) = viewAnd Right Left  x y
      viewFn (AIG.Input i)    = return (Left (inputTerms V.! i))
      viewFn (AIG.NotInput i) = return (Right (inputTerms V.! i))
      viewFn (AIG.FalseLit)   = return (Left scFalse)
      viewFn (AIG.TrueLit)    = return (Right scFalse)
  evalFn <- AIG.abstractEvaluateAIG ntk viewFn
  traverse (viewFinish <=< evalFn) outputLits

-- | Create vector for each input literal from expected types.
bitblastVarsAsInputLits :: forall s
                       . SharedContext s
                      -> [SharedTerm s]
                      -> ErrorT String IO (V.Vector (SharedTerm s))
bitblastVarsAsInputLits sc args = do
  let n = length args
  let mkLocalVar :: Int -> SharedTerm s -> IO (SharedTerm s)
      mkLocalVar i _tp = scLocalVar sc idx
          -- Earlier arguments have a higher deBruijn index.
          where idx = (n - i - 1)
  inputs <- liftIO $ zipWithM mkLocalVar [0..] args
  fmap snd $ runTypeParser V.empty $ do
    zipWithM_ (bitblastSharedTerm sc) inputs args

withReadAiger :: FilePath
              -> (forall g l. ABC.IsAIG l g => AIG.Network l g -> IO (Either String a))
              -> IO (Either String a)
withReadAiger path action = do
   mntk <- try (AIG.aigerNetwork ABC.proxy path)
   case mntk of
      Left e -> return (Left (show (e :: IOException)))
      Right ntk -> action ntk

translateNetwork :: AIG.IsAIG l g
                 => SharedContext s -- ^ Context to build in term.
                 -> g x             -- ^ Network to bitblast
                 -> [l x]           -- ^ Outputs for network.
                 -> [(String, SharedTerm s)] -- ^ Expected types
                 -> SharedTerm s -- ^ Expected output type.
                 -> ErrorT String IO (SharedTerm s)
translateNetwork sc ntk outputLits args resultType = do
  --lift $ putStrLn "inputTerms"
  inputTerms <- bitblastVarsAsInputLits sc (snd <$> args)
  -- Check number of inputs to network matches expected inputs.
  do let expectedInputCount = V.length inputTerms
     aigCount <- liftIO $ AIG.inputCount ntk
     unless (expectedInputCount == aigCount) $ do
       fail $ "AIG has " ++ show aigCount
                 ++ " inputs, while expected type has "
                 ++ show expectedInputCount ++ " inputs."
  --lift $ putStrLn "Output vars"
  -- Get outputs as SAWCore terms.
  outputVars <- liftIO $
    networkAsSharedTerms ntk sc inputTerms (V.fromList outputLits)
  --lift $ putStrLn "Type parser"
   -- Join output lits into result type.
  (res,rargs) <- runTypeParser outputVars $ parseAIGResultType sc resultType
  unless (V.null rargs) $
    fail "AIG contains more outputs than expected."
  lift $ scLambdaList sc args res

readAIGexpect
        :: forall s
         . SharedContext s -- ^ Context to build in term.
        -> FilePath        -- ^ Path to AIG
        -> SharedTerm s    -- ^ Expected type of term.
        -> IO (Either String (SharedTerm s))
readAIGexpect sc path aigType =
  withReadAiger path $ \(AIG.Network ntk outputLits) -> do
    --putStrLn "Network outputs"
    let (args,resultType) = asPiList aigType
    runErrorT $
      translateNetwork sc ntk outputLits args resultType

readAIG :: SharedContext s -> FilePath -> IO (Either String (SharedTerm s))
readAIG sc f =
  withReadAiger f $ \(AIG.Network ntk outputLits) -> do
    inputs <- AIG.inputCount ntk
    inLen <- scNat sc (fromIntegral inputs)
    outLen <- scNat sc (fromIntegral (length outputLits))
    boolType <- scBoolType sc
    inType <- scVecType sc inLen boolType
    outType <- scVecType sc outLen boolType
    runErrorT $
      translateNetwork sc ntk outputLits [("x", inType)] outType
