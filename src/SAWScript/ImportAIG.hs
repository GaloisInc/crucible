{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.ImportAIG
  ( readAIG
  , readAIG'
  ) where

import Control.Applicative
import Control.Exception
import Control.Lens
import Control.Monad
import Control.Monad.Error
import Control.Monad.State.Strict
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))

import qualified Verinf.Symbolic.Lit.ABC_GIA as GIA

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
    :: GIA.Network
    -> SharedContext s
    -> V.Vector (SharedTerm s) -- ^ Input terms for AIG
    -> V.Vector GIA.Lit -- ^ Outputs
    -> IO (V.Vector (SharedTerm s))
networkAsSharedTerms ntk sc inputTerms outputLits = do
  -- Get evaluator
  scNot <- scApplyPreludeNot sc
  scAnd <- scApplyPreludeAnd sc
  scOr <- scApplyPreludeOr sc
  scImp <- scApplyPreludeImplies sc
  scFalse <- scApplyPreludeFalse sc
  -- | Left means negated, Right means not negated.
  let viewFn (GIA.AndLit (Right x) (Right y)) = Right <$> scAnd x y
      viewFn (GIA.AndLit (Left  x) (Left  y)) = Left  <$> scOr x y
      viewFn (GIA.AndLit (Left  x) (Right y)) = Left  <$> scImp y x
      viewFn (GIA.AndLit (Right x) (Left  y)) = Left  <$> scImp x y
      viewFn (GIA.NotLit (Right x)) = return $ Left  x
      viewFn (GIA.NotLit (Left  x)) = return $ Right x
      viewFn (GIA.InputLit i) = return $ Right $ inputTerms V.! i
      viewFn GIA.FalseLit = return $ Right scFalse
  let neg (Left  x) = scNot x
      neg (Right x) = return x
  evalFn <- GIA.litEvaluator ntk viewFn
  traverse evalFn outputLits >>= traverse neg

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
              -> (GIA.Network -> IO (Either String a))
              -> IO (Either String a)
withReadAiger path action = do
  mntk <- GIA.readAiger path
  case mntk of
    Nothing -> return $ Left $ "Could not read AIG file " ++ show path ++ "."
    Just ntk -> finally (action ntk) (GIA.freeNetwork ntk)

translateNetwork :: SharedContext s -- ^ Context to build in term.
                 -> GIA.Network -- ^ Network to bitblast
                 -> SV.Vector GIA.Lit -- ^ Outputs for network.
                 -> [(String, SharedTerm s)] -- ^ Expected types
                 -> SharedTerm s -- ^ Expected output type.
                 -> ErrorT String IO (SharedTerm s)
translateNetwork sc ntk outputLits args resultType = do
  --lift $ putStrLn "inputTerms"
  inputTerms <- bitblastVarsAsInputLits sc (snd <$> args)
  -- Check number of inputs to network matches expected inputs.
  do let expectedInputCount = V.length inputTerms
     aigCount <- liftIO $ GIA.networkInputCount ntk
     unless (expectedInputCount == aigCount) $ do
       fail $ "AIG has " ++ show aigCount
                 ++ " inputs, while expected type has "
                 ++ show expectedInputCount ++ " inputs."
  --lift $ putStrLn "Output vars"
  -- Get outputs as SAWCore terms.
  outputVars <- liftIO $
    networkAsSharedTerms ntk sc inputTerms (V.fromList (SV.toList outputLits))
  --lift $ putStrLn "Type parser"
   -- Join output lits into result type.
  (res,rargs) <- runTypeParser outputVars $ parseAIGResultType sc resultType
  unless (V.null rargs) $
    fail "AIG contains more outputs than expected."
  lift $ scLambdaList sc args res

readAIG :: forall s
         . SharedContext s -- ^ Context to build in term.
        -> FilePath        -- ^ Path to AIG
        -> SharedTerm s    -- ^ Expected type of term.
        -> IO (Either String (SharedTerm s))
readAIG sc path aigType =
  withReadAiger path $ \ntk -> do
    --putStrLn "Network outputs"
    outputLits <- GIA.networkOutputs ntk
    let (args,resultType) = asPiList aigType
    runErrorT $
      translateNetwork sc ntk outputLits args resultType

-- | FIXME? (RWD) Do we need this function? Why do we
--   use this instead of readAIG above?
readAIG' :: SharedContext s -> FilePath -> IO (Either String (SharedTerm s))
readAIG' sc f =
  withReadAiger f $ \ntk -> do
    outputLits <- GIA.networkOutputs ntk
    inputLits <- GIA.networkInputs ntk
    inLen <- scNat sc (fromIntegral (SV.length inputLits))
    outLen <- scNat sc (fromIntegral (SV.length outputLits))
    boolType <- scBoolType sc
    inType <- scVecType sc inLen boolType
    outType <- scVecType sc outLen boolType
    runErrorT $
      translateNetwork sc ntk outputLits [("x", inType)] outType
