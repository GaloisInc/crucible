{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module SAWScript.AutoMatch where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Arrow ((***), (&&&), first, second)

import Data.Maybe
import Data.Char
import Data.Ord
import Data.List

import Control.Conditional (whenM)

import Text.Read (readMaybe)

import SAWScript.AutoMatch.ArgMapping
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

-- A free monad...

type Interaction = Free InteractionF

data InteractionF a =
  -- output:
    Info (Maybe String) String a
  | Warning String a
  | Choice String [String] a
  | OutOfBounds Int (Int,Int) a
  | Failure String a
  -- input:
  | Confirm String (Bool -> a)
  | GetInt String (Int -> a)
  deriving (Functor)

-- And (one possible) interpretation for it into IO...

interactIO :: Interaction a -> IO a
interactIO interaction =
   case interaction of
      Pure a -> return a
      Free a -> case a of
         Info title str k ->
            putStrLn (fromMaybe "Info" title ++ ": " ++ str) >> interactIO k
         Warning str k ->
            putStrLn ("Warning: " ++ str) >> interactIO k
         Choice str opts k -> do
            putStrLn str
            forM_ (zip [1..] opts) $ \(i, opt) ->
               putStrLn $ show (i :: Int) ++ ". " ++ opt
            interactIO k
         OutOfBounds _ (l,h) k ->
            putStrLn ("Please enter an integer between " ++ show l ++ " and " ++ show h ++ ".") >> interactIO k
         Failure str k ->
            putStrLn ("Failure: " ++ str) >> interactIO k
         Confirm str f -> do
            putStr ("Confirm: " ++ str ++ " ")
            fix $ \loop -> do
               input <- map toLower <$> getLine
               case filter snd . map (second $ elem input)
                    . zip [True, False] $ [yes, no] of
                  (b,_):_ -> interactIO (f b)
                  []      -> putStr "Please enter either 'yes' or 'no': " >> loop
         GetInt str f -> do
            putStr (str ++ " ")
            fix $ \loop ->
               maybe (putStrLn "Please enter an integer." >> loop) (interactIO . f) . readMaybe =<< getLine

type Assignments = [((Arg, Int), (Arg, Int))]
type Mappings    = (ArgMapping, ArgMapping)

-- The interactive matching procedure...

matchingProcedure :: Decl -> Decl -> Interaction (Assignments, Mappings)
matchingProcedure left right =
   execMatchDecls (left, right) . sequence_ $
      [ initialInfo
      , checkReturnTypeCompat
      , checkSignatureCompat
      , processExactMatches
      , checkNameClashes
      , matchInteractively ]

-- The individual components of the interactive matching procedure...

initialInfo :: Match (Arg,Int) ArgMapping ()
initialInfo = do
   (left, right) <- ask
   info (Just "Comparing") $ show left ++
          "\n           " ++ show right ++ "\n"

checkReturnTypeCompat :: Match (Arg,Int) ArgMapping ()
checkReturnTypeCompat = do
   (left, right) <- ask
   when (declType left /= declType right) $
      failure $
         "The declarations (" ++
         declName left ++ " : ... " ++ show (declType left) ++
         ") and (" ++
         declName right ++ " : ... " ++ show (declType right) ++
         ") do not match in return type, and so cannot be reconciled."

checkSignatureCompat :: Match (Arg,Int) ArgMapping ()
checkSignatureCompat = do
   (left, right) <- ask
   whenM (uncurry (/=) . both (fmap Set.size . typeBins) <$> get) $ do
      warning $
         "The signatures for '" ++ declName left ++
         "' and '" ++ declName right ++ 
         "' cannot be aligned by permutation."
      confirmOrQuit "Proceed with matching anyway?"

processExactMatches :: Match (Arg,Int) ArgMapping ()
processExactMatches = do
   exactMatches <- findExactMatches <$> get
   forM_ exactMatches $ \((arg1, i1), (arg2, i2)) -> do
      matchArgs (arg1, i1) (arg2, i2)
      info (Just "Exact match") $
         "(" ++ show arg1 ++ ")" ++ " at " ++
         formatIndex i1 ++ corresponds ++ formatIndex i2

checkNameClashes :: Match (Arg,Int) ArgMapping ()
checkNameClashes = do
   sharedNames <- getIntersect (Map.keys . nameLocs)
   forM_ sharedNames $ \name -> do
      ((li, lt), (ri, rt)) <- (both $ assertJust . lookupName name) <$> get -- assertJust *just*ified
      warning $                                                             -- b/c name is definitely in map
         "Arguments " ++ formatIndexedArg False name lt li ++
         corresponds  ++ formatIndexedArg False name rt ri ++
         " are named identically, but have differing types."
      confirmOrQuit "Proceed with matching by considering them distinct?"

matchInteractively :: Match (Arg,Int) ArgMapping ()
matchInteractively = do
   sharedTypes <- getIntersect (Map.keys . typeBins)
   forM_ sharedTypes $ \typ ->
      both (argsForType typ) <$> get >>=
         (fix $ \loop -> \case
             ([],_) -> return ()
             (_,[]) -> return ()
             (leftArgs@((ln, li):_), rightArgs) ->
                offerChoice
                   ("Match " ++ formatIndexedArg True ln typ li ++ corresponds ++ "___:")
                   ((for rightArgs $ \(rn, ri) ->
                      (formatIndexedArg False rn typ ri,
                       do matchArgs (Arg ln typ, li) (Arg rn typ, ri)
                          loop (delete (ln, li) leftArgs,
                                delete (rn, ri) rightArgs)))
                     ++ [("Quit", userQuit)]))
   where
      argsForType typ =
         sortBy (comparing snd) . Set.toList . assertJust . lookupType typ
         --                    *just*ified use ^^^^^^^^^^ because typ is
         --                    definitely in map when we call this function

-- The monad stack used above looks like this...

type Match m s a =
   ReaderT (Decl, Decl)                            -- information about initial declarations
      (MaybeT                                      -- possible early termination
         (WriterT [(m,m)]                          -- append-only output of matched results
                  (StateT (s,s)                    -- remaining arguments on each side
                          Interaction))) a         -- free monad of instructions to execute

runMatchDecls :: (Decl, Decl) -> Match (Arg,Int) ArgMapping a -> Interaction (Maybe a, (Assignments, Mappings))
runMatchDecls (l,r) =
   fmap rassoc
   . flip runStateT (both (makeArgMapping . declArgs) (l,r))
   . runWriterT
   . runMaybeT
   . flip runReaderT (l,r)
   where
      rassoc ((x,y),z) = (x,(y,z))

execMatchDecls :: (Decl, Decl) -> Match (Arg,Int) ArgMapping a -> Interaction (Assignments, Mappings)
execMatchDecls (l,r) = fmap snd . runMatchDecls (l,r)

matchArgs :: (Arg, Int) -> (Arg, Int) -> Match (Arg,Int) ArgMapping ()
matchArgs (Arg ln lt, li) (Arg rn rt, ri) = do
   modify (removeName ln *** removeName rn)
   tell [((Arg ln lt, li), (Arg rn rt, ri))]

-- Smart constructors for match actions...

info :: MonadFree InteractionF m => Maybe String -> String -> m ()
info title string = liftF $ Info title string ()

warning :: MonadFree InteractionF m => String -> m ()
warning string = liftF $ Warning string ()

confirm :: MonadFree InteractionF m => String -> m Bool
confirm string = liftF $ Confirm string id

offerChoice :: MonadFree InteractionF m => String -> [(String, m a)] -> m a
offerChoice str options =
   let (descriptions, actions) = unzip options
       numOptions = length options
   in do liftF $ Choice str descriptions ()
         userChoice <- getInBounds (1, numOptions)
         actions !! (userChoice - 1)

outOfBounds :: MonadFree InteractionF m => Int -> (Int,Int) -> m ()
outOfBounds i (l,h) = liftF $ OutOfBounds i (l,h) ()

getInt :: MonadFree InteractionF m => m Int
getInt = liftF $ GetInt "?" id

getInBounds :: MonadFree InteractionF m => (Int,Int) -> m Int
getInBounds (l,h) = do
   i <- getInt
   if i <= h && i >= l
      then return i
      else do outOfBounds i (l,h)
              getInBounds (l,h)

getIntersect :: (Ord b) => (s -> [b]) -> Match m s [b]
getIntersect f =
   Set.toList . uncurry Set.intersection . (both $ Set.fromList . f) <$> get

failure :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => String -> t (MaybeT m) b
failure string =
   liftF (Failure string ()) >> lift (MaybeT (return Nothing))

userQuit :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => t (MaybeT m) b
userQuit = failure "Matching terminated by user."

confirmOrQuit :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => String -> t (MaybeT m) ()
confirmOrQuit str =
   whenM (not <$> confirm str) userQuit

-- How to find exact matches (name & type) between two ArgMappings:

findExactMatches :: (ArgMapping, ArgMapping) -> [((Arg, Int), (Arg, Int))]
findExactMatches (leftMapping, rightMapping) =
   concat $
      for sharedTypes $ \typ ->
         for (sharedNamesWithType typ) $ \name ->
              let (li, _) = assertJust $ lookupName name leftMapping  -- assertJust is (pun intended) *just*ified here,
                  (ri, _) = assertJust $ lookupName name rightMapping -- b/c we have already confirmed the keys exist
              in ((Arg name typ, li), (Arg name typ, ri))
   where
      sharedTypes =
         Set.toList $
            Set.intersection (Map.keysSet (typeBins leftMapping))
                             (Map.keysSet (typeBins rightMapping))
      namesWithType typ =
         fromMaybe Set.empty
         . fmap (Set.fromList . map fst . Set.toList)
         . lookupType typ
      sharedNamesWithType typ =
         Set.toList $
            Set.intersection (namesWithType typ leftMapping)
                             (namesWithType typ rightMapping)

findDeclMatches :: [Decl] -> [Decl] -> Interaction ([(Decl,Decl)], ([Decl],[Decl]))
findDeclMatches leftModule rightModule =
   fmap (swap . first (both Map.elems))
   . runWriterT . flip execStateT (both declsNameMaps (leftModule, rightModule)) $ do
      -- exact function name matches
      sharedNames <- Set.toList . uncurry Set.intersection . both Map.keysSet <$> get
      forM_ sharedNames $ \name -> do
         info (Just "Aligning functions") $ name ++ corresponds ++ name ++ "\n"
         tell =<< (: []) <$> gets (both $ assertJust . Map.lookup name)
         modify (both $ Map.delete name)
      -- report unmatched names
      (leftoverLeft, leftoverRight) <- both Map.keys <$> get
      forM_ leftoverLeft $ \name ->
         warning $ "Could not find correspondence for " ++ name ++ " (LEFT)"
      forM_ leftoverRight $ \name ->
         warning $ "Could not find correspondence for " ++ name ++ " (RIGHT)"
   where
      swap (x,y) = (y,x)
      declsNameMaps = Map.fromList . map (declName &&& id)

matchModules :: [Decl] -> [Decl] -> Interaction [(Decl, Decl, Assignments)]
matchModules leftModule rightModule = do
   matchingDecls <- fst <$> findDeclMatches leftModule rightModule
   fmap catMaybes . forM matchingDecls $ \(leftDecl, rightDecl) -> do
      (assigns, leftovers) <- matchingProcedure leftDecl rightDecl
      if uncurry (&&) (both isEmptyArgMapping leftovers)
         then return . Just $ (leftDecl, rightDecl, assigns)
         else return Nothing

-- Example declarations:

dl, dr :: Decl
dl = Decl "foo" Int [Arg "y" Int, Arg "x" Int, Arg "p" Int, Arg "z" Int]
dr = Decl "foo" Int [Arg "z" Int, Arg "y" Int, Arg "p" Int, Arg "x" Int]
