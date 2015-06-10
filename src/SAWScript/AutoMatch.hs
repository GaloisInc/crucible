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
import Control.Arrow ((***), second)

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
   execMatch (left, right) . sequence_ $
      [ initialInfo
      , checkReturnTypeCompat
      , checkSignatureCompat
      , processExactMatches
      , checkNameClashes
      , matchInteractively ]

-- The individual components of the interactive matching procedure...

initialInfo :: Match ()
initialInfo = do
   (left, right) <- ask
   info (Just "Comparing") $ show left ++
          "\n           " ++ show right ++ "\n"

checkReturnTypeCompat :: Match ()
checkReturnTypeCompat = do
   (left, right) <- ask
   when (declType left /= declType right) $
      failure $
         "The declarations (" ++
         declName left ++ " : ... " ++ show (declType left) ++
         ") and (" ++
         declName right ++ " : ... " ++ show (declType right) ++
         ") do not match in return type, and so cannot be reconciled."

checkSignatureCompat :: Match ()
checkSignatureCompat = do
   (left, right) <- ask
   whenM (uncurry (/=) . both (fmap Set.size . typeBins) <$> get) $ do
      warning $
         "The signatures for '" ++ declName left ++
         "' and '" ++ declName right ++ 
         "' cannot be aligned by permutation."
      confirmOrQuit "Proceed with matching anyway?"

processExactMatches :: Match ()
processExactMatches = do
   exactMatches <- findExactMatches <$> get
   forM_ exactMatches $ \((arg1, i1), (arg2, i2)) -> do
      match (arg1, i1) (arg2, i2)
      info (Just "Exact match") $
         "(" ++ show arg1 ++ ")" ++ " at " ++
         formatIndex i1 ++ corresponds ++ formatIndex i2

checkNameClashes :: Match ()
checkNameClashes = do
   sharedNames <- getIntersect (Map.keys . nameLocs)
   forM_ sharedNames $ \name -> do
      ((li, lt), (ri, rt)) <- (both $ assertJust . lookupName name) <$> get -- assertJust *just*ified
      warning $                                                             -- b/c name is definitely in map
         "Arguments " ++ formatIndexedArg False name lt li ++
         corresponds  ++ formatIndexedArg False name rt ri ++
         " are named identically, but have differing types."
      confirmOrQuit "Proceed with matching by considering them distinct?"

matchInteractively :: Match ()
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
                       do match (Arg ln typ, li) (Arg rn typ, ri)
                          loop (delete (ln, li) leftArgs,
                                delete (rn, ri) rightArgs)))
                     ++ [("Quit", userQuit)]))
   where
      argsForType typ =
         sortBy (comparing snd) . Set.toList . assertJust . lookupType typ
         --                    *just*ified use ^^^^^^^^^^ because typ is
         --                    definitely in map when we call this function

-- The monad stack used above looks like this...

type Match a =
   ReaderT (Decl, Decl)                            -- information about initial declarations
      (MaybeT                                      -- possible early termination
         (WriterT [((Arg,Int),(Arg,Int))]          -- append-only output of matched results
                  (StateT (ArgMapping, ArgMapping) -- remaining arguments on each side
                          Interaction))) a         -- free monad of instructions to execute

runMatch :: (Decl, Decl) -> Match a -> Interaction (Maybe a, (Assignments, Mappings))
runMatch (l,r) =
   fmap rassoc
   . flip runStateT (both (makeArgMapping . declArgs) (l,r))
   . runWriterT
   . runMaybeT
   . flip runReaderT (l,r)
   where
      rassoc ((x,y),z) = (x,(y,z))

execMatch :: (Decl, Decl) -> Match a -> Interaction (Assignments, Mappings)
execMatch (l,r) = fmap snd . runMatch (l,r)

match :: (Arg, Int) -> (Arg, Int) -> Match ()
match (Arg ln lt, li) (Arg rn rt, ri) = do
   modify (removeName ln *** removeName rn)
   tell [((Arg ln lt, li), (Arg rn rt, ri))]

-- Smart constructors for match actions...

info :: Maybe String -> String -> Match ()
info title string = liftF $ Info title string ()

warning :: String -> Match ()
warning string = liftF $ Warning string ()

confirm :: String -> Match Bool
confirm string = liftF $ Confirm string id

offerChoice :: String -> [(String, Match a)] -> Match a
offerChoice str options =
   let (descriptions, actions) = unzip options
       numOptions = length options
   in do liftF $ Choice str descriptions ()
         userChoice <- getInBounds (1, numOptions)
         actions !! (userChoice - 1)

outOfBounds :: Int -> (Int,Int) -> Match ()
outOfBounds i (l,h) = liftF $ OutOfBounds i (l,h) ()

getInt :: Match Int
getInt = liftF $ GetInt "?" id

getInBounds :: (Int,Int) -> Match Int
getInBounds (l,h) = do
   i <- getInt
   if i <= h && i >= l
      then return i
      else do outOfBounds i (l,h)
              getInBounds (l,h)

getIntersect :: (Ord b) => (ArgMapping -> [b]) -> Match [b]
getIntersect f =
   Set.toList . uncurry Set.intersection . (both $ Set.fromList . f) <$> get

failure :: String -> Match ()
failure string =
   liftF (Failure string ()) >> lift (MaybeT (return Nothing))

userQuit :: Match ()
userQuit = failure "Matching terminated by user."

confirmOrQuit :: String -> Match ()
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
            Set.intersection (keySet (typeBins leftMapping))
                             (keySet (typeBins rightMapping))
      namesWithType typ =
         fromMaybe Set.empty
         . fmap (Set.fromList . map fst . Set.toList)
         . lookupType typ
      sharedNamesWithType typ =
         Set.toList $
            Set.intersection (namesWithType typ leftMapping)
                             (namesWithType typ rightMapping)

-- Example declarations:

dl, dr :: Decl
dl = Decl "foo" Int [Arg "y" Int, Arg "x" Int, Arg "p" Int, Arg "z" Int]
dr = Decl "bar" Int [Arg "z" Int, Arg "y" Int, Arg "p" Int, Arg "x" Int]
