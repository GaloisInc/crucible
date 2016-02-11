{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP              #-}

module SAWScript.AutoMatch.Interaction where

import System.IO
import qualified System.Console.Terminal.Size as Window

import SAWScript.AutoMatch.ArgMapping
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

import Data.Map   (Map)
import Data.Set   (Set)

import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Arrow ((***), second)
import Text.Read (readMaybe)
import Data.Maybe
import Data.Char

-- | A pure description of a user interaction by means of a free monad
type Interaction = Free InteractionF

data InteractionF a =
  -- output:
    Info (Maybe String) String a
  | Warning String a
  | Choice String [String] a
  | OutOfBounds Int (Int,Int) a
  | Failure Bool String a
  | Bulleted [String] a
  | Separator Separator a
  -- input:
  | Confirm String (Bool -> a)
  | GetInt String (Int -> a)
  | GetString String (String -> a)
  deriving (Functor)

-- | The obvious interpretation of an interaction into IO
--   The only real complexity here is that we collapse horizontal separators together
--   so that multiple adjacent separators will be printed as a single separator as thick
--   as the largest one called for by the interaction.
interactIO :: Interaction a -> IO a
interactIO program = do
   hSetBuffering stdin  NoBuffering
   hSetBuffering stdout NoBuffering
   flip evalStateT Nothing $ interactIO' program
   where
      checkSep :: StateT (Maybe Separator) IO ()
      checkSep = do
         maybe (return ()) (liftIO . printSeparator) =<< get
         put Nothing

      putSep :: Separator -> StateT (Maybe Separator) IO ()
      putSep sep = modify $ maybe (Just sep) (Just . (max sep))

      checkThenIOWithCont :: Interaction a -> IO b ->  StateT (Maybe Separator) IO a
      checkThenIOWithCont k action = checkSep >> liftIO action >> interactIO' k

      interactIO' :: Interaction a -> StateT (Maybe Separator) IO a
      interactIO' interaction =
         case interaction of
            Pure a -> checkSep >> return a
            Free a -> case a of
               Separator sep k ->
                  putSep sep >> interactIO' k
               Info title str k ->
                  checkThenIOWithCont k $ putStrLn (fromMaybe "Info" title ++ ": " ++ str)
               Warning str k ->
                  checkThenIOWithCont k $ putStrLn ("Warning: " ++ str)
               Bulleted strs k ->
                  checkThenIOWithCont k . forM_ strs $ putStrLn . ("*  " ++)
               Choice str opts k ->
                  checkThenIOWithCont k $ do
                     putStrLn str
                     forM_ (zip [1..] opts) $ \(i, opt) ->
                        putStrLn $ show (i :: Int) ++ ". " ++ opt
               OutOfBounds _ (l,h) k -> do
                  checkThenIOWithCont k $ putStrLn ("Please enter an integer between " ++ show l ++ " and " ++ show h ++ ".")
               Failure printFailure str k ->
                  checkThenIOWithCont k $ putStrLn ((if printFailure then "Failure: " else "") ++ str)
               Confirm str f -> do
                  checkSep
                  liftIO $ putStr ("Confirm: " ++ str ++ " ")
                  fix $ \loop -> do
                     input <- liftIO $ map toLower <$> getLine
                     case filter snd . map (second $ elem input)
                          . zip [True, False] $ [yes, no] of
                        (b,_):_ -> interactIO' (f b)
                        []      -> liftIO (putStr "Please enter either 'yes' or 'no': ") >> loop
               GetInt str f -> do
                  checkSep
                  result <- fix $ \loop -> do
                     liftIO $ putStr (str ++ " ")
                     maybe (liftIO (putStr "Please enter an integer: ") >> loop) (interactIO' . f) . readMaybe =<< liftIO getLine
                  return result
               GetString str f -> do
                  checkSep
                  liftIO $ putStr (str ++ " ")
                  interactIO' . f =<< liftIO getLine

-- | A list of assignments between the arguments of two declarations
type Assignments = [((Arg, Int), (Arg, Int))]

-- | A pair of ArgMappings
type Mappings    = (ArgMapping, ArgMapping)

-- | The monad stack in which we write most of our interaction code
--   We can read the initial declarations we're working with (ReaderT),
--   write out matches we've identified (WriterT),
--   remove things from consideration (StateT),
--   and possibly terminate early (MaybeT),
--   all while being able to talk to the user (Interaction)
type Match r w s a =
   ReaderT r                                   -- information about initial declarations
      (MaybeT                                  -- possible early termination
         (WriterT [w]                          -- append-only output of matched results
                  (StateT s                    -- remaining arguments on each side
                          Interaction))) a     -- free monad of instructions to execute

-- | Boil off the monad stack to get down to an Interaction
--   Needs starting read-only and writeable states
runMatch :: r -> s -> Match r w s a -> Interaction (Maybe a, ([w], s))
runMatch r s =
   fmap rassoc
   . flip runStateT s
   . runWriterT
   . runMaybeT
   . flip runReaderT r
   where
      rassoc ((x,y),z) = (x,(y,z))

-- | An ArgMatch is a computation which is sourced from two declarations,
--   produces a stream of pairs of index-paired Args,
--   and removes arguments from a pair of ArgMappings as it goes.
type ArgMatch a = Match (Decl,Decl) ((Arg,Int),(Arg,Int)) (ArgMapping,ArgMapping) a

-- | A DeclMatch is a computation which produces a stream of triples:
--   two decls and a list of argument assignments between them,
--   and removes declarations from a collection of signatures multi-mapped to declarations.
type DeclMatch a = Match () (Decl,Decl,Assignments) (Map Sig (Set Decl),Map Sig (Set Decl)) a

-- | Match two declarations together with the given assignments of arguments
--   Removes the two of them from consideration and dumps the matching into the output stream
matchDecls :: Decl -> Decl -> Assignments -> DeclMatch ()
matchDecls ld rd as = do
   modify (deleteFromSetMap (declSig ld) ld *** deleteFromSetMap (declSig rd) rd)
   tell [(ld, rd, as)]

-- | If the Match has no interesting information, boil the layers off to get an Interaction
runVoidMatch :: Match () () () a -> Interaction (Maybe a)
runVoidMatch = fmap fst . runMatch () ()

-- | Given two lists of declarations representing modules and a computation which computes their
--   matches, run the computation and produce an interaction giving the result.
runMatchModules :: [Decl] -> [Decl] -> DeclMatch a -> Interaction [(Decl,Decl,Assignments)]
runMatchModules leftModule rightModule =
   fmap (fst . snd) . runMatch () (both (tabulateBy declSig) (leftModule, rightModule))

-- | Given two declarations and a computation which computes their matches, run the computation
--   and produce an interaction giving the result.
runMatchDecls :: (Decl, Decl) -> ArgMatch a -> Interaction (Maybe a, (Assignments, Mappings))
runMatchDecls (l,r) = runMatch (l,r) (both (makeArgMapping . declArgs) (l,r))

-- | Like runMatchDecls but we don't care about what the ArgMatch computation returned
execMatchDecls :: (Decl, Decl) -> ArgMatch a -> Interaction (Assignments, Mappings)
execMatchDecls (l,r) = fmap snd . runMatchDecls (l,r)

-- | Match two arguments at given indices together
--   Removes the two of them from consideration and dumps the matching into the output stream
matchArgs :: (Arg, Int) -> (Arg, Int) -> ArgMatch ()
matchArgs (Arg ln lt, li) (Arg rn rt, ri) = do
   modify (removeName ln *** removeName rn)
   tell [((Arg ln lt, li), (Arg rn rt, ri))]

-- Smart constructors for match actions...

-- | Print information to the user
info :: MonadFree InteractionF m => Maybe String -> String -> m ()
info title string = liftF $ Info title string ()

-- | Print a bulleted list of the given strings
bulleted :: MonadFree InteractionF m => [String] -> m ()
bulleted strings = liftF $ Bulleted strings ()

-- | Warn the user about something
warning :: MonadFree InteractionF m => String -> m ()
warning string = liftF $ Warning string ()

-- | Ask the user for confirmation of some question
confirm :: MonadFree InteractionF m => String -> m Bool
confirm string = liftF $ Confirm string id

-- | Offer the user multiple choices and execute the action which corresponds to their selection
offerChoice :: MonadFree InteractionF m => String -> [(String, m a)] -> m a
offerChoice str opts =
   let (descriptions, actions) = unzip opts
       numOpts = length opts
   in do liftF $ Choice str descriptions ()
         userChoice <- getInBounds (1, numOpts)
         actions !! (userChoice - 1)

-- | Report an out-of-bounds error to the user (internal use only)
outOfBounds :: MonadFree InteractionF m => Int -> (Int,Int) -> m ()
outOfBounds i (l,h) = liftF $ OutOfBounds i (l,h) ()

-- | Get an integer from the user
getInt :: MonadFree InteractionF m => m Int
getInt = liftF $ GetInt "?" id

-- | Get a string from the user, showing a particular prompt
getString :: MonadFree InteractionF m => String -> m String
getString str = liftF $ GetString str id

-- | Get an integer from the user in a particular range, asking again and again until they comply
getInBounds :: MonadFree InteractionF m => (Int,Int) -> m Int
getInBounds (l,h) = do
   i <- getInt
   if i <= h && i >= l
      then return i
      else do outOfBounds i (l,h)
              getInBounds (l,h)

-- | Terminate the interaction, printing an error message
--   The printFailure flag indicates whether or not to use the word "Failure" in the message
--   (sometimes we don't really want to castigate the user!)
failure :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => Bool -> String -> t (MaybeT m) b
failure printFailure string =
   liftF (Failure printFailure string ()) >> lift (MaybeT (return Nothing))

-- | Terminate the interaction because the user said to do so in some manner
userQuit :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => t (MaybeT m) b
userQuit = failure False "Matching terminated by user."

-- | Ask the user whether they want to continue (phrasing up to the programmer) and quit if not
confirmOrQuit :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m)), Functor (t (MaybeT m))) => String -> t (MaybeT m) ()
confirmOrQuit str = do
   r <- confirm str
   when (not r) userQuit

-- | Symbolic representation of horizontal separators printable during interaction
data Separator = SuperThinSep | ThinSep | ThickSep | SuperThickSep deriving (Eq, Ord, Show)

-- | Print a separator of the given thickness
separator :: MonadFree InteractionF m => Separator -> m ()
separator = liftF . flip Separator ()

-- | Actually print a separator in IO -- separators assume the width of the terminal,
--   or 80 characters if we can't figure out what width the terminal is.
printSeparator :: Separator -> IO ()
printSeparator sep =
   printSeparatorWith $ case sep of
      SuperThinSep  -> ". "
      ThinSep       -> "- "
      ThickSep      -> "="
      SuperThickSep -> "#"
   where
      printSeparatorWith string =
         putStrLn . flip take (cycle string) =<< fromMaybe 80 <$> fmap Window.width <$> Window.size
