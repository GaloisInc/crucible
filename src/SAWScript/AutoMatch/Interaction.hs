{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}

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
import Control.Arrow ((***), second)
import Control.Conditional (whenM)
import Text.Read (readMaybe)
import Data.Maybe
import Data.Char

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
  deriving (Functor)

-- And (one possible) interpretation for it into IO...

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
                  result <- fix $ \loop -> do
                     liftIO $ putStr (str ++ " ")
                     maybe (liftIO (putStrLn "Please enter an integer.") >> loop) (interactIO' . f) . readMaybe =<< liftIO getLine
                  checkSep
                  return result

type Assignments = [((Arg, Int), (Arg, Int))]
type Mappings    = (ArgMapping, ArgMapping)

type Match r w s a =
   ReaderT r                                   -- information about initial declarations
      (MaybeT                                  -- possible early termination
         (WriterT [w]                          -- append-only output of matched results
                  (StateT s                    -- remaining arguments on each side
                          Interaction))) a     -- free monad of instructions to execute

runMatch :: r -> s -> Match r w s a -> Interaction (Maybe a, ([w], s))
runMatch r s =
   fmap rassoc
   . flip runStateT s
   . runWriterT
   . runMaybeT
   . flip runReaderT r
   where
      rassoc ((x,y),z) = (x,(y,z))

type ArgMatch a = Match (Decl,Decl) ((Arg,Int),(Arg,Int)) (ArgMapping,ArgMapping) a

type DeclMatch a = Match () (Decl,Decl,Assignments) (Map Sig (Set Decl),Map Sig (Set Decl)) a

matchDecls :: Decl -> Decl -> Assignments -> DeclMatch ()
matchDecls ld rd as = do
   modify (deleteFromSetMap (declSig ld) ld *** deleteFromSetMap (declSig rd) rd)
   tell [(ld, rd, as)]

runVoidMatch :: Match () () () a -> Interaction (Maybe a)
runVoidMatch = fmap fst . runMatch () ()

runMatchModules :: [Decl] -> [Decl] -> DeclMatch a -> Interaction [(Decl,Decl,Assignments)]
runMatchModules leftModule rightModule =
   fmap (fst . snd) . runMatch () (both (tabulateBy declSig) (leftModule, rightModule))

runMatchDecls :: (Decl, Decl) -> ArgMatch a -> Interaction (Maybe a, (Assignments, Mappings))
runMatchDecls (l,r) = runMatch (l,r) (both (makeArgMapping . declArgs) (l,r))

execMatchDecls :: (Decl, Decl) -> ArgMatch a -> Interaction (Assignments, Mappings)
execMatchDecls (l,r) = fmap snd . runMatchDecls (l,r)

matchArgs :: (Arg, Int) -> (Arg, Int) -> ArgMatch ()
matchArgs (Arg ln lt, li) (Arg rn rt, ri) = do
   modify (removeName ln *** removeName rn)
   tell [((Arg ln lt, li), (Arg rn rt, ri))]

-- Smart constructors for match actions...

info :: MonadFree InteractionF m => Maybe String -> String -> m ()
info title string = liftF $ Info title string ()

bulleted :: MonadFree InteractionF m => [String] -> m ()
bulleted strings = liftF $ Bulleted strings ()

warning :: MonadFree InteractionF m => String -> m ()
warning string = liftF $ Warning string ()

confirm :: MonadFree InteractionF m => String -> m Bool
confirm string = liftF $ Confirm string id

offerChoice :: MonadFree InteractionF m => String -> [(String, m a)] -> m a
offerChoice str opts =
   let (descriptions, actions) = unzip opts
       numOpts = length opts
   in do liftF $ Choice str descriptions ()
         userChoice <- getInBounds (1, numOpts)
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

failure :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => Bool -> String -> t (MaybeT m) b
failure printFailure string =
   liftF (Failure printFailure string ()) >> lift (MaybeT (return Nothing))

userQuit :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => t (MaybeT m) b
userQuit = failure False "Matching terminated by user."

confirmOrQuit :: (Monad m, MonadTrans t, MonadFree InteractionF (t (MaybeT m))) => String -> t (MaybeT m) ()
confirmOrQuit str =
   whenM (not <$> confirm str) userQuit

data Separator = SuperThinSep | ThinSep | ThickSep | SuperThickSep deriving (Eq, Ord, Show)

separator :: MonadFree InteractionF m => Separator -> m ()
separator = liftF . flip Separator ()

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
