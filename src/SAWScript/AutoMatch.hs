{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE ViewPatterns     #-}

module SAWScript.AutoMatch where

import qualified Data.Map as Map
import           Data.Map   (Map)
import qualified Data.Set as Set
import           Data.Set   (Set)

import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Arrow ((***), (&&&), second)

import Data.Maybe
import Data.Char
import Data.Ord
import Data.List

import Control.Conditional (whenM)
import Text.Read (readMaybe)
import System.FilePath
import System.Console.Terminal.Size

import SAWScript.Builtins
import SAWScript.LLVMBuiltins
import SAWScript.JavaBuiltins
import SAWScript.Options
import qualified Verifier.Java.Simulator as JSS hiding (lookupClass)
import SAWScript.Value as SV

import SAWScript.AutoMatch.ArgMapping
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

import SAWScript.AutoMatch.JVM
import SAWScript.AutoMatch.LLVM
import SAWScript.AutoMatch.Cryptol

-- A free monad...

type Interaction = Free InteractionF

data InteractionF a =
  -- output:
    Info (Maybe String) String a
  | Warning String a
  | Choice String [String] a
  | OutOfBounds Int (Int,Int) a
  | Failure String a
  | ThickSeparator a
  | ThinSeparator a
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
         ThickSeparator k ->
            putStrLn 
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

initialInfo :: ArgMatch ()
initialInfo = do
   (left, right) <- ask
   info (Just "Comparing") $ show left ++
          "\n           " ++ show right

checkReturnTypeCompat :: ArgMatch ()
checkReturnTypeCompat = do
   (left, right) <- ask
   when (declType left /= declType right) $
      failure $
         "The declarations (" ++
         declName left ++ " : ... " ++ show (declType left) ++
         ") and (" ++
         declName right ++ " : ... " ++ show (declType right) ++
         ") do not match in return type, and so cannot be reconciled."

checkSignatureCompat :: ArgMatch ()
checkSignatureCompat = do
   (left, right) <- ask
   whenM (uncurry (/=) . both (fmap Set.size . typeBins) <$> get) $ do
      warning $
         "The signatures for '" ++ declName left ++
         "' and '" ++ declName right ++ 
         "' cannot be aligned by permutation."
      confirmOrQuit "Proceed with matching anyway?"

processExactMatches :: ArgMatch ()
processExactMatches = do
   exactMatches <- findExactMatches <$> get
   forM_ exactMatches $ \((arg1, i1), (arg2, i2)) -> do
      matchArgs (arg1, i1) (arg2, i2)
      info (Just "Exact match") $
         "(" ++ show arg1 ++ ")" ++ " at " ++
         formatIndex i1 ++ corresponds ++ formatIndex i2

checkNameClashes :: ArgMatch ()
checkNameClashes = do
   sharedNames <- getIntersect (Map.keys . nameLocs)
   forM_ sharedNames $ \name -> do
      ((li, lt), (ri, rt)) <- (both $ assertJust . lookupName name) <$> get -- assertJust *just*ified
      warning $                                                             -- b/c name is definitely in map
         "Arguments " ++ formatIndexedArg False name lt li ++
         corresponds  ++ formatIndexedArg False name rt ri ++
         " are named identically, but have differing types."
      confirmOrQuit "Proceed with matching by considering them distinct?"

matchInteractively :: ArgMatch ()
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

type Match r w s a =
   ReaderT r                            -- information about initial declarations
      (MaybeT                                      -- possible early termination
         (WriterT [w]                          -- append-only output of matched results
                  (StateT s                    -- remaining arguments on each side
                          Interaction))) a         -- free monad of instructions to execute

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

getIntersect :: (Ord b) => (s -> [b]) -> Match r w (s,s) [b]
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

matchModules :: (String, [Decl]) -> (String, [Decl]) -> Interaction [(Decl, Decl, Assignments)]
matchModules (leftFilename, leftModule) (rightFilename, rightModule) =
   fmap (fst . snd) . runMatch () (both (tabulateBy declSig) (leftModule, rightModule)) $ do

      info Nothing $ "Aligning module declarations between " ++ leftFilename ++ corresponds ++ rightFilename
      sharedSigs <- gets $ uncurry sharedKeys
      forM_ sharedSigs $ \sig -> do
         declsByApproxName <- gets (both $ tabulateBy (approximateName . declName) . Set.toList . assertJust . Map.lookup sig)
         let matchingNames = uncurry sharedKeys $ declsByApproxName
         forM_ matchingNames $ \name -> do
            case both (Set.toList . assertJust . Map.lookup name) declsByApproxName of
               ([leftDecl], [rightDecl]) -> do
                  (assigns, leftovers) <- lift . lift . lift . lift $ matchingProcedure leftDecl rightDecl
                  if uncurry (&&) (both isEmptyArgMapping leftovers)
                     then matchDecls leftDecl rightDecl assigns
                     else return ()
               _ -> undefined -- TODO: what to do if multiple names match on either side

            -- TODO: provide interactive matching of remaining functions binned in signature

         -- TODO: more inexact name matching

      -- Report unmatched declarations
      (unselectedL, unselectedR) <- gets (both $ concatMap Set.toList . Map.elems)
      forM_ unselectedL $ \decl ->
         warning $ "Failed to find potential match for left-side declaration " ++ show decl
      forM_ unselectedR $ \decl ->
         warning $ "Failed to find potential match for right-side declaration " ++ show decl

type DeclMatch a = Match () (Decl,Decl,Assignments) (Map Sig (Set Decl),Map Sig (Set Decl)) a

matchDecls :: Decl -> Decl -> Assignments -> DeclMatch ()
matchDecls ld rd as = do
   modify (deleteFromSetMap (declSig ld) ld *** deleteFromSetMap (declSig rd) rd)
   tell [(ld, rd, as)]

sharedKeys :: (Ord k) => Map k v -> Map k v -> [k]
sharedKeys = curry $ Set.toList . uncurry Set.intersection . both Map.keysSet

tabulateBy :: (Ord k, Ord v) => (v -> k) -> [v] -> Map k (Set v)
tabulateBy f = Map.fromListWith Set.union . map (f &&& Set.singleton)

associateSetWith :: (Ord k) => (k -> v) -> Set k -> Map k v
associateSetWith f = Map.fromAscList . map (id &&& f) . Set.toAscList

approximateName :: Name -> Name
approximateName =
   filter (not . (`elem` "_- ")) . map toLower

--matchModules :: [Decl] -> [Decl] -> Interaction [(Decl, Decl, Assignments)]
--matchModules leftModule rightModule = do
--   matchingDecls <- fst <$> findDeclMatches leftModule rightModule
--   fmap catMaybes . forM matchingDecls $ \(leftDecl, rightDecl) -> do
--      (assigns, leftovers) <- matchingProcedure leftDecl rightDecl
--      if uncurry (&&) (both isEmptyArgMapping leftovers)
--         then return . Just $ (leftDecl, rightDecl, assigns)
--         else return Nothing

data SourceLanguage = Cryptol | JVM | LLVM deriving (Eq, Ord, Show)

data TaggedSourceFile =
   TaggedSourceFile { sourceLanguage :: SourceLanguage
                    , sourceFilePath :: FilePath } deriving (Eq, Ord, Show)

autoTagSourceFile :: FilePath -> Either String TaggedSourceFile
autoTagSourceFile path = case takeExtension path of
   ".cry"   -> Right $ TaggedSourceFile Cryptol path
   ".bc"    -> Right $ TaggedSourceFile LLVM    path
   ".class" -> Right $ TaggedSourceFile JVM     path
   ext      -> Left ext

printMatchesJVM :: BuiltinContext -> Options -> JSS.Class -> JSS.Class -> {- JavaSetup () -> -} IO ()
printMatchesJVM bic opts leftClass rightClass {- _setup -} = do
   leftDecls  <- getDeclsJVM bic opts leftClass
   rightDecls <- getDeclsJVM bic opts rightClass
   print =<< interactIO (matchModules leftDecls rightDecls)

printMatchesLLVM :: BuiltinContext -> Options -> LLVMModule -> LLVMModule -> {- LLVMSetup () -> -} IO ()
printMatchesLLVM bic _opts leftModule rightModule {- _setup -} =
   let sc = biSharedContext bic in do
      leftDecls  <- getDeclsLLVM sc leftModule
      rightDecls <- getDeclsLLVM sc rightModule
      print =<< interactIO (matchModules leftDecls rightDecls)

autoMatchFiles :: BuiltinContext -> Options -> FilePath -> FilePath -> IO (Either String (Interaction [(Decl, Decl, Assignments)]))
autoMatchFiles bic opts leftPath rightPath =
   case both autoTagSourceFile (leftPath, rightPath) of
      (Left leftExt, Left rightExt) ->
         return . Left $ "Could handle neither file extension " ++ leftExt ++ " of " ++ leftPath ++ " nor " ++ rightExt ++ " of " ++ rightPath
      (Left leftExt, Right _) ->
         return . Left $ "Couldn't handle file extension " ++ leftExt ++ " of left-hand file " ++ leftPath
      (Right _, Left rightExt) ->
         return . Left $ "Couldn't handle file extension " ++ rightExt ++ " of right-hand file " ++ rightPath
      (Right leftSource, Right rightSource) -> do
         leftModule  <- loadDecls bic opts leftSource
         rightModule <- loadDecls bic opts rightSource
         return . Right $ matchModules leftModule rightModule

autoMatchPrint :: BuiltinContext -> Options -> FilePath -> FilePath -> IO ()
autoMatchPrint bic opts left right =
   either print (print <=< interactIO) =<< autoMatchFiles bic opts left right

loadDecls :: BuiltinContext -> Options -> TaggedSourceFile -> IO (String,[Decl])
loadDecls bic opts (TaggedSourceFile lang path) =
   case lang of
      Cryptol -> getDeclsCryptol path
      LLVM    -> loadLLVMModule path >>= getDeclsLLVM (biSharedContext bic)
      JVM     -> loadJavaClass bic (dropExtension path) >>= getDeclsJVM bic opts
