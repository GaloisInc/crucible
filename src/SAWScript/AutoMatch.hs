{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE ViewPatterns     #-}

module SAWScript.AutoMatch where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader

import Data.Char
import Data.Ord
import Data.List
import Data.Maybe

import Control.Conditional (whenM)
import System.FilePath

import SAWScript.Builtins
import SAWScript.Options

import SAWScript.AutoMatch.ArgMapping
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

import SAWScript.AutoMatch.Interaction
import SAWScript.AutoMatch.JVM
import SAWScript.AutoMatch.LLVM
import SAWScript.AutoMatch.Cryptol

import SAWScript.LLVMBuiltins
import SAWScript.JavaBuiltins

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
      failure True $
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
   forM_ exactMatches $ uncurry matchArgs
   separator ThinSep
   when (not . null $ exactMatches) $ do
      info Nothing "Exact matches:"
      bulleted . for exactMatches $
         \((arg1, i1), (_arg2, i2)) ->
            "(" ++ show arg1 ++ ")" ++ " at " ++
            formatIndex i1 ++ corresponds ++ formatIndex i2
      separator ThinSep

checkNameClashes :: ArgMatch ()
checkNameClashes = do
   sharedNames <- getIntersect (Map.keys . nameLocs)
   fencepostForM_ (separator ThinSep) sharedNames $ \name -> do
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
             ([],_) -> separator ThinSep >> return ()
             (_,[]) -> separator ThinSep >> return ()
             (leftArgs@((ln, li):_), rightArgs) -> do
                separator ThinSep
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

getIntersect :: (Ord b) => (s -> [b]) -> Match r w (s,s) [b]
getIntersect f =
   Set.toList . uncurry Set.intersection . (both $ Set.fromList . f) <$> get

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

matchModules :: [Decl] -> [Decl] -> Interaction [(Decl, Decl, Assignments)]
matchModules leftModule rightModule =
   runMatchModules leftModule rightModule $ do
      sharedSigs <- gets $ uncurry sharedKeys
      forM_ sharedSigs $ \sig -> do
         declsByApproxName <- gets (both $ tabulateBy (approximateName . declName) . Set.toList . assertJust . Map.lookup sig)
         let matchingNames = uncurry sharedKeys $ declsByApproxName
         fencepostForM_ (separator ThickSep) matchingNames $ \name -> do
            case both (Set.toList . assertJust . Map.lookup name) declsByApproxName of
               ([leftDecl], [rightDecl]) -> do
                  (assigns, leftovers) <- lift . lift . lift . lift $ matchingProcedure leftDecl rightDecl
                  if uncurry (&&) (both isEmptyArgMapping leftovers)
                     then matchDecls leftDecl rightDecl assigns
                     else return ()
               _ -> return ()

            -- TODO: provide interactive matching of remaining functions binned in signature

         -- TODO: more inexact name matching

      -- Report unmatched declarations
      (unselectedL, unselectedR) <- gets (both $ concatMap Set.toList . Map.elems)
      when (not . null $ unselectedL) $ do
         warning "Did not find matches for left-side declarations:"
         bulleted $ map show unselectedL
      separator ThinSep
      when (not . null $ unselectedR) $ do
         warning "Did not find matches for right-side declarations:"
         bulleted $ map show unselectedR

approximateName :: Name -> Name
approximateName =
   filter (not . (`elem` "_- ")) . map toLower

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

autoMatchFiles :: BuiltinContext -> Options -> FilePath -> FilePath -> IO (Interaction [(Decl, Decl, Assignments)])
autoMatchFiles bic opts leftPath rightPath =
   case both autoTagSourceFile (leftPath, rightPath) of
      (Left leftExt, Left rightExt) ->
         returning (return []) . print $
            "Could handle neither file extension " ++ leftExt ++ " of " ++ leftPath ++ " nor " ++ rightExt ++ " of " ++ rightPath
      (Left leftExt, Right _) ->
         returning (return []) . print $
            "Couldn't handle file extension " ++ leftExt ++ " of left-hand file " ++ leftPath
      (Right _, Left rightExt) ->
         returning (return []) . print $
            "Couldn't handle file extension " ++ rightExt ++ " of right-hand file " ++ rightPath
      (Right leftSource, Right rightSource) -> do
         leftModuleInteraction  <- loadDecls bic opts leftSource
         rightModuleInteraction <- loadDecls bic opts rightSource
         return . frame (separator SuperThickSep) $ do 
            info Nothing $ "Aligning declarations between " ++ leftPath ++ corresponds ++ rightPath
            separator ThickSep
            mlm <- leftModuleInteraction
            mrm <- rightModuleInteraction
            case (mlm, mrm) of
               (Just leftModule, Just rightModule) -> matchModules leftModule rightModule
               _                                   -> return []

autoMatchPrint :: BuiltinContext -> Options -> FilePath -> FilePath -> IO ()
autoMatchPrint bic opts left right =
   print =<< interactIO =<< autoMatchFiles bic opts left right

loadDecls :: BuiltinContext -> Options -> TaggedSourceFile -> IO (Interaction (Maybe [Decl]))
loadDecls bic opts (TaggedSourceFile lang path) =
   case lang of
      Cryptol -> getDeclsCryptol path
      LLVM    -> loadLLVMModule path >>= getDeclsLLVM (biSharedContext bic)
      JVM     -> loadJavaClass bic (dropExtension path) >>= getDeclsJVM bic opts
