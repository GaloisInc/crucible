{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE RecordWildCards  #-}

module SAWScript.AutoMatch where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Supply
import Control.Conditional (ifM)

import Data.Char
import Data.Ord
import Data.List
import Data.Maybe
import Data.Function

import Control.Conditional (whenM)
import System.FilePath

import qualified SAWScript.AST as SAWScript
--import qualified Cryptol.Parser.AST as Cryptol
import SAWScript.Builtins
import SAWScript.Options

import SAWScript.AutoMatch.ArgMapping
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util
import SAWScript.Utils

import SAWScript.AutoMatch.Interaction
import SAWScript.AutoMatch.JVM
import SAWScript.AutoMatch.LLVM
import SAWScript.AutoMatch.Cryptol

import SAWScript.LLVMBuiltins
import SAWScript.JavaBuiltins

import Text.PrettyPrint.ANSI.Leijen (putDoc, hPutDoc)

import System.IO

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
         declsByApproxName <- gets (both $ tabulateBy (approximateName . declName) .
                                           Set.toList . assertJust . Map.lookup sig)
         let matchingNames = uncurry sharedKeys $ declsByApproxName
         fencepostForM_ (separator ThickSep) matchingNames $ \name -> do
            case both (Set.toList . assertJust . Map.lookup name) declsByApproxName of
               ([leftDecl], [rightDecl]) -> do
                  (assigns, leftovers) <- lift . lift . lift . lift $
                                          matchingProcedure leftDecl rightDecl
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

autoTagSourceFiles :: FilePath -> FilePath -> Either String (TaggedSourceFile, TaggedSourceFile)
autoTagSourceFiles leftPath rightPath =
   case both autoTagSourceFile (leftPath, rightPath) of
      (Left leftExt, Left rightExt) ->
         Left $
            "Could handle neither file extension " ++
            leftExt ++ " of " ++ leftPath ++ " nor " ++
            rightExt ++ " of " ++ rightPath
      (Left leftExt, Right _) ->
         Left $
            "Couldn't handle file extension " ++
            leftExt ++ " of left-hand file " ++ leftPath
      (Right _, Left rightExt) ->
         Left $
            "Couldn't handle file extension " ++
            rightExt ++ " of right-hand file " ++ rightPath
      (Right leftSource, Right rightSource) ->
         return (leftSource, rightSource)

autoMatchFiles :: BuiltinContext -> Options
               -> TaggedSourceFile -> TaggedSourceFile
               -> IO (Interaction MatchResult)
autoMatchFiles bic opts
               leftSource@(TaggedSourceFile _ leftPath)
               rightSource@(TaggedSourceFile _ rightPath) = do
   leftModInteract  <- loadDecls bic opts leftSource
   rightModInteract <- loadDecls bic opts rightSource
   return . frame (separator SuperThickSep) $ do 
      info Nothing $ "Aligning declarations between " ++ leftPath ++ corresponds ++ rightPath
      separator ThickSep
      maybe (return $ MatchResult [] Nothing False False)
            (processResults leftSource rightSource <=< uncurry matchModules) =<<
         pairA <$> leftModInteract <*> rightModInteract

loadDecls :: BuiltinContext -> Options -> TaggedSourceFile -> IO (Interaction (Maybe [Decl]))
loadDecls bic opts (TaggedSourceFile lang path) =
   case lang of
      Cryptol -> getDeclsCryptol path
      LLVM    -> loadLLVMModule path >>= getDeclsLLVM (biSharedContext bic)
      JVM     -> loadJavaClass bic (dropExtension path) >>= getDeclsJVM bic opts

-- What to do after performing the matching procedure...
data MatchResult =
   MatchResult { generatedScript   :: [SAWScript.Stmt]
               , afterMatchSave    :: Maybe FilePath 
               , afterMatchPrint   :: Bool
               , afterMatchExecute :: Bool }

actAfterMatch :: BuiltinContext -> Options -> MatchResult -> IO ()
actAfterMatch bic opts MatchResult{..} =
   let renderedScript = SAWScript.prettyWholeModule generatedScript
   in do case afterMatchSave of
            Nothing   -> return ()
            Just file ->
               withFile file WriteMode $ \handle ->
                  hPutDoc handle renderedScript
         when afterMatchPrint   $ putDoc renderedScript
         when afterMatchExecute $ interpret bic opts generatedScript
   where
      interpret = undefined -- TODO: hook into SAWScript interpreter to execute the AST

processResults :: TaggedSourceFile -> TaggedSourceFile
               -> [(Decl, Decl, Assignments)]
               -> Interaction MatchResult
processResults (TaggedSourceFile leftLang  leftFile)
               (TaggedSourceFile rightLang rightFile)
               matchings =

      MatchResult script <$> (ifM (confirm "Save generated script to file?")
                                  (Just <$> getString "Filename:")
                                  (return Nothing))
                         <*> confirm "Print generated script to the console?"
                         <*> confirm "Execute generated script?"

   where

      nameLeft, nameRight, nameCenter :: String -> String -> String
      nameLeft   str = (("left_"  ++ str ++ "_") ++)
      nameRight  str = (("right_" ++ str ++ "_") ++)
      nameCenter str = ((str ++ "_") ++)

      loadFile :: (String -> String) -> SourceLanguage -> FilePath -> ScriptWriter (SAWScript.LName)
      loadFile prefix lang file = do
         boundName <- newNameWith prefix
         returning boundName . tell $
            case lang of
               Cryptol ->
                  [SAWScript.StmtBind (Just boundName) Nothing Nothing
                     (SAWScript.Application
                        (SAWScript.Var . locate $ "cryptol_load")
                        (SAWScript.String file))]
               LLVM ->
                  [SAWScript.StmtBind (Just boundName) Nothing Nothing
                     (SAWScript.Application
                        (SAWScript.Var . locate $ "llvm_load_module")
                        (SAWScript.String file))]
               JVM ->
                  [SAWScript.StmtBind (Just boundName) Nothing Nothing
                     (SAWScript.Application
                        (SAWScript.Var . locate $ "java_load_class")
                        (SAWScript.String $ dropExtension file))]

      extractFunction :: (String -> String) -> SourceLanguage -> String -> SAWScript.LName -> ScriptWriter (SAWScript.LName)
      extractFunction prefix lang function loadedModule = do
         boundName <- newNameWith prefix
         returning boundName . tell $
            case lang of
               Cryptol ->
                  [SAWScript.StmtBind (Just boundName) Nothing Nothing
                     (SAWScript.Application
                        (SAWScript.Application
                           (SAWScript.Var . locate $ "cryptol_extract")
                           (SAWScript.Var loadedModule))
                        (SAWScript.String function))]
               LLVM ->
                  [SAWScript.StmtBind (Just boundName) Nothing Nothing
                     (SAWScript.Application
                        (SAWScript.Application
                           (SAWScript.Application
                              (SAWScript.Var . locate $ "llvm_extract")
                              (SAWScript.Var loadedModule))
                           (SAWScript.String function))
                        (SAWScript.Var . locate $ "llvm_pure"))]
               JVM ->
                  [SAWScript.StmtBind (Just boundName) Nothing Nothing
                     (SAWScript.Application
                        (SAWScript.Application
                           (SAWScript.Application
                              (SAWScript.Var . locate $ "java_extract")
                              (SAWScript.Var loadedModule))
                           (SAWScript.String function))
                        (SAWScript.Var . locate $ "java_pure"))]

      equivalenceTheorem :: (String -> String) -> SAWScript.LName -> SAWScript.LName -> Assignments -> ScriptWriter (SAWScript.LName)
      equivalenceTheorem prefix leftFunction rightFunction assigns = do
         (leftArgs, rightArgs) <-
            fmap (both (map snd . sortBy (comparing fst)) . unzip) .
            forM assigns $
               \((Arg leftName _, leftIndex), (Arg rightName _, rightIndex)) -> do
                  name <- newNameWith (nameCenter (leftName ++ "__" ++ rightName))
                  return ((leftIndex, name), (rightIndex, name))
         return undefined

      nameCryptolFromSAW :: SAWScript.LName -> Cryptol.QName
      nameCryptolFromSAW = Cryptol.QName Nothing . Cryptol.Name . getVal

      cryptolAbstractNamesSAW :: [SAWScript.LName] -> Cryptol.Expr -> Cryptol.Expr
      cryptolAbstractNamesSAW names expr =
         Cryptol.EFun (for names $ nameCryptolFromSAW) expr

      cryptolApplyFunctionSAW :: SAWScript.LName -> [SAWScript.LName] -> Cryptol.Expr
      cryptolApplyFunctionSAW function args =
         let f  = Cryptol.EVar . nameCryptolFromSAW $ function
             as = for args $ Cryptol.EVar . nameCryptolFromSAW
         in foldl Cryptol.EApp f as

      -- TODO: Make abstract-all-arguments function out of the two above
      -- TODO: Make constructor for Cryptol equality between two expressions
      -- TODO: Invoke Cryptol pretty-printer to render the result to a string in the SAWScript AST

      prove :: SAWScript.LName -> ScriptWriter ()
      prove = undefined -- TODO: render an invocation of the prover as AST

      printString :: String -> ScriptWriter ()
      printString string = tell $
         [SAWScript.StmtBind Nothing Nothing Nothing
             (SAWScript.Application
                (SAWScript.Var . locate $ "print")
                (SAWScript.String string))]

      locate :: String -> SAWScript.LName
      locate name =
         SAWScript.Located name "" (PosInternal "generated by auto_match")

      newNameWith :: (String -> String) -> ScriptWriter (SAWScript.LName)
      newNameWith prefix = locate . prefix <$> supply

      script :: [SAWScript.Stmt]
      script = flip evalSupply (map show [(0 :: Integer) ..]) . execWriterT $ do
         leftModule  <- loadFile (nameLeft  "module") leftLang  leftFile
         rightModule <- loadFile (nameRight "module") rightLang rightFile
         forM_ matchings $ \(leftDecl, rightDecl, assigns) -> do
            leftFunction  <- extractFunction (nameLeft  "function") leftLang  (declName leftDecl)  leftModule
            rightFunction <- extractFunction (nameRight "function") rightLang (declName rightDecl) rightModule
            theorem       <- equivalenceTheorem (nameCenter "theorem") leftFunction rightFunction assigns
            printString $ "Proving " ++ declName leftDecl  ++ " from " ++ leftFile ++
                              " == " ++ declName rightDecl ++ " from " ++ rightFile
            prove theorem

type ScriptWriter = WriterT [SAWScript.Stmt] (Supply String)

autoMatch :: BuiltinContext -> Options -> FilePath -> FilePath -> IO ()
autoMatch bic opts leftFile rightFile =
   autoTagSourceFiles leftFile rightFile &
      (either putStrLn $ 
         uncurry (autoMatchFiles bic opts) >=> interactIO >=> actAfterMatch bic opts)
