{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE ViewPatterns     #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE CPP              #-}

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
import Control.Monad.IfElse (awhen)

import Data.Char
import Data.Ord
import Data.List
import Data.Maybe
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import Control.Conditional (whenM)
import System.FilePath

import qualified SAWScript.AST as SAWScript
import qualified Cryptol.Parser.AST      as Cryptol
import qualified Cryptol.Parser.Position as Cryptol
import qualified Cryptol.Utils.PP        as Cryptol
import SAWScript.Builtins
--import SAWScript.Options
import SAWScript.Utils
import SAWScript.TopLevel
import SAWScript.Value
--import Verifier.SAW.SharedTerm

import SAWScript.AutoMatch.ArgMapping
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

import SAWScript.AutoMatch.Interaction
import SAWScript.AutoMatch.JVM
import SAWScript.AutoMatch.LLVM
import SAWScript.AutoMatch.Cryptol

import SAWScript.LLVMBuiltins
--import SAWScript.JavaBuiltins
import Language.JVM.Common (dotsToSlashes)

import Text.PrettyPrint.ANSI.Leijen (putDoc, hPutDoc)

import System.IO

#if MIN_VERSION_base(4,8,0)
import Data.Function
#endif

-- | The interactive procedure for matching two given function declarations
matchingProcedure :: Decl -> Decl -> Interaction (Assignments, Mappings)
matchingProcedure left right =
   execMatchDecls (left, right) . sequence_ $
      [ initialInfo
      , checkReturnTypeCompat
      , checkSignatureCompat
      , processExactMatches
      , checkNameClashes
      , matchInteractively ]

-- | Print information about the two declarations about to be matched
initialInfo :: ArgMatch ()
initialInfo = do
   (left, right) <- ask
   info (Just "Comparing") $ show left ++
          "\n           " ++ show right

-- | Fail matching if the two declarations differ in return type
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

-- | Fail matching if the two declarations have argument types which aren't permutations of each other
checkSignatureCompat :: ArgMatch ()
checkSignatureCompat = do
   (left, right) <- ask
   whenM (uncurry (/=) . both (fmap Set.size . typeBins) <$> get) $ do
      warning $
         "The signatures for '" ++ declName left ++
         "' and '" ++ declName right ++ 
         "' cannot be aligned by permutation."
      confirmOrQuit "Proceed with matching anyway?"

-- | Automatically equate all arguments which match exactly in type and name
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

-- | Interactively warn when any arguments of *different* types have the same name -- this is likely a user error
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

-- | Walk through the remaining unmatched declarations asking the user to align them
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

-- | Project from the (s,s) state a list of the intersection of return values
--   from the function on both parts of the state
getIntersect :: (Ord b) => (s -> [b]) -> Match r w (s,s) [b]
getIntersect f =
   Set.toList . uncurry Set.intersection . (both $ Set.fromList . f) <$> get

-- | Compute exact matches (name & type) between two ArgMappings:
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

-- | The interactive procedure to match declarations between two whole modules
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

-- | Names are approximately equal if they are equal modulo
--   spaces, underscores, hyphens, and capitalization
approximateName :: Name -> Name
approximateName =
   filter (not . (`elem` "_- ")) . map toLower

-- | Source langauges we support
data SourceLanguage = Cryptol | JVM | LLVM deriving (Eq, Ord, Show)

-- | A filepath tagged with its language of origin
data TaggedSourceFile =
   TaggedSourceFile { sourceLanguage :: SourceLanguage
                    , sourceFilePath :: FilePath } deriving (Eq, Ord, Show)

-- | Try to recognize the source language of a filepath, and tag it if we know how
autoTagSourceFile :: FilePath -> Either String TaggedSourceFile
autoTagSourceFile path = case takeExtension path of
   ".cry"   -> Right $ TaggedSourceFile Cryptol path
   ".bc"    -> Right $ TaggedSourceFile LLVM    path
   ".class" -> Right $ TaggedSourceFile JVM     path
   ext      -> Left ext

-- | Try to tag both files and fail with a descriptive error if either cannot be recognized
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

-- | Take two tagged source files and load them up to generate an interaction which matches the modules together
autoMatchFiles :: TaggedSourceFile -> TaggedSourceFile -> TopLevel (Interaction MatchResult)
autoMatchFiles leftSource@(TaggedSourceFile _ leftPath) rightSource@(TaggedSourceFile _ rightPath) = do
   leftModInteract  <- loadDecls leftSource
   rightModInteract <- loadDecls rightSource
   return . frame (separator SuperThickSep) $ do 
      info Nothing $ "Aligning declarations between " ++ leftPath ++ corresponds ++ rightPath
      separator ThickSep
      maybe (return $ MatchResult [] Nothing False False)
            (processResults leftSource rightSource <=< uncurry matchModules) =<<
         pairA <$> leftModInteract <*> rightModInteract

-- | Load the declarations from the given file, dispatching on the source language to determine how to do this
loadDecls :: TaggedSourceFile -> TopLevel (Interaction (Maybe [Decl]))
loadDecls (TaggedSourceFile lang path) = do
   sc <- getSharedContext
   case lang of
      Cryptol -> io $ getDeclsCryptol path
      LLVM    -> io $ loadLLVMModule path >>= getDeclsLLVM sc
      JVM     -> loadJavaClassTopLevel (dropExtension path) >>= io . getDeclsJVM
   where
      loadJavaClassTopLevel cls = do 
         javaCodebase <- getJavaCodebase
         io . lookupClass javaCodebase fixPos . dotsToSlashes $ cls

-- A description of the result of matching: some generated SAWScript, and some flags determining what to do now
data MatchResult =
   MatchResult { generatedScript   :: [SAWScript.Stmt]
               , afterMatchSave    :: Maybe FilePath 
               , afterMatchPrint   :: Bool
               , afterMatchExecute :: Bool }

-- | The type of the line-by-line interpreter, which needs to be passed in another module to avoid circularity
type StmtInterpreter = TopLevelRO -> TopLevelRW -> [SAWScript.Stmt] -> IO Value

-- | How to interpret a MatchResult to the TopLevel monad
actAfterMatch :: StmtInterpreter -> MatchResult -> TopLevel ()
actAfterMatch interpretStmts MatchResult{..} =
   let renderedScript = SAWScript.prettyWholeModule generatedScript
   in do io . awhen afterMatchSave $ \file ->
                 withFile file WriteMode $ \handle ->
                     hPutDoc handle renderedScript
         io . when afterMatchPrint $ putDoc renderedScript
         when afterMatchExecute $ interpret generatedScript
   where
      interpret script = do
         ro <- getTopLevelRO
         rw <- getTopLevelRW
         io . void $ interpretStmts ro rw script

-- | The top level entry-point for AutoMatch
--   Requires a StmtInterpreter to be passed as input to resolve import cycle
autoMatch :: StmtInterpreter -> FilePath -> FilePath -> TopLevel ()
autoMatch interpreter leftFile rightFile =
   autoTagSourceFiles leftFile rightFile &
      (either (io . putStrLn) $ 
         uncurry autoMatchFiles >=> io . interactIO >=> actAfterMatch interpreter)

#if !MIN_VERSION_base(4,8,0)
   where (&) = flip ($)
#endif

-- | Just a bunch of SAWScript statments as output and a supply of unique identifiers
type ScriptWriter = WriterT [SAWScript.Stmt] (Supply String)

-- | Given two tagged source files and a bunch of matchings of declarations,
--   generate an interaction which asks the user what to do after the matching
--   and gives the appropriate MatchResult. Contains the logic for generating 
--   SAWScript based upon the assignments.
processResults :: TaggedSourceFile -> TaggedSourceFile
               -> [(Decl, Decl, Assignments)]
               -> Interaction MatchResult
processResults (TaggedSourceFile leftLang  leftFile) (TaggedSourceFile rightLang rightFile) matchings = do

      MatchResult script <$> (do separator ThickSep
                                 ifM (confirm "Save generated script to file?")
                                     (Just <$> getString "Filename:")
                                     (return Nothing))
                         <*> (do separator ThinSep
                                 confirm "Print generated script to the console?")
                         <*> (do separator ThinSep
                                 confirm "Execute generated script?")

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
         theoremName <- newNameWith prefix
         (leftArgs, rightArgs) <-
            fmap (both (map snd . sortBy (comparing fst)) . unzip) .
            forM assigns $
               \((Arg leftName _, leftIndex), (Arg rightName _, rightIndex)) -> do
                  name <- newNameWith (nameCenter (leftName ++ "_" ++ rightName))
                  return ((leftIndex, name), (rightIndex, name))
         returning theoremName . tell $
            [SAWScript.StmtBind (Just theoremName) Nothing Nothing .
                SAWScript.Code . locate .
                   show . Cryptol.ppPrec 0 .
                      cryptolAbstractNamesSAW leftArgs .
                         cryptolApplyFunction (Cryptol.EParens . Cryptol.EVar . nameCryptolFromSAW . locate $ "==") $
                            [ cryptolApplyFunctionSAW leftFunction  leftArgs
                            , cryptolApplyFunctionSAW rightFunction rightArgs ]]

      nameCryptolFromSAW :: SAWScript.LName -> Cryptol.QName
      nameCryptolFromSAW = Cryptol.mkUnqual . Cryptol.mkName . SAWScript.getVal

      cryptolAbstractNamesSAW :: [SAWScript.LName] -> Cryptol.Expr -> Cryptol.Expr
      cryptolAbstractNamesSAW names expr =
         Cryptol.EFun (for names $ Cryptol.PVar . cryptolLocate . SAWScript.getVal) expr

      cryptolApplyFunctionSAW :: SAWScript.LName -> [SAWScript.LName] -> Cryptol.Expr
      cryptolApplyFunctionSAW function args =
         cryptolApplyFunction (Cryptol.EVar $ nameCryptolFromSAW function)
                              (map (Cryptol.EVar . nameCryptolFromSAW) args)

      cryptolApplyFunction :: Cryptol.Expr -> [Cryptol.Expr] -> Cryptol.Expr
      cryptolApplyFunction function args =
         foldl Cryptol.EApp function args

      prove :: SAWScript.LName -> ScriptWriter ()
      prove theorem = tell $
         [SAWScript.StmtBind Nothing Nothing Nothing
             (SAWScript.Application
                (SAWScript.Application
                   (SAWScript.Var . locate $ "prove_print")
                   (SAWScript.Var (locate "abc")))
                (SAWScript.Var theorem))]

      printString :: String -> ScriptWriter ()
      printString string = tell $
         [SAWScript.StmtBind Nothing Nothing Nothing
             (SAWScript.Application
                (SAWScript.Var . locate $ "print")
                (SAWScript.String string))]

      locate :: String -> SAWScript.LName
      locate name =
         SAWScript.Located name "" (PosInternal "generated by auto_match")

      cryptolLocate :: String -> Cryptol.LName
      cryptolLocate name =
         Cryptol.Located
            (Cryptol.Range
               (Cryptol.Position 0 0)
               (Cryptol.Position 0 0)
               (error "bogus position generated by auto_match"))
            (Cryptol.mkName name)

      newNameWith :: (String -> String) -> ScriptWriter (SAWScript.LName)
      newNameWith prefix = locate . prefix <$> supply

      -- Here's the template for the output script:
      script :: [SAWScript.Stmt]
      script = flip evalSupply (map show [(0 :: Integer) ..]) . execWriterT $ do
         leftModule  <- loadFile (nameLeft  "module") leftLang  leftFile
         rightModule <- loadFile (nameRight "module") rightLang rightFile
         forM_ matchings $ \(leftDecl, rightDecl, assigns) -> do
            leftFunction  <- extractFunction (nameLeft  (declName leftDecl))  leftLang  (declName leftDecl)  leftModule
            rightFunction <- extractFunction (nameRight (declName rightDecl)) rightLang (declName rightDecl) rightModule
            theorem       <- equivalenceTheorem (nameCenter "theorem") leftFunction rightFunction assigns
            printString $ "Proving '" ++ declName leftDecl  ++ "' (" ++ leftFile  ++ ")" ++
                              " == '" ++ declName rightDecl ++ "' (" ++ rightFile ++ ")"
            prove theorem
