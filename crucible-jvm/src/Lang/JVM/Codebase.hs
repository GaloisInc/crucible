{- |
Module           : Lang.JVM.Codebase
Description      : Codebase manipulation, copied from jvm-verifier package
License          : BSD3
Stability        : stable
Point-of-contact : jhendrix
-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DoAndIfThenElse #-}
module Lang.JVM.Codebase
  ( Codebase
  , getClasses
  , isStrictSuper
  , isSubtype
  , loadCodebase
  , locateField
  , tryLookupClass
  , lookupClass
  , findStaticMethodsByRef
  , findVirtualMethodsByRef
  , supers
  , module Language.JVM.Parser
  ) where

import Control.Monad
import qualified Data.Map as M
import Data.IORef
import Data.List (isPrefixOf)
import Data.Maybe
import System.Directory (doesFileExist)
import System.FilePath (pathSeparator, (<.>), (</>))

import Language.JVM.Common
import Language.JVM.JarReader
import Language.JVM.Parser

-- | Collection of classes loaded by JVM.
data CodebaseState = CodebaseState {
    jarReader   :: JarReader
  -- ^ Maps class names to lazily loaded classes in JARs
  , classPaths :: [FilePath]
  , classMap    :: M.Map ClassName Class
  , subclassMap :: M.Map ClassName [Class]
  -- ^ Maps class names to the list of classes that are direct subclasses, and
  -- interfaces to list of classes that directly implement them.
  }

newtype Codebase = Codebase (IORef CodebaseState)

instance Show Codebase where
  show _ = "Codebase XXXXXX"

-- | Loads Java classes directly beneath given path.  Also loads jar indices for
-- lazy class loading.
loadCodebase :: [FilePath] -> [FilePath] -> IO Codebase
loadCodebase jarFiles classPaths = do
  -- REVISIT: Currently, classes found in the classpath shadow those in the
  -- jars.  Pretty sure the -classpath argument to the vanilla jvm allows
  -- mixture of jars and directories, and resolves names in the order in which
  -- those elements are encountered.  We probably want to do the same thing (and
  -- be able to just provide one argument to loadCodebase), but not for the
  -- beta. [js 04 Nov 2010]
  --
  -- UPDATE: docs on class resolution:
  -- http://docs.oracle.com/javase/8/docs/technotes/tools/findingclasses.html.
  -- I don't see any mention of resolution order in case of name
  -- conflicts. This Stack Overflow answer claims it's complicated in
  -- general, but that it will be the first encountered, searching
  -- left to right in the class path:
  -- http://stackoverflow.com/a/9757708/470844.
  --
  -- If we later want to make the resolution order be the
  -- left-to-right-in-classpath order, then we can e.g. implement a
  -- 'ClassPathLoader' which includes sequence of 'JarLoader' and
  -- 'DirLoader' objects, which embed maps from class names to 'Class'
  -- objects. A
  --
  --   getClass :: String -> IO (Maybe Class)
  --
  -- interface would be sufficient. If we want to avoid repeating the
  -- lookup in many maps -- one for each classpath component -- we can
  -- merge the maps as in the current 'JarReader' type, but I doubt
  -- this would ever matter, performance wise.
  jars       <- newJarReader jarFiles
  let cb = CodebaseState jars classPaths M.empty M.empty
  Codebase <$> newIORef cb

-- | Register a class with the given codebase
addClass :: Class -> CodebaseState -> CodebaseState
addClass cl (CodebaseState jr cp cMap scMap) =
  CodebaseState jr cp
                (M.insert (className cl) cl cMap)
                (foldr addToSuperclass scMap
                   (maybeToList (superClass cl)++classInterfaces cl))
  where addToSuperclass super m =
          M.alter (\subclasses -> case subclasses of
                                    Just list -> Just (cl : list)
                                    Nothing -> Just [cl])
                  super
                  m

-- | Returns class with given name in codebase or returns nothing if no class with
-- that name can be found.
tryLookupClass :: Codebase -> ClassName -> IO (Maybe Class)
tryLookupClass (Codebase cbRef) clNm = do
  cb <- readIORef cbRef
  case M.lookup clNm (classMap cb) of
    Just cl -> return (Just cl)
    Nothing -> do
      -- Here we bias our search to JARs before classpath directories,
      -- as mentioned above in 'loadCodebase'.
      let mcls = [loadClassFromJar clNm (jarReader cb)] ++
                 map (loadClassFromDir clNm) (classPaths cb)
      mcl <- foldl1 firstSuccess mcls
      case mcl of
        Just cl -> do
          writeIORef cbRef $! addClass cl cb
          return $ Just cl
        Nothing -> return Nothing
  where
    -- | Combine two @IO (Maybe a)@ computations lazily, choosing the
    -- first to succeed (i.e. return 'Just').
    firstSuccess :: IO (Maybe a) -> IO (Maybe a) -> IO (Maybe a)
    -- This seems like it would be a common pattern, although I can't
    -- find it in the standard libraries.
    firstSuccess ima1 ima2 = do
      ma1 <- ima1
      case ma1 of
        Nothing -> ima2
        Just _ -> return ma1

-- | Attempt to load a class by searching under directory @dir@, which
-- is assumed to be a classpath component. If class @C1. ... .Cn@ is
-- available under @dir@, then it must be located at
-- @dir/C1/.../Cn.class@.
-- http://docs.oracle.com/javase/8/docs/technotes/tools/findingclasses.html#userclass
loadClassFromDir :: ClassName -> FilePath -> IO (Maybe Class)
loadClassFromDir clNm dir = do
  exists <- doesFileExist file
  if exists
  then Just <$> loadClass file
  else return Nothing
  where
    file = dir </> classNameToClassFilePath clNm
    -- | Turn a @com/example/Class@-style classname into a
    --  @"com" </> "example" </> "Class.class"@-style platform dependent
    --  relative class-file path.
    --
    -- TODO: move this to 'jvm-parser.git:Language.JVM.Common'?
    classNameToClassFilePath :: ClassName -> FilePath
    classNameToClassFilePath clNm =
      map (\c -> if c == '/' then pathSeparator else c) (unClassName clNm) <.> "class"

-- | Returns class with given name in codebase or raises error if no class with
-- that name can be found.
--
-- The components of class name @clNm@ should be slash separated, not
-- dot separated. E.g. the class @com.example.Class@ should be
-- @com/example/class@.
lookupClass :: Codebase -> ClassName -> IO Class
lookupClass cb clNm = do
  maybeCl <- tryLookupClass cb clNm
  case maybeCl of
    Just cl -> return cl
    Nothing -> error $ errorMsg
  where
    dotNm = slashesToDots (unClassName clNm)
    isStandardLibClass = "java.lang" `isPrefixOf` dotNm
    errorMsg = unlines $
      if isStandardLibClass then
        [ "Cannot find class " ++ dotNm ++ " in codebase."
        , ""
        , "You probably forgot to specify the location of the"
        , "Java standard libraries JAR using the '-j' flag to saw or jss. The"
        , " standard libraries JAR is called 'classes.jar' on OS X systems and"
        , "'rt.jar' on Windows and Linux systems. Its location can be found by"
        , "running 'java -verbose 2>&1 | grep Opened', assuming you're using"
        , "a Sun Java."
        ]
      else
        [ "Cannot find class " ++ dotNm ++ " in codebase."
        , ""
        , "You can specify the location of classes you depend on using"
        , "the '-c' flag to specify non-jar classpaths and the '-j' flag"
        , "to specify the location of JAR files."
        ]

getClasses :: Codebase -> IO [Class]
getClasses (Codebase cbRef) = do
  cb <- readIORef cbRef
  return . M.elems . classMap $ cb

-- | Adjusts the given field id to specify as its class the class in the
-- superclass hierarchy that declares it
locateField :: Codebase -> FieldId -> IO FieldId
locateField cb fldId = do
  owner <- findFieldOwner fldId
  return $ fldId { fieldIdClass = className owner}
  where
    -- Walk an inheritance hierarchy to determine the the class that declares a
    -- given field (i.e., the "field owner")
    findFieldOwner :: FieldId -> IO Class
    findFieldOwner FieldId{fieldIdName = fldNm, fieldIdClass = clNm } = do
      sups <- supers cb =<< lookupClass cb clNm
      case filter hasField sups of
        -- In theory, this should be unreachable.
        [] -> error $ "Unable to find field '" ++ fldNm
                    ++ "' in superclass hierarchy of class " ++ unClassName clNm
        (cl' : _) -> return cl'
      where
        hasField cl = fldNm `elem` map fieldName accessibleFields
          where accessibleFields
                  | className cl == clNm = classFields cl
                  | otherwise =
                      filter ((/=) Private . fieldVisibility) (classFields cl)

-- | (isStrictSuper cb name class) returns true if name is a (strict) superclass
-- of class in cb.
isStrictSuper :: Codebase -> ClassName -> Class -> IO Bool
isStrictSuper cb name cl = do
  case superClass cl of
    Just super
      | name == super -> return True
      | otherwise -> isStrictSuper cb name =<< lookupClass cb super
    Nothing -> return False

-- | Returns true if subclass is a subtype of superclass in codebase.
isSubtype :: Codebase -> Type -> Type -> IO Bool
isSubtype _ sub super | sub == super           = return True
isSubtype cb (ArrayType sub) (ArrayType super)  = isSubtype cb sub super
isSubtype _ (ArrayType _sub) (ClassType super) =
  return $ super == "java/lang/Object"
           || super == "java/lang/Cloneable"
           || super == "java/io/Serializable"
isSubtype cb (ClassType subName) super@(ClassType _) = do
 subclass <- lookupClass cb subName
 -- Check if sub is a subclass of super
 b <- case (superClass subclass) of
        Just superName -> isSubtype cb (ClassType superName) super
        Nothing        -> return False
 -- Check if super is an interface that sub implements
 b' <- or <$> mapM (\i -> isSubtype cb (ClassType i) super)
                   (classInterfaces subclass)
 return $ b || b'
isSubtype _ _sub _super = return False

-- | Finds all classes that implement a given method. List is ordered so that
-- subclasses appear before their base class.
findVirtualMethodsByRef :: Codebase
                        -> ClassName -- ^ Name of class given in code for this class.
                        -> MethodKey -- ^ Method to identify.
                        -> ClassName -- ^ Concrete class for this object.
                        -> IO [ClassName]
findVirtualMethodsByRef cb name key instTyNm = do
  cl <- lookupClass cb name
  sups    <- drop 1 <$> supers cb cl
  revSubs <- reverse <$> cb `subs` cl
  map className <$> filterM isMatch (revSubs ++ sups)
 where
    isMatch cl = case cl `lookupMethod` key of
      Nothing -> return False
      Just _  -> do
        b   <- isStrictSuper cb (className cl) =<< lookupClass cb instTyNm
        return $ className cl == instTyNm || b

-- | Finds all classes that implement a given static method. List is
-- ordered so that subclasses appear before their base class.
findStaticMethodsByRef :: Codebase
                       -> ClassName
                       -- ^ Name of class given in the code for this call
                       -> MethodKey
                       -- ^ Method to call
                       -> IO [ClassName]
findStaticMethodsByRef cb name key = do
  cl <- lookupClass cb name
  sups <- supers cb cl
  let isMatch clName = isJust (clName `lookupMethod` key)
  return . map className . filter isMatch $ sups

-- | Produces the superclass hierarchy of the given class. Ordered from subclass
-- to base class, starting with the given class.
supers :: Codebase -> Class -> IO [Class]
supers cb cl = do
  starClosureM (maybe (return []) (fmap (:[]) . lookupClass cb) . superClass) cl

-- | Produces the subclass hierarchy of the given class.  Ordered
-- from base class to subclass, starting with the given class.
subs :: Codebase -> Class -> IO [Class]
subs (Codebase ref) cl = do
  cb <- readIORef ref
  return $ starClosure (fromMaybe [] . (`M.lookup` subclassMap cb) . className) cl


--------------------------------------------------------------------------------
-- Misc

-- (starClosure f a) returns the list of values obtainable by 0 or more
-- applications of f.
starClosure :: (a -> [a]) -> a -> [a]
starClosure fn a = a : concatMap (starClosure fn) (fn a)

-- The monadic variant of starClosure
starClosureM :: Monad m => (a -> m [a]) -> a -> m [a]
starClosureM fn a =
  return ((a:) . concat) `ap` (mapM (starClosureM fn) =<< fn a)
