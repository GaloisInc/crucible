{- |
Module           : Lang.JVM.Codebase
Description      : Java Codebase manipulation
License          : BSD3
Stability        : stable
Point-of-contact : jhendrix
-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
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
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe (MaybeT(..))
import Crypto.Hash.SHA1 (hash)
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as B
import Data.Foldable (Foldable(..))
import qualified Data.Map as M
import Data.IORef
import Data.List (isPrefixOf)
import Data.Maybe
import System.Directory
import System.FilePath (pathSeparator, takeDirectory, (<.>), (</>))

import Lang.JVM.JavaTools
import Lang.JVM.ProcessUtils

import Language.JVM.Common
import Language.JVM.JarReader
import Language.JVM.Parser

{- Note [Loading classes from JIMAGE files]

The Java standard library is packaged differently depending on which version of
the JDK is being used:

* JDK 8 and earlier ship the standard library in <java.home>/lib/rt.jar, so
  loading the standard library's .class files is simply a matter of parsing
  rt.jar. The `jvm-parser` library is used to parse rt.jar like any other JAR
  file.
* JDK 9 and later abandon rt.jar and instead distribute the standard library as
  a JIMAGE file. (For more on the JIMAGE file format and how it compares to
  JAR, see https://stackoverflow.com/a/64202720.) In particular, the standard
  library is now located in a JIMAGE file at <java.home>/lib/modules.

We need access to the standard library's .class files in order to verify even
the simplest Java programs, so figuring out how to load classes from JIMAGE
files is a requirement for using JDK 9 or later with crucible-jvm. Unlike JAR,
however, the JIMAGE file format is internal to the JDK and subject to change in
the future. As a result, parsing JIMAGE files directly, like `jvm-parser` does
with JAR files, is likely not a good idea.

If parsing JIMAGE files directly isn't a viable option, what can be done? As
far as I can tell, there are only two reasonable ways of extracting .class
files from JIMAGE files (outside of using Java itself):

* Use libjimage, a C++ library bundled with the JDK, to load classes. This is
  what the JDK itself uses internally, and as a result, it's reasonably space-
  and time-efficient to load a single class from a JIMAGE file. Unfortunately,
  this is a non-starter for crucible-jvm due to potential linking issues that
  would arise when combining GHC with C++ code.
  See https://github.com/GaloisInc/crucible/issues/621.

* Use the jimage utility, shipped alongside java in <java.home>/bin, to extract
  the contents of JIMAGE files. The `jimage extract` command can either be used
  to extract everything in a JIMAGE file all at once, or it can be used to
  extract one class at a time, like in this example:

    jimage extract --include regex:.*/java/lang/Class.class --dir <output-dir> <jimage-file>

Since libjimage is an option, that only leaves jimage. Unfortunately, jimage is
not without its flaws:

* jimage is /slow/. It takes about about 1.5 seconds for jimage to extract the
  standard `modules` file on a reasonably performant machine. Having an extra
  1.5 seconds of lag every time that crucible-jvm is invoked doesn't sound
  appealing.

* What's worse, jimage is still unreasonably slow even if you only use it to
  extract a single class from a JIMAGE file. It takes about 0.25 seconds to
  extract java/lang/Class.class from the standard `modules`, which leads me to
  suspect that jimage is doing a linear scan through every file in `modules`.
  In any case, this is about 14× slower than loading a class file from a JAR,
  and if crucible-jvm spends 0.25 seconds every time it loads any class from
  `modules`, this would add up very quickly.

What can we do about jimage's performance issues? One appealing alternative is
to use jlink, yet another utility that the JDK ships. If you give jlink a list
of Java modules, it will produce a minimal runtime environment that includes a
JIMAGE file that only contains the classes needed to support those modules, but
nothing else. In theory, this could cut down on the time it takes to extract
classes from a JIMAGE file, as the standard library's `modules` file is ~136 MB
when compressed (~493 MB when uncompressed), and most Java classes will only
use a small portion of that.

Unfortunately, jlink is even slower than jimage. It takes jlink about 3 seconds
to create a runtime environment that only contains the `java.base` module,
which cancels out any time saved when extracting the JIMAGE file afterwards.

Having exhausted all other possibilities, we have concluded that we simply
can't make JIMAGE extraction fast in the general case. We /can/, however,
amortize the cost of using JIMAGE files by caching the extracted contents.
This is exactly what crucible-jvm does. Any time that crucible-jvm tries to
load a class (e.g., java/lang/Class.class), it first checks to see if it is in
a known cache directory
(e.g., ~/.cache/crucible-jvm/<hashed-path-to-modules-file>/java.base/java/lang/Class.class),
and if so, loads it like it would any other .class on the classpath. If not,
it will then consult the JAR path and the classpath. If it is not located by
that point, then crucible-jvm will attempt to extract it from the JIMAGE file,
caching the result for subsequent lookups. Importantly, we perform the JIMAGE
extraction step last, as it is far more time-consuming that trying to load
classes from the JAR path or classpath.

There's still possibly some room for further optimization here. As mentioned
above, extracting one class at a time from a JIMAGE file takes about 0.25
seconds, while extracting the entire JIMAGE file takes about 1.5 seconds.
Depending on how many classes a program uses, it may take less time overall
to just extract-and-cache everything from a JIMAGE file at once. The downside,
however, is that the cache would require much more space. A typical JDK
`modules` file takes up ~493 MB of classes when extracted, but most simple Java
programs will only use <1 MB of these classes. As a result, we opt for the
one-class-at-a-time approach, which seems better tuned for the sorts of
Java programs that crucible-jvm verifies in common cases.
-}

-- | Collection of classes loaded by JVM.
data CodebaseState = CodebaseState {
    classMap    :: M.Map ClassName Class
  , subclassMap :: M.Map ClassName [Class]
  -- ^ Maps class names to the list of classes that are direct subclasses, and
  -- interfaces to list of classes that directly implement them.
  }

-- | Contains the path to the @jimage@ tool, the standard @modules@ JIMAGE
-- file, and the path where the extracted contents of @modules@ are cached.
--
-- This is only used when crucible-jvm uses JDK 9 or later.
-- See Note [Loading classes from JIMAGE files].
data JimagePaths = JimagePaths
  { jimagePath               :: FilePath
  , standardModulesFilePath  :: FilePath
  , standardModulesCachePath :: FilePath
  }

data Codebase = Codebase
  { jarReader  :: JarReader
  -- ^ Maps class names to lazily loaded classes in JARs
  , classPaths :: [FilePath]
  , jimagePaths :: Maybe JimagePaths
  -- ^ The path to the @jimage@ tool and the paths it works on.
  , stateRef   :: IORef CodebaseState
  }

instance Show Codebase where
  show _ = "Codebase XXXXXX"

-- | Loads Java classes directly beneath given path.  Also loads jar indices for
-- lazy class loading.
loadCodebase :: [FilePath] -> [FilePath] -> [FilePath] -> IO Codebase
loadCodebase jarFiles classPaths javaBinDirs = do
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
  jars          <- newJarReader jarFiles
  mbJimagePaths <- findJimagePaths javaBinDirs
  let cb = CodebaseState { classMap = M.empty, subclassMap = M.empty }
  cbRef <- newIORef cb
  pure $ Codebase
    { jarReader   = jars
    , classPaths  = classPaths
    , jimagePaths = mbJimagePaths
    , stateRef    = cbRef
    }

-- | Register a class with the given codebase
addClass :: Class -> CodebaseState -> CodebaseState
addClass cl (CodebaseState cMap scMap) =
  CodebaseState (M.insert (className cl) cl cMap)
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
tryLookupClass (Codebase{jarReader, classPaths, jimagePaths, stateRef}) clNm = do
  cb <- readIORef stateRef
  case M.lookup clNm (classMap cb) of
    Just cl -> return (Just cl)
    Nothing -> do
      -- Here we bias our search to JARs before classpath directories,
      -- as mentioned above in 'loadCodebase'.
      let mcls = [ loadClassFromStandardModulesCache clNm jimagePaths
                 , loadClassFromJar clNm jarReader ] ++
                 map (loadClassFromDir clNm) classPaths ++
                 [ loadClassFromStandardModulesFile clNm jimagePaths ]
      mcl <- foldl1 firstSuccess mcls
      case mcl of
        Just cl -> do
          writeIORef stateRef $! addClass cl cb
          return $ Just cl
        Nothing -> return Nothing

-- Search for a .class file in the cache of files extracted from the `modules`
-- JIMAGE file. If it is not found, this does /not/ extract it from a JIMAGE
-- file—see loadClassFromStandardModulesFile.
loadClassFromStandardModulesCache :: ClassName -> Maybe JimagePaths -> IO (Maybe Class)
loadClassFromStandardModulesCache clNm mbJimagePaths =
  case mbJimagePaths of
    Nothing -> pure Nothing
    Just JimagePaths{standardModulesCachePath} ->
      loadClassFromParentDir clNm standardModulesCachePath

-- Attempt to extract a .class file from the `modules` JIMAGE file, cache it
-- for subsequent lookups, and load the resulting .class.
loadClassFromStandardModulesFile :: ClassName -> Maybe JimagePaths -> IO (Maybe Class)
loadClassFromStandardModulesFile clNm mbJimagePaths =
  case mbJimagePaths of
    Nothing -> pure Nothing
    Just JimagePaths{jimagePath, standardModulesFilePath, standardModulesCachePath} -> do
      _ <- readProcessExitIfFailure jimagePath
             [ "extract"
             , "--include", "regex:.*/" ++ escapeDollars (unClassName clNm) ++ ".class"
             , "--dir", standardModulesCachePath
             , standardModulesFilePath
             ]
      -- After extracting a single class from a JIMAGE file, why do we then
      -- have to search every directory under the cached path again? It's
      -- because `jimage extract` doesn't tell you the path of the thing it
      -- just extracted. Sigh. We can't reasonably infer what this path is
      -- either, as it will start with a module name, which isn't something
      -- that is contained in a ClassName.
      loadClassFromParentDir clNm standardModulesCachePath
  where
    -- The '$' character needs to be escaped in the regex that
    -- `jimage extract` uses.
    escapeDollars :: String -> String
    escapeDollars []       = []
    escapeDollars ('$':cs) = '\\':'$':escapeDollars cs
    escapeDollars (c:cs)   = c:escapeDollars cs

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

-- Given @parentDir@, search through its subdirectories to find a class,
-- loading it if it is found.
loadClassFromParentDir :: ClassName -> FilePath -> IO (Maybe Class)
loadClassFromParentDir clNm parentDir = do
  childDirBaseNames <- listDirectory parentDir
  let childDirs = map (parentDir </>) childDirBaseNames
  foldl' firstSuccess (pure Nothing) $ map (loadClassFromDir clNm) childDirs

-- | Attempt to find an executable named @jimage@, either in the directories
-- supplied as arguments or on the @PATH@. If such an executable can be found,
-- then @Just@ a @JimagePaths@ is returned. Otherwise, @Nothing@ is returned.
--
-- This is only used when crucible-jvm uses JDK 9 or later.
-- See Note [Loading classes from JIMAGE files].
findJimagePaths :: [FilePath] -> IO (Maybe JimagePaths)
findJimagePaths javaBinDirs = runMaybeT $ do
  javaPath <- MaybeT $ findJavaIn javaBinDirs
  javaPathCanonical <- liftIO $ canonicalizePath javaPath -- Remove any symlinks
  jimagePath <- MaybeT $ findJimageIn [takeDirectory javaPathCanonical]
  javaHome <- MaybeT $ findJavaProperty javaPathCanonical "java.home"
  MaybeT $ do
    let standardModulesPath = javaHome </> "lib" </> "modules"
    xdgCacheDir <- getXdgDirectory XdgCache "crucible-jvm"
    let standardModulesHash = B16.encode $ hash $ B.pack standardModulesPath
        standardModulesCache = xdgCacheDir </> B.unpack standardModulesHash
    createDirectoryIfMissing True standardModulesCache
    pure $ Just $ JimagePaths
      { jimagePath               = jimagePath
      , standardModulesFilePath  = standardModulesPath
      , standardModulesCachePath = standardModulesCache
      }

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
getClasses (Codebase{stateRef}) = do
  cb <- readIORef stateRef
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
subs (Codebase{stateRef}) cl = do
  cb <- readIORef stateRef
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
