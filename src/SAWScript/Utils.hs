{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : jhendrix, lerkok
-}

{-# LANGUAGE DeriveDataTypeable  #-}
module SAWScript.Utils where

import Control.Applicative
import Control.Exception as CE
import Control.Monad.State
import Control.DeepSeq(rnf, NFData(..))
import Data.List(intercalate)
import Data.Char(isSpace)
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable (traverse)
import System.Directory(makeRelativeToCurrentDirectory)
import System.FilePath(makeRelative, isAbsolute, (</>), takeDirectory)
import System.Time(TimeDiff(..), getClockTime, diffClockTimes, normalizeTimeDiff, toCalendarTime, formatCalendarTime)
import System.Locale(defaultTimeLocale)
import Text.PrettyPrint.Leijen hiding ((</>), (<$>))
import Numeric(showFFloat)

import qualified Verifier.Java.Codebase as JSS

import Verifier.SAW.Conversion
import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

data SAWCtx
  deriving (Typeable)
data JSSCtx
  deriving (Typeable)
data LSSCtx
  deriving (Typeable)

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col
         | PosInternal String
         | PosREPL
  deriving (Eq)

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

fmtPoss :: [Pos] -> String -> String
fmtPoss [] m = fmtPos (PosInternal "saw-script internal") m
fmtPoss ps m = "[" ++ intercalate ",\n " (map show ps) ++ "]:\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

posRelativeToCurrentDirectory :: Pos -> IO Pos
posRelativeToCurrentDirectory (Pos f l c)     = makeRelativeToCurrentDirectory f >>= \f' -> return (Pos f' l c)
posRelativeToCurrentDirectory (PosInternal s) = return $ PosInternal s
posRelativeToCurrentDirectory PosREPL = return PosREPL

posRelativeTo :: FilePath -> Pos -> Pos
posRelativeTo d (Pos f l c)     = Pos (makeRelative d f) l c
posRelativeTo _ (PosInternal s) = PosInternal s
posRelativeTo _ PosREPL = PosREPL

routePathThroughPos :: Pos -> FilePath -> FilePath
routePathThroughPos (Pos f _ _) fp
  | isAbsolute fp = fp
  | True          = takeDirectory f </> fp
routePathThroughPos _ fp = fp

instance Show Pos where
  show (Pos f 0 0)     = show f ++ ":end-of-file"
  show (Pos f l c)     = show f ++ ":" ++ show l ++ ":" ++ show c
  show (PosInternal s) = "[internal:" ++ s ++ "]"
  show PosREPL = "REPL"

data SSMode = Verify | Blif | CBlif deriving (Eq, Show, Data, Typeable)

-- | Convert a string to a paragraph formatted document.
ftext :: String -> Doc
ftext msg = fillSep (map text $ words msg)

-- | Insert multiple keys that map to the same value in a map.
mapInsertKeys :: Ord k => [k] -> a -> Map k a -> Map k a
mapInsertKeys keys val m = foldr (\i -> Map.insert i val) m keys

-- | Returns the value bound to the first key in the map, or
-- Nothing if none of the keys are in the map.
mapLookupAny :: Ord k => [k] -> Map k a -> Maybe a
mapLookupAny keys m = listToMaybe $ catMaybes $ map (\k -> Map.lookup k m) keys

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

-- ExecException {{{1

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException Pos          -- ^ Position
                                   Doc          -- ^ Error message
                                   String       -- ^ Resolution tip
  deriving (Show, Typeable)

instance Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException pos errorMsg resolution = liftIO $ throwIO (ExecException pos errorMsg resolution)

-- | Throw exec exception in a MonadIO.
throwExecException :: Pos -> Doc -> String -> m a
throwExecException pos errorMsg resolution = throw (ExecException pos errorMsg resolution)

-- Timing {{{1

-- | Return a string representation of the elapsed time since start
timeIt :: (NFData a, MonadIO m) => m a -> m (a, String)
timeIt action = do
        start <- liftIO $ getClockTime
        r <- action
        end <- rnf r `seq` liftIO getClockTime
        let itd = diffClockTimes end start
            td = normalizeTimeDiff itd
            vals = dropWhile (\(v, _) -> v == 0) (zip [tdYear td, tdMonth td, tdDay td, tdHour td, tdMin td] "YMDhm")
            sec = ' ' : show (tdSec td) ++ dropWhile (/= '.') pico
            pico = showFFloat (Just 3) (((10**(-12))::Double) * fromIntegral (tdPicosec td)) "s"
        return $ (r, dropWhile isSpace $ concatMap (\(v, c) -> ' ':show v ++ [c]) vals ++ sec)

-- | get a readable time stamp
getTimeStamp :: MonadIO m => m String
getTimeStamp = do t <- liftIO (getClockTime >>= toCalendarTime)
                  return $ formatCalendarTime defaultTimeLocale "%l:%M:%S %p" t

-- Java lookup functions {{{1

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists. Class name should be in slash-separated form.
lookupClass :: JSS.Codebase -> Pos -> String -> IO JSS.Class
lookupClass cb pos nm = do
  maybeCl <- JSS.tryLookupClass cb nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ JSS.slashesToDots nm ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException pos msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: JSS.Codebase -> Pos -> String -> JSS.Class -> IO (JSS.Class, JSS.Method)
findMethod cb pos nm initClass = impl initClass
  where javaClassName = JSS.slashesToDots (JSS.className initClass)
        methodMatches m = JSS.methodName m == nm && not (JSS.methodIsAbstract m)
        impl cl =
          case filter methodMatches (JSS.classMethods cl) of
            [] -> do
              case JSS.superClass cl of
                Nothing ->
                  let msg = ftext $ "Could not find method " ++ nm
                              ++ " in class " ++ javaClassName ++ "."
                      res = "Please check that the class and method are correct."
                   in throwIOExecException pos msg res
                Just superName ->
                  impl =<< lookupClass cb pos superName
            [method] -> return (cl,method)
            _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                             ++ " is ambiguous.  SAWScript currently requires that "
                             ++ "method names are unique."
                     res = "Please rename the Java method so that it is unique."
                  in throwIOExecException pos (ftext msg) res

throwFieldNotFound :: Pos -> JSS.Type -> String -> IO a
throwFieldNotFound pos tp fieldName =
  let msg = "Values with type \'" ++ show tp ++ "\' do not contain field named "
              ++ fieldName ++ "."
   in throwIOExecException pos (ftext msg) ""

findField :: JSS.Codebase -> Pos -> JSS.Type -> String -> IO JSS.FieldId
findField _ pos tp@(JSS.ArrayType _) nm = throwFieldNotFound pos tp nm
findField cb pos tp@(JSS.ClassType clName) nm = impl =<< lookupClass cb pos clName
  where impl cl =
          case filter (\f -> JSS.fieldName f == nm) $ JSS.classFields cl of
            [] -> do
              case JSS.superClass cl of
                Nothing -> throwFieldNotFound pos tp nm
                Just superName -> impl =<< lookupClass cb pos superName
            [f] -> return $ JSS.FieldId (JSS.className cl) nm (JSS.fieldType f)
            _ -> error "internal: Found multiple fields with the same name."
findField _ pos _ _ =
  let msg = "Primitive types cannot be dereferenced."
   in throwIOExecException pos (ftext msg) ""

equal :: SharedContext s -> [SharedTerm s] -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
equal sc _ctx (STApp _ (Lambda x1 ty1 tm1)) (STApp _ (Lambda _ ty2 tm2)) =
  case (asBitvectorType ty1, asBitvectorType ty2) of
    (Just n1, Just n2) -> do
      unless (n1 == n2) $
        fail $ "Arguments have different sizes: " ++
               show n1 ++ " and " ++ show n2
      eqBody <- equal sc [ty1] tm1 tm2
      scLambda sc x1 ty1 eqBody
    (_, _) ->
        fail $ "Incompatible function arguments. Types are " ++
               show ty1 ++ " and " ++ show ty2
equal sc ctx tm1 tm2 = do
    ty1 <- scTypeOf' sc ctx tm1
    ty2 <- scTypeOf' sc ctx tm2
    ss <- basic_ss sc
    ty1' <- rewriteSharedTerm sc ss ty1
    ty2' <- rewriteSharedTerm sc ss ty2
    case (ty1', ty2') of
      (asBitvectorType -> Just n1, asBitvectorType -> Just n2) -> do
        unless (n1 == n2) $ fail "Bitvectors have different sizes."
        n1t <- scNat sc n1
        scBvEq sc n1t tm1 tm2
      (asVecType -> Just (l1 :*: ety1), asVecType -> Just (l2 :*: _ety2)) -> do
        unless (l1 == l2) $ fail "Arrays have different sizes."
        -- TODO: check that ety1 == ety2?
        getOp <- scApplyPreludeGet sc
        eqs <- forM [0..l1-1] $ \i -> do
                 it <- scNat sc i
                 lt <- scNat sc l1
                 ft <- scFinVal sc it lt
                 et1 <- getOp lt ety1 tm1 ft
                 et2 <- getOp lt ety1 tm2 ft
                 equal sc ctx et1 et2
        andOp <- scApplyPreludeAnd sc
        trueTm <- scBool sc True
        foldM andOp trueTm eqs
      (_, _) ->
        fail $ "Incompatible non-lambda terms. Types are " ++
               show ty1' ++ " and " ++ show ty2'

allEqual :: SharedContext s -> [(SharedTerm s, SharedTerm s)] -> IO (SharedTerm s)
allEqual sc [] = scApplyPreludeTrue sc
allEqual sc ((t, t'):ts) = do
  r <- allEqual sc ts
  eq <- equal sc [] t t'
  andFn <- scApplyPreludeAnd sc
  andFn eq r

scRemoveBitvector :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scRemoveBitvector sc tm = do 
  rules <- scDefRewriteRules sc def
  tm' <- rewriteSharedTerm sc (addRules rules emptySimpset) tm
  return tm'
    where Just def = findDef (scModule sc) (parseIdent "Prelude.bitvector")

scEq :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scEq sc x y = equal sc [] x y {- do
  xty <- scTypeOf sc x
  eqOp <- scApplyPreludeEq sc
  res <- eqOp xty x y
  return res -}

scImplies :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scImplies sc x y = do
  xNot <- scNot sc x
  orOp <- scApplyPreludeOr sc
  orOp xNot y

defRewrites :: SharedContext s -> Ident -> IO [RewriteRule (SharedTerm s)]
defRewrites sc ident =
      case findDef (scModule sc) ident of
        Nothing -> return []
        Just def -> scDefRewriteRules sc def

basic_ss :: SharedContext s -> IO (Simpset (SharedTerm s))
basic_ss sc = do
  rs1 <- concat <$> traverse (defRewrites sc) defs
  rs2 <- scEqsRewriteRules sc eqs
  return $ addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
  where
    eqs = map (mkIdent preludeName)
      ["get_single", "get_bvAnd", "get_bvOr", "get_bvXor", "get_bvNot",
       "not_not", "get_slice", "bvAddZeroL", "bvAddZeroR", "ite_eq"]
    defs = map (mkIdent preludeName)
      [ "not", "and", "or", "xor", "boolEq", "ite", "addNat", "mulNat"
      , "compareNat", "finSucc", "finFront", "equalNat", "mkFinVal"
      , "bitvector"
      ]
    procs = bvConversions ++ natConversions ++ finConversions ++ vecConversions
