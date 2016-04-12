{- |
Module           : $Header$
Description      : Provides typechecked representation for method specifications and function for creating it from AST representation.
License          : BSD3
Stability        : provisional
Point-of-contact : jhendrix, atomb
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWScript.JavaMethodSpecIR
  (-- * MethodSpec record
    JavaMethodSpecIR
  , specName
  , specPos
  , specCodebase
  , specThisClass
  , specMethod
  , specMethodClass
  , specInitializedClasses
  , specBehaviors
  , specAddBehaviorCommand
  , specAddVarDecl
  , specAddLogicAssignment
  , specAddAliasSet
  , specAddAssumption
  , specActualTypeMap
  , specAllowAlloc
  , specSetAllowAllocation
  , specAssumptions
  , initMethodSpec
  --, resolveMethodSpecIR
    -- * Method behavior.
  , BehaviorSpec
  , bsLoc
  , bsRefExprs
  , bsMayAliasSet
  , RefEquivConfiguration
  , bsRefEquivClasses
  , bsActualTypeMap
  , bsLogicAssignments
  , bsAssumptions
  , bsLogicClasses
  , bsCheckAliasTypes
  , BehaviorCommand(..)
  , bsCommands
    -- * Equivalence classes for references.
  , JavaExprEquivClass
  , ppJavaExprEquivClass
  , ppMethodSpec
  ) where

-- Imports {{{1

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad
import Data.Graph.Inductive (scc, Gr, mkGraph)
import Data.List (intercalate, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Common as JSS

import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.CongruenceClosure (CCSet)
import SAWScript.JavaExpr
import SAWScript.Utils

-- ExprActualTypeMap {{{1

-- | Maps Java expressions for references to actual type.
type ExprActualTypeMap = Map JavaExpr JavaActualType

-- Alias definitions {{{1

type JavaExprEquivClass = [JavaExpr]

-- | Returns a name for the equivalence class.
ppJavaExprEquivClass :: JavaExprEquivClass -> String
ppJavaExprEquivClass [] = error "internal: ppJavaExprEquivClass"
ppJavaExprEquivClass [expr] = ppJavaExpr expr
ppJavaExprEquivClass cl = "{ " ++ intercalate ", " (map ppJavaExpr (sort cl)) ++ " }"

-- BehaviorSpec {{{1

-- | Postconditions used for implementing behavior specification. All
-- LogicExprs in behavior commands need to be extracted with
-- useLogicExpr, in a specific shared context, before they can be
-- used.
data BehaviorCommand
     -- | Assign Java expression the value given by the mixed expression.
   = EnsureInstanceField Pos JavaExpr JSS.FieldId MixedExpr
     -- | Assign static Java field the value given by the mixed expression.
   | EnsureStaticField Pos JSS.FieldId MixedExpr
     -- | Assign array value of Java expression the value given by the rhs.
   | EnsureArray Pos JavaExpr MixedExpr
     -- | Modify the Java expression to an arbitrary value.
     -- May point to integral type or array.
   | ModifyInstanceField JavaExpr JSS.FieldId
     -- | Modify the Java static field to an arbitrary value.
   | ModifyStaticField JSS.FieldId
     -- | Modify the Java array to an arbitrary value.
     -- May point to integral type or array.
   | ModifyArray JavaExpr JavaActualType
     -- | Specifies value method returns.
   | ReturnValue MixedExpr
  deriving (Show)

data BehaviorSpec = BS {
         -- | Program counter for spec.
         bsLoc :: JSS.Breakpoint
         -- | Maps all expressions seen along path to actual type.
       , bsActualTypeMap :: ExprActualTypeMap
         -- | Stores which Java expressions must alias each other.
       , bsMustAliasSet :: CCSet JavaExprF
         -- | May alias relation between Java expressions.
       , bsMayAliasClasses :: [[JavaExpr]]
         -- | Equations
       , bsLogicAssignments :: [(Pos, JavaExpr, MixedExpr)]
         -- | Conditions assumed by this specification.
       , bsAssumptions :: [LogicExpr]
         -- | Commands to execute in reverse order.
       , bsReversedCommands :: [BehaviorCommand]
       } deriving (Show)

ppLogicExpr :: LogicExpr -> Doc
ppLogicExpr (LogicExpr t args) =
  vcat $
  parens (scPrettyTermDoc defaultPPOpts t) :
  map (text . ppJavaExpr) args

ppMixedExpr :: MixedExpr -> Doc
ppMixedExpr (JE je) = text (ppJavaExpr je)
ppMixedExpr (LE le) = ppLogicExpr le

ppBehaviorCommand :: BehaviorCommand -> Doc
ppBehaviorCommand cmd =
  case cmd of
    (EnsureInstanceField _ je f me) ->
      "sets instance field" <+>
      text (ppJavaExpr je) <> "." <> ppField f <+>
      "to" <+> ppMixedExpr me
    (EnsureStaticField _ f me) ->
      "sets static field" <+>
      ppStaticField f <+>
      "to" <+> ppMixedExpr me
    (EnsureArray _ je me) ->
      "sets array" <+> text(ppJavaExpr je) <+>
      "to" <+> ppMixedExpr me
    (ModifyInstanceField je f) ->
      "modifies instance field" <+>
      text (ppJavaExpr je) <> "." <> ppField f
    (ModifyStaticField f) ->
      "modifies static field" <+>
      ppStaticField f
    (ModifyArray je _) ->
      "modifies array" <+> text (ppJavaExpr je)
    (ReturnValue me) ->
      "returns" <+> ppMixedExpr me
  where
    ppField f = text (JSS.fieldIdName f)
    ppStaticField f =
      text (JSS.fieldIdClass f) <> "." <> text (JSS.fieldIdName f)

ppBehavior :: BehaviorSpec -> Doc
ppBehavior bs =
  vcat [ "Assumes the following types for Java locations:"
       , indent 2 $ vcat $ map ppActualTypeEntry $
         Map.toList (bsActualTypeMap bs)
       , ""
       , "Assumes the following sets of references must alias:"
       , indent 2 $ vcat $ map ppSet $ CC.toList $ bsMustAliasSet bs
       , ""
       , "Assumes the following sets of references may alias:"
       , indent 2 $ vcat $ map ppSet $ bsMayAliasClasses bs
       , ""
       , "Assumes the following set of assignments:"
       , indent 2 $ vcat $ map ppAssign $ bsLogicAssignments bs
       , ""
       , "Assumes the following preconditions:"
       , indent 2 $ vcat $ map ppLogicExpr $ bsAssumptions bs
       , ""
       , "Ensures the following postconditions:"
       , indent 2 $ vcat $ map ppBehaviorCommand $ bsCommands bs
       , ""
       ]
  where
    ppActualTypeEntry (e, t) =
      text (ppJavaExpr e) <+> "::" <+> text (ppActualType t)
    ppSet =
      hcat . map (text . ppJavaExpr)
    ppAssign (_, je, me) =
      text (ppJavaExpr je) <+> ":=" <+> ppMixedExpr me

ppMethodSpec :: JavaMethodSpecIR -> Doc
ppMethodSpec ms =
  vcat [ "Java Method specification."
       , ""
       , "Instance class:" <+> text (JSS.className (specThisClass ms))
       , "Definition class:" <+> text (JSS.className (specMethodClass ms))
       , "Method:" <+> text (JSS.methodName (specMethod ms))
       , ""
       , "Requires these classes to be initialized:"
       , indent 2 $ vcat $ map text $ specInitializedClasses ms
       , ""
       , if specAllowAlloc ms
         then "Allows allocation."
         else "Does not allow allocation."
       , ""
       , ppBehavior $ specBehaviors ms
       ]

-- | Returns list of all Java expressions that are references.
bsExprs :: BehaviorSpec -> [JavaExpr]
bsExprs bs = Map.keys (bsActualTypeMap bs)

-- | Returns list of all Java expressions that are references.
bsRefExprs :: BehaviorSpec -> [JavaExpr]
bsRefExprs bs = filter isRefJavaExpr (bsExprs bs)

bsMayAliasSet :: BehaviorSpec -> CCSet JavaExprF
bsMayAliasSet bs =
  CC.foldr CC.insertEquivalenceClass
           (bsMustAliasSet bs)
           (bsMayAliasClasses bs)

-- | Check that all expressions that may alias have equal types.
bsCheckAliasTypes :: Pos -> BehaviorSpec -> IO ()
bsCheckAliasTypes pos bs = mapM_ checkClass (CC.toList (bsMayAliasSet bs))
  where atm = bsActualTypeMap bs
        checkClass [] = error "internal: Equivalence class empty"
        checkClass (x:l) = do
          let Just xType = Map.lookup x atm
          forM l $ \y -> do
            let Just yType = Map.lookup x atm
            when (xType /= yType) $ do
              let msg = "Different types are assigned to " ++ show x ++ " and " ++ show y ++ "."
                  res = "All references that may alias must be assigned the same type."
              throwIOExecException pos (ftext msg) res

type RefEquivConfiguration = [(JavaExprEquivClass, JavaActualType)]

-- | Returns all possible potential equivalence classes for spec.
bsRefEquivClasses :: BehaviorSpec -> [RefEquivConfiguration]
bsRefEquivClasses bs =
  map (map parseSet . CC.toList) $ Set.toList $
    CC.mayAliases (bsMayAliasClasses bs) (bsMustAliasSet bs)
 where parseSet l@(e:_) =
         case Map.lookup e (bsActualTypeMap bs) of
           Just tp -> (l,tp)
           Nothing -> error $ "internal: bsRefEquivClass given bad expression: " ++ show e
       parseSet [] = error "internal: bsRefEquivClasses given empty list."

bsPrimitiveExprs :: BehaviorSpec -> [JavaExpr]
bsPrimitiveExprs bs =
  [ e | (e, PrimitiveType _) <- Map.toList (bsActualTypeMap bs) ]

bsLogicEqs :: BehaviorSpec -> [(JavaExpr, JavaExpr)]
bsLogicEqs bs =
  [ (lhs, rhs) | (_, lhs, JE rhs) <- bsLogicAssignments bs ]

-- | Returns logic assignments to equivance class.
bsAssignmentsForClass ::  BehaviorSpec -> JavaExprEquivClass
                      -> [LogicExpr]
bsAssignmentsForClass bs cl = res
  where s = Set.fromList cl
        res = [ rhs
              | (_, lhs, LE rhs) <- bsLogicAssignments bs
              , Set.member lhs s
              ]

-- | Retuns ordering of Java expressions to corresponding logic value.
bsLogicClasses :: BehaviorSpec
               -> RefEquivConfiguration
               -> IO (Maybe [(JavaExprEquivClass, JavaActualType, [LogicExpr])])
bsLogicClasses bs cfg = do
  let allClasses = CC.toList
                   -- Add logic equations.
                   $ flip (foldr (uncurry CC.insertEquation)) (bsLogicEqs bs)
                   -- Add primitive expression.
                   $ flip (foldr CC.insertTerm) (bsPrimitiveExprs bs)
                   -- Create initial set with references.
                   $ CC.fromList (map fst cfg)
  logicClasses <- (catMaybes <$>) $
                  forM allClasses $ \(cl@(e:_)) ->
                    case Map.lookup e (bsActualTypeMap bs) of
                      Just (ClassInstance _) -> return Nothing
                      Just at -> return (Just (cl, at))
                      Nothing -> return Nothing
  let v = V.fromList logicClasses
      -- Create nodes.
      grNodes = [0..] `zip` logicClasses
      -- Create edges
      exprNodeMap = Map.fromList [ (e,n) | (n,(cl,_)) <- grNodes, e <- cl ]
      grEdges = [ (s,t,()) | (t,(cl,_)) <- grNodes
                           , src:_ <- [bsAssignmentsForClass bs cl]
                           , se <- logicExprJavaExprs src
                           , let Just s = Map.lookup se exprNodeMap ]
      -- Compute strongly connected components.
      components = scc (mkGraph grNodes grEdges :: Gr (JavaExprEquivClass, JavaActualType) ())
  return $ if all (\l -> length l == 1) components
             then Just [ (cl, at, bsAssignmentsForClass bs cl)
                       | [n] <- components
                       , let (cl,at) = v V.! n ]
             else Nothing

-- Command utilities {{{2

-- | Return commands in behavior in order they appeared in spec.
bsCommands :: BehaviorSpec -> [BehaviorCommand]
bsCommands = reverse . bsReversedCommands

bsAddCommand :: BehaviorCommand -> BehaviorSpec -> BehaviorSpec
bsAddCommand bc bs =
  bs { bsReversedCommands = bc : bsReversedCommands bs }

bsAddAssumption :: LogicExpr -> BehaviorSpec -> BehaviorSpec
bsAddAssumption le bs =
  bs { bsAssumptions = le : bsAssumptions bs }

initMethodSpec :: Pos -> JSS.Codebase
               -> JSS.Class -> String
               -> IO JavaMethodSpecIR
initMethodSpec pos cb thisClass mname = do
  (methodClass,method) <- findMethod cb pos mname thisClass
  superClasses <- JSS.supers cb thisClass
  let this = thisJavaExpr thisClass
      initTypeMap | JSS.methodIsStatic method = Map.empty
                  | otherwise = Map.singleton this (ClassInstance thisClass)
      initBS = BS { bsLoc = JSS.BreakEntry
                  , bsActualTypeMap = initTypeMap
                  , bsMustAliasSet =
                      if JSS.methodIsStatic method then
                        CC.empty
                      else
                        CC.insertTerm this CC.empty
                  , bsMayAliasClasses = []
                  , bsLogicAssignments = []
                  , bsAssumptions = []
                  , bsReversedCommands = []
                  }
      initMS = MSIR { specPos = pos
                    , specCodebase = cb
                    , specThisClass = thisClass
                    , specMethodClass = methodClass
                    , specMethod = method
                    , specInitializedClasses =
                        map JSS.className superClasses
                    , specBehaviors = initBS
                    , specAllowAlloc = False
                    }
  return initMS

-- JavaMethodSpecIR {{{1

-- | This class captures the spec for the overall method.
data JavaMethodSpecIR = MSIR {
    -- | The position of the specification for error reporting purposes.
    specPos :: Pos
    -- | The codebase containing the method being specified.
  , specCodebase :: JSS.Codebase
    -- | Class used for this instance.
  , specThisClass :: JSS.Class
    -- | Class where method is defined.
  , specMethodClass :: JSS.Class
    -- | Method to verify.
  , specMethod :: JSS.Method
    -- | Class names expected to be initialized using JVM "/" separators.
    -- (as opposed to Java "." path separators). Currently this is set
    -- to the list of superclasses of specThisClass.
  , specInitializedClasses :: [String]
    -- | Behavior specifications for method at different PC values.
    -- A list is used because the behavior may depend on the inputs.
  , specBehaviors :: BehaviorSpec  -- Map JSS.Breakpoint [BehaviorSpec]
    -- | Whether this method is allowed to (invisibly) allocate new objects.
  , specAllowAlloc :: Bool
  }

-- | Return user printable name of method spec (currently the class + method name).
specName :: JavaMethodSpecIR -> String
specName ir =
 let clName = JSS.className (specThisClass ir)
     mName = JSS.methodName (specMethod ir)
  in JSS.slashesToDots clName ++ ('.' : mName)

-- TODO: error if already declared
specAddVarDecl :: JavaExpr -> JavaActualType
               -> JavaMethodSpecIR -> JavaMethodSpecIR
specAddVarDecl expr jt ms = ms { specBehaviors = bs'
                               , specInitializedClasses = cs'
                               }
  where bs = specBehaviors ms
        cs = specInitializedClasses ms
        cs' = case jt of
                ClassInstance c -> JSS.className c : cs
                _ -> cs
        bs' = bs { bsActualTypeMap =
                     Map.insert expr jt (bsActualTypeMap bs)
                 , bsMustAliasSet =
                     if isRefJavaExpr expr then
                       CC.insertTerm expr (bsMustAliasSet bs)
                     else
                       bsMustAliasSet bs
                 }

specAddLogicAssignment :: Pos -> JavaExpr -> MixedExpr
                       -> JavaMethodSpecIR -> JavaMethodSpecIR
specAddLogicAssignment pos expr t ms = ms { specBehaviors = bs' }
  where bs = specBehaviors ms
        las = bsLogicAssignments bs
        bs' = bs { bsLogicAssignments = (pos, expr, t) : las }

specAddAliasSet :: [JavaExpr] -> JavaMethodSpecIR -> JavaMethodSpecIR
specAddAliasSet exprs ms = ms { specBehaviors = bs' }
  where bs = specBehaviors ms
        bs' = bs { bsMayAliasClasses = exprs : bsMayAliasClasses bs }

specAddBehaviorCommand :: BehaviorCommand
                       -> JavaMethodSpecIR -> JavaMethodSpecIR
specAddBehaviorCommand bc ms =
  ms { specBehaviors = bsAddCommand bc (specBehaviors ms) }


specAddAssumption :: LogicExpr -> JavaMethodSpecIR -> JavaMethodSpecIR
specAddAssumption le ms =
  ms { specBehaviors = bsAddAssumption le (specBehaviors ms)}

specActualTypeMap :: JavaMethodSpecIR -> Map JavaExpr JavaActualType
specActualTypeMap = bsActualTypeMap . specBehaviors

specSetAllowAllocation :: JavaMethodSpecIR -> JavaMethodSpecIR
specSetAllowAllocation ms = ms { specAllowAlloc = True }

specAssumptions :: JavaMethodSpecIR -> [LogicExpr]
specAssumptions = bsAssumptions . specBehaviors
