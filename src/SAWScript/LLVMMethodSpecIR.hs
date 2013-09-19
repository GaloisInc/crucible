-- | Provides 
{- |
Module           : $Header$
Description      : Provides typechecked representation for LLVM function
                   specifications and function for creating it from AST
                   representation.
Stability        : provisional
Point-of-contact : atomb
-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.LLVMMethodSpecIR 
  ( LLVMSetup
  , LLVMSetupState(..)
    -- * MethodSpec record
  , LLVMMethodSpecIR
  , specName
  , specPos
  , specCodebase
  , specFunction
  , specBehavior
  , specValidationPlan
  , specAddBehaviorCommand
  , specAddVarDecl
  , specSetVerifyTactic
  , specLLVMExprNames
  , initLLVMMethodSpec
    -- * Method behavior.
  , BehaviorSpec
  , bsLoc
  , bsPtrExprs
  , bsActualTypeMap
  , bsLogicAssignments
  , BehaviorCommand(..)
  , bsCommands
  , ValidationPlan(..)
  ) where

-- Imports {{{1

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Graph.Inductive (scc, Gr, mkGraph)
import Data.List (sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust, catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))

import qualified Verifier.LLVM.Codebase as LSS
import Verifier.LLVM.Backend.SAW

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verinf.Symbolic as L

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.CongruenceClosure (CCSet)
import SAWScript.LLVMExpr
import SAWScript.Utils
import SAWScript.Proof

-- Integration with SAWScript

data LLVMSetupState
  = LLVMSetupState {
      lsSpec :: LLVMMethodSpecIR
    , lsContext :: SharedContext LSSCtx
    }

type LLVMSetup a = StateT LLVMSetupState IO a

-- ExprActualTypeMap {{{1

-- | Maps LLVM expressions for references to actual type.
type ExprActualTypeMap = Map LLVMExpr LLVMActualType

{-
-- Alias definitions {{{1

type LLVMExprEquivClass = [LLVMExpr]

-- | Returns a name for the equivalence class.
ppLLVMExprEquivClass :: LLVMExprEquivClass -> Doc
ppLLVMExprEquivClass [] = error "internal: ppLLVMExprEquivClass"
ppLLVMExprEquivClass [expr] = ppLLVMExpr expr
ppLLVMExprEquivClass cl = list (map ppLLVMExpr (sort cl))
-}

-- BehaviorSpec {{{1

-- | Postconditions used for implementing behavior specification. All
-- LogicExprs in behavior commands need to be extracted with
-- useLogicExpr, in a specific shared context, before they can be
-- used.
data BehaviorCommand
     -- | An assertion that is assumed to be true in the specificaiton.
   = AssertPred Pos LogicExpr
     -- | An assumption made in a conditional behavior specification.
   | AssumePred LogicExpr
     -- | Assign an LLVM variables the value given by the mixed expression.
   | Ensure Pos LLVMExpr MixedExpr
     -- | Modify an LLVM variables to an arbitrary expression.
     -- integral type or array.
   | Modify LLVMExpr LLVMActualType
     -- | Specifies return value for a function.
   | Return MixedExpr

data BehaviorSpec = BS {
         -- | Program counter for spec.
         bsLoc :: LSS.SymBlockID
         -- | Maps all expressions seen along path to actual type.
       , bsActualTypeMap :: ExprActualTypeMap
         -- | Stores which LLVM expressions must alias each other.
{-
       , bsMustAliasSet :: CCSet LLVMExprF
         -- | May alias relation between LLVM expressions.
       , bsMayAliasClasses :: [[LLVMExpr]]
-}
         -- | Equations 
       , bsLogicAssignments :: [(Pos, LLVMExpr, LogicExpr)]
         -- | Commands to execute in reverse order.
       , bsReversedCommands :: [BehaviorCommand]
       }

-- | Returns list of all LLVM expressions that are not pointers.
bsExprs :: BehaviorSpec -> [LLVMExpr]
bsExprs bs = Map.keys (bsActualTypeMap bs)

-- | Returns list of all LLVM expressions that are pointers.
bsPtrExprs :: BehaviorSpec -> [LLVMExpr]
bsPtrExprs bs = filter isPtrLLVMExpr (bsExprs bs)

{-
bsMayAliasSet :: BehaviorSpec -> CCSet LLVMExprF
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
                  res = "All pointers that may alias must be assigned the same type."
              throwIOExecException pos (ftext msg) res

type PtrEquivConfiguration = [(LLVMExprEquivClass, LLVMActualType)]

-- | Returns all possible potential equivalence classes for spec.
bsRefEquivClasses :: BehaviorSpec -> [PtrEquivConfiguration]
bsRefEquivClasses bs = 
  map (map parseSet . CC.toList) $ Set.toList $
    CC.mayAliases (bsMayAliasClasses bs) (bsMustAliasSet bs)
 where parseSet l@(e:_) =
         case Map.lookup e (bsActualTypeMap bs) of
           Just tp -> (l,tp)
           Nothing -> error $ "internal: bsRefEquivClass given bad expression: " ++ show e
       parseSet [] = error "internal: bsRefEquivClasses given empty list."

bsPrimitiveExprs :: BehaviorSpec -> [LLVMExpr]
bsPrimitiveExprs bs =
  [ e | (e, ty) <- Map.toList (bsActualTypeMap bs), isPrimitiveType ty ]
 
asLLVMExpr :: Map String LLVMExpr -> LogicExpr -> Maybe LLVMExpr
asLLVMExpr m (asCtor -> Just (i, [e])) =
  case e of
    (asStringLit -> Just s) | i == parseIdent "LLVM.mkValue" -> Map.lookup s m
    _ -> Nothing
asLLVMExpr _ _ = Nothing

bsLogicEqs :: Map String LLVMExpr -> BehaviorSpec -> [(LLVMExpr, LLVMExpr)]
bsLogicEqs m bs =
  [ (lhs,rhs') | (_,lhs,rhs) <- bsLogicAssignments bs
               , let Just rhs' = asLLVMExpr m rhs]

-- | Returns logic assignments to equivance class.
bsAssignmentsForClass :: Map String LLVMExpr -> BehaviorSpec -> LLVMExprEquivClass
                      -> [LogicExpr]
bsAssignmentsForClass m bs cl = res 
  where s = Set.fromList cl
        res = [ rhs 
              | (_,lhs,rhs) <- bsLogicAssignments bs
              , Set.member lhs s
              , not (isJust (asLLVMExpr m rhs)) ]

-- | Retuns ordering of LLVM expressions to corresponding logic value.
bsLogicClasses :: forall s.
                  SharedContext s
               -> Map String LLVMExpr
               -> BehaviorSpec
               -> PtrEquivConfiguration
               -> IO (Maybe [(LLVMExprEquivClass, SharedTerm s, [LogicExpr])])
bsLogicClasses sc m bs cfg = do
  let allClasses = CC.toList
                   -- Add logic equations.
                   $ flip (foldr (uncurry CC.insertEquation)) (bsLogicEqs m bs)
                   -- Add primitive expression.
                   $ flip (foldr CC.insertTerm) (bsPrimitiveExprs bs)
                   -- Create initial set with references.
                   $ CC.fromList (map fst cfg)
  logicClasses <- (catMaybes <$>) $
                  forM allClasses $ \(cl@(e:_)) -> do
                    case Map.lookup e (bsActualTypeMap bs) of
                      Just at -> do
                        mtp <- logicTypeOfActual sc at
                        case mtp of
                          Just tp -> return (Just (cl, tp))
                          Nothing -> return Nothing
                      Nothing -> return Nothing
  let v = V.fromList logicClasses
      -- Create nodes.
      grNodes = [0..] `zip` logicClasses
      -- Create edges
      exprNodeMap = Map.fromList [ (e,n) | (n,(cl,_)) <- grNodes, e <- cl ]
      grEdges = [ (s,t,()) | (t,(cl,_)) <- grNodes
                           , src:_ <- [bsAssignmentsForClass m bs cl]
                           , se <- Set.toList (logicExprLLVMExprs src)
                           , let Just s = Map.lookup se exprNodeMap ]
      -- Compute strongly connected components.
      components = scc (mkGraph grNodes grEdges :: Gr (LLVMExprEquivClass, SharedTerm s) ())
  return $ if all (\l -> length l == 1) components
             then Just [ (cl, at, bsAssignmentsForClass m bs cl)
                       | [n] <- components
                       , let (cl,at) = v V.! n ]
             else Nothing
-}

-- Command utilities {{{2

-- | Return commands in behavior in order they appeared in spec.
bsCommands :: BehaviorSpec -> [BehaviorCommand]
bsCommands = reverse . bsReversedCommands

bsAddCommand :: BehaviorCommand -> BehaviorSpec -> BehaviorSpec
bsAddCommand bc bs =
  bs { bsReversedCommands = bc : bsReversedCommands bs }

type Backend = SAWBackend LSSCtx L.Lit

initLLVMMethodSpec :: Pos -> LSS.Codebase Backend -> String
                   -> IO LLVMMethodSpecIR
initLLVMMethodSpec pos cb symname = do
  let sym = fromString symname
      Just def = LSS.lookupDefine sym cb
  let initBS = BS { bsLoc = LSS.sdEntry def
                  , bsActualTypeMap = Map.empty
{-
                  , bsMustAliasSet = CC.empty
                  , bsMayAliasClasses = []
-}
                  , bsLogicAssignments = []
                  , bsReversedCommands = []
                  }
      initMS = MSIR { specPos = pos
                    , specCodebase = cb
                    , specFunction = def
                    , specLLVMExprNames = Map.empty
                    , specBehavior = initBS
                    , specValidationPlan = Skip
                    }
  return initMS

-- resolveValidationPlan {{{1

-- The ProofScript in RunVerify is in the SAWScript context, and
-- should stay there.
data ValidationPlan
  = Skip
  | RunVerify (ProofScript SAWCtx ProofResult)

-- MethodSpecIR {{{1

data LLVMMethodSpecIR = MSIR {
    specPos :: Pos
    -- | Codebase containing function to verify.
  , specCodebase :: LSS.Codebase Backend
    -- | Function to verify.
  , specFunction :: LSS.SymDefine (SharedTerm LSSCtx)
    -- | Mapping from user-visible LLVM state names to LLVMExprs
  , specLLVMExprNames :: Map String LLVMExpr
    -- | Behavior specification for method.
  , specBehavior :: BehaviorSpec
    -- | Describes how the method is expected to be validated.
  , specValidationPlan :: ValidationPlan
  }

-- | Return user printable name of method spec (currently the class +
-- method name).
specName :: LLVMMethodSpecIR -> Doc
specName = LSS.ppSymbol . LSS.sdName . specFunction

specAddVarDecl :: String -> LLVMExpr -> LLVMActualType
               -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddVarDecl name expr lt ms = ms { specBehavior = bs'
                                    , specLLVMExprNames = ns' }
  where bs = specBehavior ms
        bs' = bs { bsActualTypeMap =
                     Map.insert expr lt (bsActualTypeMap bs) }
        ns' = Map.insert name expr (specLLVMExprNames ms)

{-
specAddAliasSet :: [LLVMExpr] -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddAliasSet exprs ms = ms { specBehavior = bs' }
  where bs = specBehavior ms
        bs' = bs { bsMayAliasClasses = exprs : bsMayAliasClasses bs }
-}

specAddBehaviorCommand :: BehaviorCommand
                       -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddBehaviorCommand bc ms =
  ms { specBehavior = bsAddCommand bc (specBehavior ms) }

specSetVerifyTactic :: ProofScript SAWCtx ProofResult
                    -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specSetVerifyTactic script ms = ms { specValidationPlan = RunVerify script }
