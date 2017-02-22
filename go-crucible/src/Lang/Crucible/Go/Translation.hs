{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

module Lang.Crucible.Go.Translation where

import Language.Go.AST
import Language.Go.Parser (ParserAnnotation)
import Language.Go.Types hiding (Complex)
import qualified Language.Go.Types as Go

import Lang.Crucible.RegCFG
import Lang.Crucible.Core (AnyCFG(..))
import qualified Lang.Crucible.Core as C
import Lang.Crucible.Generator hiding (Label)
import qualified Lang.Crucible.Generator as Gen
import Lang.Crucible.Types
import Lang.Crucible.BaseTypes
import Lang.Crucible.SSAConversion( toSSA )
import Lang.Crucible.FunctionHandle
import Lang.Crucible.FunctionName (functionNameFromText)
import Lang.Crucible.ProgramLoc

import Data.Parameterized.Some
import Data.Parameterized.NatRepr
import qualified Data.Parameterized.Context as Ctx

import Data.Int
import Data.Maybe
import Control.Monad.ST
import Control.Monad (foldM)
import Control.Monad.State
import Data.Text (Text)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Default.Class
import Lens.Simple
  
translateFunction :: forall h. Id ParserAnnotation -> ParameterList ParserAnnotation -> ReturnList ParserAnnotation -> [Statement ParserAnnotation] -> ST h AnyCFG
translateFunction (Id _ fname) params returns body =
  withHandleAllocator $ \ha ->
  bindReturns returns $ \(retctx :: CtxRepr tretctx) setupReturns ->
  bindParams params $ \(ctx :: CtxRepr tctx) setupParams ->
  do fnhandle <- mkHandle' ha (functionNameFromText fname) ctx (StructRepr retctx)
     (SomeCFG g, []) <- defineFunction InternalPos fnhandle
                        (\assignment -> (def,
                                         do retslots <- setupReturns
                                            modify (\ts -> ts {returnSlots = retslots})

                                            setupParams assignment
                                            graphGenerator body (StructRepr retctx)))
     case toSSA g of
       C.SomeCFG gs -> return $ AnyCFG gs

bindReturns :: ReturnList ParserAnnotation
            -> (forall ctx. CtxRepr ctx -> (forall s ret rctx. Generator h s (TransState rctx) ret (Maybe (VariableAssignment s ctx))) -> a)
            -> a
bindReturns rlist f =
  let goNamed :: [NamedParameter ParserAnnotation]
              -> (forall ctx. CtxRepr ctx -> (forall s ret rctx. Generator h s (TransState rctx) ret (VariableAssignment s ctx)) -> a)
              -> a
      goNamed [] k = k Ctx.empty (return Ctx.empty)
      goNamed ((NamedParameter _ (Id (_, Just (TypeB vt)) rname) _):ps) k =
        translateType {- TODO Abstract this: implicit parameter or generator state -}
           32 vt (\t zv ->
                    goNamed ps (\ctx gen -> k (ctx Ctx.%> t)
                                 (do assign <- gen
                                     reg <- declareVar rname zv t
                                     return (assign Ctx.%> GoVarOpen reg))
                               ))
      goAnon :: [Type ParserAnnotation] -> (forall ctx. CtxRepr ctx -> a) -> a
      goAnon [] k = k Ctx.empty
      goAnon (t:ts) k = case snd $ t^.ann of
        Just (TypeB vt) -> translateType 32 vt $ \t _ ->
          goAnon ts (\ctx -> k (ctx Ctx.%> t))
        _ -> error "Expecting a semantic type inferred for a return type, but found none"
  in case rlist of
    NamedReturnList _ nrets -> goNamed nrets $ \ctx gen -> f ctx (Just <$> gen)
    AnonymousReturnList _ rtypes -> goAnon rtypes $ \ctx -> f ctx (return Nothing)

type VariableAssignment s ctx = Ctx.Assignment (GoVarOpen s) ctx
newtype GoVarOpen s tp = GoVarOpen {unGoVarOpen :: Reg s (ReferenceType tp)}

-- | Generate the Crucible type context and bind parameter names to
-- (typed) Crucible registers
bindParams :: ParameterList ParserAnnotation
           -> (forall ctx. CtxRepr ctx
               -> (forall s ret. Ctx.Assignment (Atom s) ctx -> Generator h s (TransState rctx) ret ())
               -> a)
           -> a
bindParams plist f =
  let go :: [NamedParameter ParserAnnotation]
         -> (forall ctx. CtxRepr ctx
             -> (forall s ret. Ctx.Assignment (Atom s) ctx -> Generator h s (TransState rctx) ret ())
             -> a)
         -> a
      go []     k = k Ctx.empty (\_ -> return ())
      go ((NamedParameter _ (Id (_, Just (TypeB vt)) pname) _):ps) k =
        translateType {- TODO Abstract this: implicit parameter or generator state -}
        32 vt $ \t zv -> go ps (\ctx f -> k (ctx Ctx.%> t) 
                                         (\a -> do f (Ctx.init a)
                                                   void $ declareVar pname (AtomExpr (Ctx.last a)) t))
  in case plist of
    NamedParameterList _ params mspread -> go (params ++ maybeToList mspread) f
    AnonymousParameterList _ _ _ -> error "Unexpected anonymous parameter list in a function definition"

data TransState ctx s = TransState {lexenv :: !(HashMap Text (GoVarReg s))
                                   ,enclosingLabels :: !(LabelStack s)
                                   ,returnSlots :: !(Maybe (VariableAssignment s ctx))
                                   }

instance Default (TransState ctx s) where
  def = TransState {lexenv = HM.empty
                   ,enclosingLabels = LabelStack []
                   ,returnSlots = Nothing}

data GoVarReg s where
  GoVarReg :: TypeRepr tp -> Reg s (ReferenceType tp) -> GoVarReg s
                   
newtype LabelStack s = LabelStack [Gen.Label s]

declareVar :: Text -> Expr s tp -> TypeRepr tp -> Generator h s (TransState rctx) ret (Reg s (ReferenceType tp))
declareVar name value t = do ref <- newReference value
                             reg <- newReg ref
                             modify' (\ts -> ts {lexenv = HM.insert name (GoVarReg t reg) (lexenv ts)})
                             return reg


graphGenerator :: [Statement ParserAnnotation] -> TypeRepr ret -> Generator h s (TransState rctx) ret (Expr s ret)
graphGenerator body retTypeRepr =
  do mapM (\s -> generateStatement s retTypeRepr) body
     reportError $ App (C.TextLit "Expected a return statement, but found none.")
  -- do Just Refl <- return $ testEquality retTypeRepr $ BVRepr (knownNat :: NatRepr 32)
  --    return $ App (C.BVLit (knownNat :: NatRepr 32) 12)

generateStatement :: Statement ParserAnnotation -> TypeRepr ret -> Generator h s (TransState rctx) ret (Expr s ret)
generateStatement s retTypeRepr = undefined

-- | Translate a Go type to a Crucible type
translateType :: forall a. Int32 {-Target architecture word size-}
              -> ValueType
              -> (forall typ. TypeRepr typ -> (forall s. Expr s typ) -> a)
              -> a
translateType wordSize typ = typeAsRepr (instantiateWordSize wordSize typ)

instantiateWordSize :: Int32 -> ValueType -> ValueType
instantiateWordSize wordSize typ = case typ of
  Int Nothing signed -> Int (Just wordSize) signed
  _                  -> typ

typeAsRepr :: forall a. ValueType
           -> (forall typ. TypeRepr typ -> (forall s. Expr s typ) -> a)
           -> a
typeAsRepr typ lifter = injectType (toTypeRepr typ)
   where injectType :: ReprAndValue -> a
         injectType (ReprAndValue repr zv) = lifter repr zv

toTypeRepr :: ValueType
           -> ReprAndValue
toTypeRepr typ = case typ of
  Int (Just width) _ -> case someNat (fromIntegral width) of
    Just (Some w) | Just LeqProof <- isPosNat w -> ReprAndValue (BVRepr w) undefined
    _ -> error $ unwords ["invalid integer width",show width]
  Float width -> ReprAndValue RealValRepr undefined
  Boolean -> ReprAndValue BoolRepr undefined
  Go.Complex width -> undefined
  Iota -> ReprAndValue IntegerRepr undefined
  Nil -> ReprAndValue (MaybeRepr AnyRepr) undefined
  String -> ReprAndValue (VectorRepr $ BVRepr (knownNat :: NatRepr 8)) undefined
  Function mrecvtyp paramtyps mspreadtyp returntyps -> undefined -- Ctx.Assignment????
  Array _ typ -> typeAsRepr typ $ \t tzv -> ReprAndValue (VectorRepr t) undefined
  Struct fields -> undefined
  Pointer typ -> ReprAndValue (ReferenceRepr AnyRepr) undefined
  Go.Interface sig -> undefined
  Map keyType valueType -> undefined
  Slice typ -> typeAsRepr typ $ \t zv -> ReprAndValue (StructRepr undefined) undefined
  Channel _ typ -> toTypeRepr typ
  BuiltIn name -> undefined -- ^ built-in function
  Alias (TypeName (Just bind) _ _) -> undefined

data ReprAndValue = forall typ. ReprAndValue (TypeRepr typ) (forall s. Expr s typ)
