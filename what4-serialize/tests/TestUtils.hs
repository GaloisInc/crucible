{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module TestUtils where

import           Control.Monad ( forM_, when )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Function ( on )
import qualified Data.List as L
import           Data.Parameterized.Classes
import           Data.Parameterized.List ( List( (:<) ) )
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Hedgehog
import           System.Directory
import qualified What4.Expr.Builder as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import           Prelude


debugFile :: FilePath
debugFile = "what4serialize.log"

debugReset :: IO ()
debugReset = do e <- doesFileExist debugFile
                when e $ removeFile debugFile

debugOut, alwaysPrint :: MonadIO m => String -> m ()
debugOut msg = liftIO $ do appendFile debugFile (msg <> "\n")
                           -- alwaysPrint  -- comment this out to disable printing
                           return ()
alwaysPrint = liftIO . putStrLn


compareSymFnsSimply
  :: ( MonadIO m
     , MonadTest m
     , ShowF (WI.BoundVar sym)
     , WI.BoundVar sym ~ WE.ExprBoundVar t
     ) =>
     sym
  -> WI.SymFn sym args ret
  -> WI.SymFn sym args ret
  -> m ()
compareSymFnsSimply sym origFormula resultFormula = failure

  -- do on (===) SF.pfUses origFormula resultFormula

  --    compareOperandLists sym ncycles
  --      (SF.pfOperandVars origFormula)
  --      (SF.pfOperandVars resultFormula)

  --    compareLiteralVarMaps sym
  --      (SF.pfLiteralVars origFormula)
  --      (SF.pfLiteralVars resultFormula)

  --    on (===) (MapF.size . SF.pfDefs) origFormula resultFormula
  --    on (===) (MapF.keys . SF.pfDefs) origFormula resultFormula

compareSymFnsSymbolically
  :: ( MonadIO m
     , MonadTest m
     , ShowF (WI.BoundVar sym)
     , WI.BoundVar sym ~ WE.ExprBoundVar t
     , WI.IsExprBuilder sym
     ) =>
     sym
  -> WI.SymFn sym args ret
  -> WI.SymFn sym args ret
  -> m ()
compareSymFnsSymbolically sym origFormula resultFormula = failure

  -- do on (===) SF.pfUses origFormula resultFormula

  --    compareOperandLists sym ncycles
  --      (SF.pfOperandVars origFormula)
  --      (SF.pfOperandVars resultFormula)

  --    compareLiteralVarMaps sym
  --      (SF.pfLiteralVars origFormula)
  --      (SF.pfLiteralVars resultFormula)

  --    on (===) (MapF.size . SF.pfDefs) origFormula resultFormula
  --    on (===) (MapF.keys . SF.pfDefs) origFormula resultFormula
  --    (_te1, f1) <- liftIO $ instantiateFormula sym origFormula operands
  --    (_te2, f2) <- liftIO $ instantiateFormula sym resultFormula operands
  --    -- NOTE: The test architecture doesn't even support memory, so we don't
  --    -- need to specify any memory locations to test here.  If we do need to
  --    -- check that, we'll have go carefully set up memory to make the test
  --    -- possible.
  --    equiv <- liftIO $ formulasEquivSym sym [] f1 f2
  --    case equiv of
  --      Equivalent -> success
  --      DifferentBehavior _ -> failure
  --      Timeout -> failure



compareBVars :: ( MonadIO m
                , MonadTest m
                , WI.BoundVar sym ~ WE.ExprBoundVar t
                ) =>
                Maybe String
             -> sym
             -> Integer
             -> WI.BoundVar sym ty
             -> WI.BoundVar sym ty
             -> m ()
compareBVars mbPrefix _ ncycles origOprnd resultOprnd = do
  -- debugPrint $ "bvId=" <> show (WE.bvarId origOprnd)
  -- debugPrint $ "bvLoc=" <> show (WE.bvarLoc origOprnd)
  -- debugPrint $ "bvName=" <> show (WE.bvarName origOprnd)
  -- debugPrint $ "bvType=" <> show (WE.bvarType origOprnd)
  -- If the resultOprnd is supplied via a Formula Parse, the Parse
  -- operation will add an 'operandVarPrefix' (e.g. "op_") prefix to
  -- the parsed names to indicate they occurred in the operand
  -- location.  Allow that here if it is present.
  let orignm = bvName origOprnd
      rsltnm = bvName resultOprnd
      bvName = WE.bvarName
      rsltnm_str = show rsltnm
      newnm = WI.userSymbol $ dropPfx ncycles mbPrefix rsltnm_str
      dropPfx _ Nothing s = s
      dropPfx 0 _ s = s
      dropPfx n (Just p) s = let s' = if p `L.isPrefixOf` s
                                      then drop (length p) s
                                      else s
                             in dropPfx (n-1) mbPrefix s'
  if (orignm == rsltnm)
    then orignm === rsltnm
    else do nm' <- evalEither newnm
            orignm === nm'
  on compareBaseTypes WE.bvarType origOprnd resultOprnd
  -- cannot compare bvarId: generated via Nonce
  -- cannot compare bvarKind: not exported from What4.Expr.Builder
  -- cannot compare bvarLoc: dependent on sym state
  success


----------------------------------------------------------------------
-- BaseTypes

-- | Verifies that two BaseTypes are equal
compareBaseTypes :: ( MonadIO m
                    , MonadTest m
                    ) =>
                    WI.BaseTypeRepr t1 -> WI.BaseTypeRepr t2 -> m ()
compareBaseTypes ty1 ty2 =
  case testEquality ty1 ty2 of
    Just Refl -> success
    Nothing -> show ty1 === show ty2 -- fails, but reveals types
