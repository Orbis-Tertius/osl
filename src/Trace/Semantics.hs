{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Trace.Semantics
  ( evalTrace
  ) where

import Control.Lens ((^.))
import Control.Monad (forM_, forM, when)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Halo2.Types.CellReference (CellReference)
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Stark.Types.Scalar (Scalar)
import Trace.Types (TraceType, Trace, Case, SubexpressionId, ResultExpressionId (ResultExpressionId))
import Trace.Types.EvaluationContext (EvaluationContext, ContextType (Global, Local))

evalTrace ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
evalTrace ann tt t = do
  checkAllResultsArePresentForUsedCases ann tt t
  checkAllStepConstraintsAreSatisfied ann tt t
  checkAllEqualityConstraintsAreSatisfied ann tt t

checkAllResultsArePresentForUsedCases ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
checkAllResultsArePresentForUsedCases ann tt t =
  forM_ (t ^. #usedCases) $ \c ->
    forM_ (tt ^. #results) $ \(ResultExpressionId sId) ->
      maybe (Left (ErrorMessage ann "result is not present"))
        (const (pure ())) (Map.lookup (c, sId) (t ^. #subexpressions))

checkAllStepConstraintsAreSatisfied ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
checkAllStepConstraintsAreSatisfied ann tt t = do
  gc <- getGlobalEvaluationContext ann tt t
  forM_ (Map.keys (t ^. #subexpressions)) $ \(c, sId) -> do
    lc <- getSubexpressionEvaluationContext ann tt t gc (c, sId)
    checkStepConstraintsAreSatisfied ann tt c sId lc

checkStepConstraintsAreSatisfied ::
  ann ->
  TraceType ->
  Case ->
  SubexpressionId ->
  EvaluationContext 'Local ->
  Either (ErrorMessage ann) ()
checkStepConstraintsAreSatisfied = todo

checkAllEqualityConstraintsAreSatisfied ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
checkAllEqualityConstraintsAreSatisfied ann tt t = do
  cellMap <- getGlobalCellMap <$> getGlobalEvaluationContext ann tt t
  forM_ (tt ^. #equalityConstraints . #getEqualityConstraints) $ \eq -> do
    vs <- mapM (lookupCellReference ann cellMap) (Set.toList (eq ^. #getEqualityConstraint))
    case vs of
      [] -> pure ()
      (v:_) -> when (not (all (== v) vs)) (Left (ErrorMessage ann "equality constraint not satisifed"))

lookupCellReference ::
  ann ->
  Map CellReference Scalar ->
  CellReference ->
  Either (ErrorMessage ann) Scalar
lookupCellReference = todo

getGlobalCellMap ::
  EvaluationContext t ->
  Map CellReference Scalar
getGlobalCellMap = todo

getGlobalEvaluationContext ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) (EvaluationContext 'Global)
getGlobalEvaluationContext = todo traceTypeLookupTables

traceTypeLookupTables ::
  TraceType ->
  Set (Set LookupTableColumn)
traceTypeLookupTables = todo

getSubexpressionEvaluationContext ::
  ann ->
  TraceType ->
  Trace ->
  EvaluationContext 'Global ->
  (Case, SubexpressionId) ->
  Either (ErrorMessage ann) (EvaluationContext 'Local)
getSubexpressionEvaluationContext = todo getLookupTable

getLookupTable ::
  ann ->
  TraceType ->
  Trace ->
  EvaluationContext 'Global ->
  Set LookupTableColumn ->
  Either (ErrorMessage ann) (Set (Map LookupTableColumn Scalar))
getLookupTable ann tt t gc cs =
  fmap Set.fromList $ forM (Map.keys (t ^. #subexpressions)) $ \(c, sId) -> do
    lc <- getSubexpressionEvaluationContext ann tt t gc (c, sId)
    Map.fromList <$> sequence
      [ maybe (Left (ErrorMessage ann "lookup table has a hole"))
          (pure . (col,)) (Map.lookup (col ^. #unLookupTableColumn) (lc ^. #localMappings))
       | col <- Set.toList cs
      ]

todo :: a
todo = todo
