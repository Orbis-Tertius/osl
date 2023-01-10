module Trace.Types.EvaluationContext (EvaluationContext (EvaluationContext)) where

import Data.Map (Map)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Trace.Types (Case)

data EvaluationContext =
  EvaluationContext
  { globalMappings :: Map (Case, ColumnIndex) Scalar,
    localMappings :: Map ColumnIndex Scalar,
    lookupTables :: Map (Set LookupTableColumn) (Set (Map LookupTableColumn Scalar))
  }
