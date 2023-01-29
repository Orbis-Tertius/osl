{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Trace.Types.EvaluationContext (EvaluationContext (EvaluationContext), ContextType (Global, Local)) where

import Data.Kind (Type)
import Data.Map (Map)
import Data.Set (Set)
import GHC.Generics (Generic)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import OSL.Types.OSL (ContextType (Global, Local))
import Stark.Types.Scalar (Scalar)
import Trace.Types (Case)

type EvaluationContext :: ContextType -> Type
data EvaluationContext t = EvaluationContext
  { globalMappings :: Map (Case, ColumnIndex) Scalar,
    localMappings :: Map ColumnIndex Scalar,
    lookupTables :: Map (Set LookupTableColumn) (Set (Map LookupTableColumn Scalar))
  }
  deriving (Generic, Show)

instance Semigroup (EvaluationContext t) where
  EvaluationContext a b c <> EvaluationContext d e f =
    EvaluationContext (a <> d) (b <> e) (c <> f)

instance Monoid (EvaluationContext t) where
  mempty = EvaluationContext mempty mempty mempty
