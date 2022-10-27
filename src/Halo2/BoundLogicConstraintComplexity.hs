{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}


module Halo2.BoundLogicConstraintComplexity
  ( ComplexityBound (ComplexityBound)
  , boundLogicConstraintComplexity
  ) where


import Control.Lens ((^.))
import Control.Monad.Trans.State (State, execState, get, put)
import qualified Data.Map as Map
import GHC.Generics (Generic)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType (Advice))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.LogicConstraint (LogicConstraint)
import Halo2.Types.LogicConstraints (LogicConstraints (LogicConstraints))
import Halo2.Types.Circuit (LogicCircuit, Circuit (Circuit))


newtype ComplexityBound = ComplexityBound { unComplexityBound :: Int }
  deriving Generic


data S = S ColumnTypes LogicConstraints
  deriving Generic


boundLogicConstraintComplexity
  :: ComplexityBound
  -> LogicCircuit
  -> LogicCircuit
boundLogicConstraintComplexity bound x =
  let S colTypes gateConstraints = execState
        (mapM_ (go bound) (x ^. #gateConstraints . #constraints))
        (S (x ^. #columnTypes) (LogicConstraints mempty (x ^. #gateConstraints . #bounds)))
  in Circuit
     colTypes
     (x ^. #equalityConstrainableColumns)
     gateConstraints
     (x ^. #lookupArguments)
     (x ^. #rowCount)
     (x ^. #equalityConstraints)
     (x ^. #fixedValues)


go :: ComplexityBound -> LogicConstraint -> State S ()
go = todo


addCol :: State S ColumnIndex
addCol = do
  S colTypes constraints <- get
  let i = maybe 0 ((1+) . fst) (Map.lookupMax (colTypes ^. #getColumnTypes))
  put (S (colTypes <> ColumnTypes (Map.singleton i Advice)) constraints)
  pure i


todo :: a
todo = todo
