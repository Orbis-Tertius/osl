{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}

module Halo2.BoundLogicConstraintComplexity
  ( ComplexityBound (ComplexityBound),
    boundLogicConstraintComplexity,
  )
where

import Control.Lens ((^.))
import Control.Monad.Trans.State (State, execState, get, put)
import qualified Data.Map as Map
import GHC.Generics (Generic)
import Halo2.Polynomial (constant, var')
import Halo2.Types.Circuit (Circuit (Circuit), LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType (Advice))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top))
import Halo2.Types.LogicConstraints (LogicConstraints (LogicConstraints))

newtype ComplexityBound = ComplexityBound {unComplexityBound :: Int}
  deriving (Eq, Ord, Num, Generic)

data S = S ColumnTypes LogicConstraints
  deriving (Generic)

boundLogicConstraintComplexity ::
  ComplexityBound ->
  LogicCircuit ->
  LogicCircuit
boundLogicConstraintComplexity bound x =
  let S colTypes gateConstraints =
        execState
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
go n p = addConstraint =<< go' n n p

go' :: ComplexityBound -> ComplexityBound -> LogicConstraint -> State S LogicConstraint
go' _ 0 (Atom p) = pure (Atom p)
go' n0 0 p = do
  i <- addCol
  p' <- go' n0 n0 p
  addConstraint (Atom (var' i `Equals` constant 1) `Iff` p')
  addConstraint (Atom (var' i `Equals` constant 1) `Or` Atom (var' i `Equals` constant 0))
  pure (Atom (var' i `Equals` constant 1))
go' n0 n r =
  case r of
    Atom p -> pure (Atom p)
    Not p -> Not <$> rec n p
    And p q -> And <$> rec (n - 1) p <*> rec (n - 1) q
    Or p q -> Or <$> rec (n - 1) p <*> rec (n - 1) q
    Iff p q -> Iff <$> rec (n - 1) p <*> rec (n - 1) q
    Top -> pure Top
    Bottom -> pure Bottom
  where
    rec = go' n0

addConstraint :: LogicConstraint -> State S ()
addConstraint p = do
  S colTypes constraints <- get
  put (S colTypes (constraints <> LogicConstraints [p] mempty))

addCol :: State S ColumnIndex
addCol = do
  S colTypes constraints <- get
  let i = maybe 0 ((1 +) . fst) (Map.lookupMax (colTypes ^. #getColumnTypes))
  put (S (colTypes <> ColumnTypes (Map.singleton i Advice)) constraints)
  pure i
