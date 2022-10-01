{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveGeneric #-}


module Halo2.Types.LogicToArithmeticColumnLayout
  ( SignColumnIndex (..)
  , ByteColumnIndex (..)
  , TruthValueColumnIndex (..)
  , AtomAdvice (..)
  , ByteRangeColumnIndex (..)
  , ZeroIndicatorColumnIndex (..)
  , TruthTableColumnIndices (..)
  , LogicToArithmeticColumnLayout (..)
  ) where


import Halo2.Prelude
import Halo2.Types.LogicConstraint (AtomicLogicConstraint)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)


newtype SignColumnIndex =
  SignColumnIndex { unSignColumnIndex :: ColumnIndex }
  deriving Generic


newtype ByteColumnIndex =
  ByteColumnIndex { unByteColumnIndex :: ColumnIndex }
  deriving Generic


newtype TruthValueColumnIndex =
  TruthValueColumnIndex
  { unTruthValueColumnIndex :: ColumnIndex }
  deriving Generic


data AtomAdvice =
  AtomAdvice
  { sign :: SignColumnIndex
  , bytes :: [ByteColumnIndex] -- most significant first
  , truthValue :: [TruthValueColumnIndex]
  } deriving Generic


newtype ByteRangeColumnIndex =
  ByteRangeColumnIndex
  { unByteRangeColumnIndex :: ColumnIndex }
  deriving Generic


newtype ZeroIndicatorColumnIndex =
  ZeroIndicatorColumnIndex
  { unZeroIndicatorColumnIndex :: ColumnIndex }
  deriving Generic


data TruthTableColumnIndices =
  TruthTableColumnIndices
  { byteRangeColumnIndex :: ByteRangeColumnIndex
  , zeroIndicatorColumnIndex :: ZeroIndicatorColumnIndex
  } deriving Generic


data LogicToArithmeticColumnLayout =
  LogicToArithmeticColumnLayout
  { columnTypes :: ColumnTypes
  , logicCircuitColumns :: Set ColumnIndex
  , atomAdvice :: Map AtomicLogicConstraint AtomAdvice
  , truthTable :: TruthTableColumnIndices
  } deriving Generic
