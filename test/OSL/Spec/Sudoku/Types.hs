{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

module OSL.Spec.Sudoku.Types
  ( Digit (Digit),
    Row (Row),
    Col (Col),
    Cell (Cell),
    Problem (Problem, unProblem),
    Solution (Solution, unSolution),
    X (X),
    Y (Y),
    Square (Square),
    SquareCell (SquareCell),
    SudokuWitness (SudokuWitness, solution, rowPermutations, colPermutations, squarePermutations),
  )
where

import Data.Map (Map)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import OSL.FromHaskell (ToOSLType)

newtype Digit = Digit Integer
  deriving (Eq, Ord, Num, Enum, Show, Generic, ToOSLType, Typeable)

newtype Row = Row Integer
  deriving (Eq, Ord, Num, Enum, Show, Generic, ToOSLType, Typeable)

newtype Col = Col Integer
  deriving (Eq, Ord, Num, Enum, Show, Generic, ToOSLType, Typeable)

newtype Cell = Cell (Row, Col)
  deriving (Eq, Ord, Show, Generic, Typeable, ToOSLType)

newtype Problem = Problem {unProblem :: Cell -> Maybe Digit}
  deriving (Generic, ToOSLType)

newtype Solution = Solution {unSolution :: Cell -> Digit}
  deriving (Generic, ToOSLType)

newtype X = X Integer
  deriving (Eq, Ord, Num, Enum, Generic, ToOSLType)

newtype Y = Y Integer
  deriving (Eq, Ord, Num, Enum, Generic, ToOSLType)

newtype Square = Square (X, Y)
  deriving (Eq, Ord, Generic, ToOSLType)

newtype SquareCell = SquareCell (X, Y)
  deriving (Eq, Ord, Generic, ToOSLType)

data SudokuWitness = SudokuWitness
  { solution :: Solution,
    rowPermutations :: Map Row (Map Digit Col),
    colPermutations :: Map Col (Map Digit Row),
    squarePermutations :: Map Square (Map Digit SquareCell)
  }
  deriving (Generic)
