{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
    SudokuWitness (SudokuWitness, solution, rowPermutations, colPermutations, squarePermutations)
  ) where

import Data.Map (Map)
import GHC.Generics (Generic)

newtype Digit = Digit Integer
  deriving (Eq, Ord, Num, Enum, Show)

newtype Row = Row Integer
  deriving (Eq, Ord, Num, Enum, Show)

newtype Col = Col Integer
  deriving (Eq, Ord, Num, Enum, Show)

newtype Cell = Cell (Row, Col)
  deriving (Eq, Ord, Show)

newtype Problem = Problem {unProblem :: Cell -> Maybe Digit}

newtype Solution = Solution {unSolution :: Cell -> Digit}

newtype X = X Integer
  deriving (Eq, Ord, Num, Enum)

newtype Y = Y Integer
  deriving (Eq, Ord, Num, Enum)

newtype Square = Square (X, Y)
  deriving (Eq, Ord)

newtype SquareCell = SquareCell (X, Y)
  deriving (Eq, Ord)

data SudokuWitness = SudokuWitness
  { solution :: Solution,
    rowPermutations :: Map Row (Map Digit Col),
    colPermutations :: Map Col (Map Digit Row),
    squarePermutations :: Map Square (Map Digit SquareCell)
  }
  deriving (Generic)
