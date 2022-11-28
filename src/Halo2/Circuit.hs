{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}

module Halo2.Circuit
  ( HasPolynomialVariables (getPolynomialVariables),
    HasScalars (getScalars),
  ) where


import Halo2.Prelude
import Halo2.Types.Circuit (Circuit)
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Stark.Types.Scalar (Scalar)


class HasPolynomialVariables a where
  getPolynomialVariables :: a -> Set PolynomialVariable

instance HasPolynomialVariables LogicConstraints where
  getPolynomialVariables = todo

instance HasPolynomialVariables LookupArguments where
  getPolynomialVariables = todo

instance HasPolynomialVariables a => HasPolynomialVariables (Circuit a) where
  getPolynomialVariables x =
    mconcat
    [ getPolynomialVariables (x ^. #gateConstraints),
      getPolynomialVariables (x ^. #lookupArguments)
    ]

todo :: a
todo = todo

class HasScalars a where
  getScalars :: a -> Set Scalar

instance HasScalars LogicConstraints where
  getScalars = todo

instance HasScalars LookupArguments where
  getScalars = todo

instance HasScalars a => HasScalars (Circuit a) where
  getScalars x =
    mconcat
    [ getScalars (x ^. #gateConstraints),
      getScalars (x ^. #lookupArguments)
    ]
