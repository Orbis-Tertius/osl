{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}

module Halo2.Circuit
  ( HasPolynomialVariables (getPolynomialVariables),
    HasScalars (getScalars),
  ) where


import qualified Data.Map as Map
import Halo2.Prelude
import Halo2.Types.Circuit (Circuit)
import Halo2.Types.InputExpression (InputExpression (getInputExpression))
import Halo2.Types.LogicConstraint (LogicConstraint (Atom, Not, And, Or, Iff, Top, Bottom), AtomicLogicConstraint (Equals, LessThan))
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArgument (LookupArgument)
import Halo2.Types.LookupArguments (LookupArguments (getLookupArguments))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Halo2.Types.PowerProduct (PowerProduct (getPowerProduct))
import Stark.Types.Scalar (Scalar)


class HasPolynomialVariables a where
  getPolynomialVariables :: a -> Set PolynomialVariable

instance HasPolynomialVariables PowerProduct where
  getPolynomialVariables = Map.keysSet . getPowerProduct

instance HasPolynomialVariables Polynomial where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . Map.keys . (^. #monos)

instance HasPolynomialVariables AtomicLogicConstraint where
  getPolynomialVariables =
    \case
      Equals x y -> getPolynomialVariables x <> getPolynomialVariables y
      LessThan x y -> getPolynomialVariables x <> getPolynomialVariables y

instance HasPolynomialVariables LogicConstraint where
  getPolynomialVariables x =
    case x of
      Atom y -> getPolynomialVariables y
      Not y -> rec y
      And y z -> rec y <> rec z
      Or y z -> rec y <> rec z
      Iff y z -> rec y <> rec z
      Top -> mempty
      Bottom -> mempty
    where
      rec = getPolynomialVariables

instance HasPolynomialVariables LogicConstraints where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . (^. #constraints)

instance HasPolynomialVariables InputExpression where
  getPolynomialVariables = getPolynomialVariables . getInputExpression

instance HasPolynomialVariables LookupArgument where
  getPolynomialVariables x =
    mconcat 
    ( getPolynomialVariables (x ^. #gate)
      : (getPolynomialVariables . fst <$> (x ^. #tableMap)) )

instance HasPolynomialVariables LookupArguments where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . getLookupArguments

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
