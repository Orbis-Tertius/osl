{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StandaloneDeriving #-}

module Halo2.Circuit
  ( HasPolynomialVariables (getPolynomialVariables),
    HasScalars (getScalars),
    getLookupTables,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Halo2.Prelude
import Halo2.Types.Circuit (Circuit)
import Halo2.Types.Coefficient (Coefficient (getCoefficient))
import Halo2.Types.InputExpression (InputExpression (..))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan, EqualsMax), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top))
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArgument (LookupArgument)
import Halo2.Types.LookupArguments (LookupArguments (getLookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn)
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
      EqualsMax x y z -> getPolynomialVariables x <> getPolynomialVariables y <> getPolynomialVariables z

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

deriving newtype instance HasPolynomialVariables InputExpression

instance HasPolynomialVariables LookupArgument where
  getPolynomialVariables x =
    mconcat
      ( getPolynomialVariables (x ^. #gate) :
        (getPolynomialVariables . fst <$> (x ^. #tableMap))
      )

instance HasPolynomialVariables LookupArguments where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . getLookupArguments

instance HasPolynomialVariables a => HasPolynomialVariables (Circuit a) where
  getPolynomialVariables x =
    mconcat
      [ getPolynomialVariables (x ^. #gateConstraints),
        getPolynomialVariables (x ^. #lookupArguments)
      ]

class HasScalars a where
  getScalars :: a -> Set Scalar

instance HasScalars Polynomial where
  getScalars =
    Set.fromList . fmap getCoefficient
      . Map.elems
      . (^. #monos)

instance HasScalars AtomicLogicConstraint where
  getScalars =
    \case
      Equals x y -> getScalars x <> getScalars y
      LessThan x y -> getScalars x <> getScalars y
      EqualsMax x y z -> getScalars x <> getScalars y <> getScalars z

instance HasScalars LogicConstraint where
  getScalars x =
    case x of
      Atom y -> getScalars y
      Not y -> rec y
      And y z -> rec y <> rec z
      Or y z -> rec y <> rec z
      Iff y z -> rec y <> rec z
      Top -> Set.singleton 1
      Bottom -> Set.singleton 0
    where
      rec = getScalars

instance HasScalars LogicConstraints where
  getScalars =
    mconcat . fmap getScalars . (^. #constraints)

deriving newtype instance HasScalars InputExpression

instance HasScalars LookupArgument where
  getScalars x =
    mconcat
      ( getScalars (x ^. #gate) :
        (getScalars . fst <$> (x ^. #tableMap))
      )

instance HasScalars LookupArguments where
  getScalars =
    mconcat . fmap getScalars . getLookupArguments

instance HasScalars a => HasScalars (Circuit a) where
  getScalars x =
    mconcat
      [ getScalars (x ^. #gateConstraints),
        getScalars (x ^. #lookupArguments)
      ]

getLookupTables :: Circuit a -> Set (Polynomial, [LookupTableColumn])
getLookupTables c =
  Set.fromList
    [ (a ^. #gate, snd <$> (a ^. #tableMap))
      | a <- c ^. #lookupArguments . #getLookupArguments
    ]
