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
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top), Term (Const, IndLess, Lookup, Max, Plus, Times, Var))
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArgument (LookupArgument)
import Halo2.Types.LookupArguments (LookupArguments (getLookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.PowerProduct (PowerProduct (getPowerProduct))
import Stark.Types.Scalar (Scalar)

class HasPolynomialVariables a where
  getPolynomialVariables :: a -> Set PolynomialVariable

instance HasPolynomialVariables PowerProduct where
  getPolynomialVariables = Map.keysSet . getPowerProduct

instance HasPolynomialVariables Polynomial where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . Map.keys . (^. #monos)

instance HasPolynomialVariables Term where
  getPolynomialVariables =
    \case
      Var x -> Set.singleton x
      Lookup is o ->
        mconcat (rec . (^. #getInputExpression) . fst <$> is)
          <> Set.singleton (PolynomialVariable (o ^. #unLookupTableOutputColumn . #unLookupTableColumn) 0)
      Const _ -> mempty
      Plus x y -> rec x <> rec y
      Times x y -> rec x <> rec y
      Max x y -> rec x <> rec y
      IndLess x y -> rec x <> rec y
    where
      rec = getPolynomialVariables

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

deriving newtype instance HasPolynomialVariables a => HasPolynomialVariables (InputExpression a)

instance HasPolynomialVariables a => HasPolynomialVariables (LookupArgument a) where
  getPolynomialVariables x =
    mconcat
      ( getPolynomialVariables (x ^. #gate) :
        (getPolynomialVariables . fst <$> (x ^. #tableMap))
      )

instance HasPolynomialVariables a => HasPolynomialVariables (LookupArguments a) where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . getLookupArguments

instance
  (HasPolynomialVariables a, HasPolynomialVariables b) =>
  HasPolynomialVariables (Circuit a b)
  where
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

instance HasScalars Term where
  getScalars =
    \case
      Var _ -> mempty
      Lookup is _ -> mconcat (getScalars . fst <$> is)
      Const x -> Set.singleton x
      Plus x y -> getScalars x <> getScalars y
      Times x y -> getScalars x <> getScalars y
      Max x y -> getScalars x <> getScalars y
      IndLess x y -> getScalars x <> getScalars y

instance HasScalars AtomicLogicConstraint where
  getScalars =
    \case
      Equals x y -> getScalars x <> getScalars y
      LessThan x y -> getScalars x <> getScalars y

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

deriving newtype instance HasScalars a => HasScalars (InputExpression a)

instance HasScalars a => HasScalars (LookupArgument a) where
  getScalars x =
    mconcat
      ( getScalars (x ^. #gate) :
        (getScalars . fst <$> (x ^. #tableMap))
      )

instance HasScalars a => HasScalars (LookupArguments a) where
  getScalars =
    mconcat . fmap getScalars . getLookupArguments

instance (HasScalars a, HasScalars b) => HasScalars (Circuit a b) where
  getScalars x =
    mconcat
      [ getScalars (x ^. #gateConstraints),
        getScalars (x ^. #lookupArguments)
      ]

getLookupTables :: Ord b => Circuit a b -> Set (b, [LookupTableColumn])
getLookupTables c =
  Set.fromList
    [ (a ^. #gate, snd <$> (a ^. #tableMap))
      | a <- c ^. #lookupArguments . #getLookupArguments
    ]
