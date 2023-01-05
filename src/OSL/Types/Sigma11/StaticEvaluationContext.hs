{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Sigma11.StaticEvaluationContext
  ( StaticBound (StaticBound),
    StaticEvaluationContextF (StaticEvaluationContext),
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Data.Map (Map)
import GHC.Generics (Generic)
import Stark.Types.Scalar (Scalar, one, zero)

newtype StaticBound = StaticBound {unStaticBound :: Maybe Scalar}
  deriving (Eq, Generic)

instance Group.C StaticBound where
  StaticBound x + StaticBound y =
    StaticBound ((Group.+) <$> x <*> y)
  negate (StaticBound x) =
    StaticBound (Group.negate <$> x)
  zero = StaticBound (Just zero)

instance Ring.C StaticBound where
  StaticBound x * StaticBound y =
    StaticBound ((Ring.*) <$> x <*> y)
  one = StaticBound (Just one)

instance Ord StaticBound where
  _ <= StaticBound Nothing = True
  StaticBound Nothing <= StaticBound (Just _) = False
  StaticBound (Just x) <= StaticBound (Just y) = x <= y

newtype StaticEvaluationContextF name = StaticEvaluationContext
  { unStaticEvaluationContext ::
      Map name StaticBound
  }
  deriving stock (Generic)
  deriving newtype (Semigroup, Monoid)
