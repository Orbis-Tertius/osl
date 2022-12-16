{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Sigma11.Value
  ( Value (Value)
  ) where

import GHC.Generics (Generic)
import Data.Map (Map)
import Stark.Types.Scalar (Scalar)

-- All Sigma11 variable values are of this form.
-- Notable special cases:
--  * A scalar variable has one key, which is []
--  * A predicate variable's values are
--    arbitrary (can be zero); only the keys
--    matter, and they represent the set of
--    satisfying inputs
newtype Value =
  Value { unValue :: Map [Scalar] Scalar }
  deriving (Generic, Semigroup, Monoid)
