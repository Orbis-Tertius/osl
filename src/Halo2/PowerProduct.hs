{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.PowerProduct
  ( times
  , degree
  ) where


import qualified Data.Map as Map

import Halo2.Prelude
import Halo2.Types.Exponent (Exponent (..))
import Halo2.Types.PowerProduct (PowerProduct (..))


times :: PowerProduct -> PowerProduct -> PowerProduct
times (PowerProduct a) (PowerProduct b) =
  PowerProduct (Map.unionWith (+) a b)


degree :: PowerProduct -> Int
degree (PowerProduct m) =
  product (getExponent <$> Map.elems m)
