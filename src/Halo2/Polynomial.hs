{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Polynomial (plus, times) where


import qualified Data.Map as Map

import Halo2.Prelude
import qualified Halo2.Coefficient as C
import qualified Halo2.PowerProduct as P
import Halo2.Types.Coefficient (Coefficient)
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.Polynomial (Polynomial (..))
import Halo2.Types.PowerProduct (PowerProduct)


plus :: FiniteField -> Polynomial -> Polynomial -> Polynomial
plus f (Polynomial p) (Polynomial q) =
  Polynomial $ Map.unionWith (C.plus f) p q


times :: FiniteField -> Polynomial -> Polynomial -> Polynomial
times f (Polynomial p) (Polynomial q) =
  Polynomial . sumMonomials f
    $ [ ( P.times x y, C.times f a b )
      | (x,a) <- Map.toList p
      , (y,b) <- Map.toList q ]


sumMonomials :: FiniteField
  -> [(PowerProduct, Coefficient)]
  -> Map PowerProduct Coefficient
sumMonomials f = foldl g mempty
  where
    g :: Map PowerProduct Coefficient
      -> (PowerProduct, Coefficient)
      -> Map PowerProduct Coefficient
    g p (x, a) =
      case Map.lookup x p of
        Just b -> Map.insert x (C.plus f a b) p
        Nothing -> Map.insert x a p
