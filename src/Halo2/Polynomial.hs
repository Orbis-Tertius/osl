{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Polynomial
  ( plus,
    times,
    constant,
    var,
    var',
    multilinearMonomial,
    zero,
    one,
    negative,
    minus,
    sum,
    degree,
  )
where

import Data.List (foldl')
import qualified Data.Map as Map
import qualified Halo2.Coefficient as C
import qualified Halo2.FiniteField as F
import qualified Halo2.PowerProduct as P
import Halo2.Prelude
import Halo2.Types.Coefficient (Coefficient (..))
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.FieldElement (FieldElement)
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.Polynomial (Polynomial (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.PowerProduct (PowerProduct (..))

plus :: FiniteField -> Polynomial -> Polynomial -> Polynomial
plus f (Polynomial p) (Polynomial q) =
  Polynomial $ Map.unionWith (C.plus f) p q

times :: FiniteField -> Polynomial -> Polynomial -> Polynomial
times f (Polynomial p) (Polynomial q) =
  Polynomial . sumMonomials f $
    [ (P.times x y, C.times f a b)
      | (x, a) <- Map.toList p,
        (y, b) <- Map.toList q
    ]

sumMonomials ::
  FiniteField ->
  [(PowerProduct, Coefficient)] ->
  Map PowerProduct Coefficient
sumMonomials f = foldl' g mempty
  where
    g ::
      Map PowerProduct Coefficient ->
      (PowerProduct, Coefficient) ->
      Map PowerProduct Coefficient
    g p (x, a) =
      case Map.lookup x p of
        Just b -> Map.insert x (C.plus f a b) p
        Nothing -> Map.insert x a p

constant :: FieldElement -> Polynomial
constant = Polynomial . Map.singleton (PowerProduct mempty) . Coefficient

var :: PolynomialVariable -> Polynomial
var v =
  Polynomial
    (Map.singleton (PowerProduct (Map.singleton v 1)) C.one)

var' :: ColumnIndex -> Polynomial
var' i = var (PolynomialVariable i 0)

multilinearMonomial ::
  Coefficient ->
  [PolynomialVariable] ->
  Polynomial
multilinearMonomial a xs =
  Polynomial
    ( Map.singleton
        ( PowerProduct
            ( Map.fromList
                ((,1) <$> xs)
            )
        )
        a
    )

zero :: Polynomial
zero = constant F.zero

one :: Polynomial
one = constant F.one

minusOne :: FiniteField -> Polynomial
minusOne f = constant (F.minusOne f)

negative :: FiniteField -> Polynomial -> Polynomial
negative f = times f (minusOne f)

minus :: FiniteField -> Polynomial -> Polynomial -> Polynomial
minus f a b = plus f a (negative f b)

sum :: FiniteField -> [Polynomial] -> Polynomial
sum f = foldl' (plus f) zero

degree :: Polynomial -> Int
degree (Polynomial p) =
  foldl' max 0 (P.degree <$> Map.keys p)
