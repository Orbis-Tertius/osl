{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Spec.Gen
  ( genType,
    genValueOfType,
  )
where

import Cast (integerToInt)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Die (die)
import OSL.Types.OSL
  ( Cardinality (Cardinality),
    ContextType (Global),
    Declaration (Data),
    Name,
    Type (Coproduct, F, Fin, Fp, List, Map, Maybe, N, NamedType, P, Product, Prop, Z),
    ValidContext (ValidContext),
  )
import OSL.Types.Value (Value (Bool, Fin', Fp', Fun, Int, Iota1', Iota2', List'', Map'', Maybe'', Nat, Pair', To'))
import qualified Stark.Types.Scalar as Scalar
import Test.QuickCheck (Gen, arbitrary, choose, listOf, oneof, shuffle)

genType :: Gen ann -> Gen Name -> Gen (Type ann)
genType ann name =
  oneof
    [ Prop <$> ann,
      F <$> ann <*> genMaybe genCardinality
        <*> rec
        <*> rec,
      do
        a <- rec
        P <$> ann <*> genMaybe genCardinality
          <*> pure a
          <*> pure a,
      N <$> ann,
      Z <$> ann,
      Fp <$> ann,
      Fin <$> ann <*> choose (0, 1000),
      Product <$> ann <*> rec <*> rec,
      Coproduct <$> ann <*> rec <*> rec,
      NamedType <$> ann <*> name,
      Maybe <$> ann <*> rec,
      List <$> ann <*> genCardinality <*> rec,
      Map <$> ann <*> genCardinality <*> rec <*> rec
    ]
  where
    rec = genType ann name

genMaybe :: Gen a -> Gen (Maybe a)
genMaybe g =
  oneof
    [ pure Nothing,
      Just <$> g
    ]

genCardinality :: Gen Cardinality
genCardinality =
  Cardinality <$> choose (0, 10)

genValueOfType :: ValidContext 'Global ann -> Type ann -> Gen Value
genValueOfType (ValidContext c) =
  \case
    Prop _ -> Bool <$> oneof [pure True, pure False]
    F _ (Just (Cardinality n)) a b ->
      let n' = fromMaybe 1000 $ integerToInt n
       in Fun . Map.fromList . take n'
            <$> listOf ((,) <$> rec a <*> rec b)
    F _ Nothing a b ->
      Fun . Map.fromList
        <$> listOf ((,) <$> rec a <*> rec b)
    P _ (Just (Cardinality n)) a _b -> do
      let n' = fromMaybe 1000 $ integerToInt n
      vs <-
        Set.toList . Set.fromList . take n'
          <$> listOf (rec a)
      vs' <- shuffle vs
      pure (Fun (Map.fromList (zip vs vs')))
    P _ Nothing a _b -> do
      vs <- Set.toList . Set.fromList <$> listOf (rec a)
      vs' <- shuffle vs
      pure (Fun (Map.fromList (zip vs vs')))
    N _ -> Nat <$> genScalar
    Z _ -> Int <$> genScalar
    Fp _ -> Fp' <$> genScalar
    Fin _ n -> do
      x <- choose (0, n - 1)
      case Scalar.integerToScalar x of
        Just x' -> pure (Fin' x')
        Nothing -> die "genValueOfType: Fin out of range of scalar"
    Product _ a b ->
      Pair' <$> rec a <*> rec b
    Coproduct _ a b ->
      oneof
        [ Iota1' <$> rec a,
          Iota2' <$> rec b
        ]
    NamedType _ name ->
      case Map.lookup name c of
        Just (Data a) ->
          To' name <$> rec a
        _ -> die "genValueOfType: name lookup failed"
    Maybe _ a ->
      Maybe'' <$> genMaybe (rec a)
    List _ (Cardinality n) a ->
      List'' . take (fromMaybe 1000 (integerToInt n))
        <$> listOf (rec a)
    Map _ (Cardinality n) a b ->
      Map'' . Map.fromList . take (fromMaybe 1000 (integerToInt n))
        <$> listOf ((,) <$> rec a <*> rec b)
  where
    rec = genValueOfType (ValidContext c)

genScalar :: Gen Scalar.Scalar
genScalar = do
  r <- Scalar.fromWord64 <$> arbitrary
  case r of
    Just r' -> pure r'
    Nothing -> genScalar
