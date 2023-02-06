{-# LANGUAGE OverloadedStrings #-}

module Stark.Spec.ScalarSpec (spec) where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Data.Maybe (fromMaybe)
import Die (die)
import OSL.Spec.Gen (genScalar)
import Stark.Types.Scalar (inverseScalar, integerToScalar, one, zero)
import Test.QuickCheck (forAll)
import Test.Syd (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Stark.Types.Scalar" $ do
    abelianGroupLaws
    fieldLaws

abelianGroupLaws :: Spec
abelianGroupLaws =
  describe "Abelian group addition" $ do
    associativity
    commutativity
    leftCancellation
    rightCancellation
    inverseCancellation
    describe "subtraction" $ do
      subtractCancellationProp
      subtractCancellationConst
  where
    associativity =
      it "is associative" $
        forAll ((,,) <$> genScalar <*> genScalar <*> genScalar) $ \(x, y, z) ->
          (x Group.+ y) Group.+ z `shouldBe` x Group.+ (y Group.+ z)

    commutativity =
      it "is commutative" $
        forAll ((,) <$> genScalar <*> genScalar) $ \(x, y) ->
          (x Group.+ y) `shouldBe` y Group.+ x

    leftCancellation =
      it "has a left identity" $
        forAll genScalar $ \x ->
          (zero Group.+ x) `shouldBe` x

    rightCancellation =
      it "has a right identity" $
        forAll genScalar $ \x ->
          (x Group.+ zero) `shouldBe` x

    inverseCancellation =
      it "has inverses" $
        forAll genScalar $ \x -> do
          (Group.negate x Group.+ x) `shouldBe` zero
          (x Group.+ Group.negate x) `shouldBe` zero

    subtractCancellationConst =
      it "cancels" $ do
        let f x = fromMaybe (die "subtractCancellationConst: x out of range of scalar field")
                    (integerToScalar x)
        (f 9 Group.- f 9) `shouldBe` zero
        (f 8 Group.- f 8) `shouldBe` zero

    subtractCancellationProp =
      it "cancels" $ do
        forAll genScalar $ \x ->
          (x Group.- x) `shouldBe` zero

fieldLaws :: Spec
fieldLaws =
  describe "Field multiplication" $ do
    associativity
    commutativity
    leftCancellation
    rightCancellation
    inverseCancellation
    leftDistributivity
    rightDistributivity
  where
    associativity =
      it "is associative" $
        forAll ((,,) <$> genScalar <*> genScalar <*> genScalar) $ \(x, y, z) ->
          (x Ring.* y) Ring.* z `shouldBe` x Ring.* (y Ring.* z)

    commutativity =
      it "is commutative" $
        forAll ((,) <$> genScalar <*> genScalar) $ \(x, y) ->
          (x Ring.* y) `shouldBe` (y Ring.* x)

    leftCancellation =
      it "has a left identity" $
        forAll genScalar $ \x ->
          (one Ring.* x) `shouldBe` x

    rightCancellation =
      it "has a right identity" $
        forAll genScalar $ \x ->
          (x Ring.* one) `shouldBe` x

    inverseCancellation =
      it "has inverses" $
        forAll genScalar $ \x -> do
          case inverseScalar x of
            Nothing -> x `shouldBe` zero
            Just x' -> do
              x Ring.* x' `shouldBe` one
              x' Ring.* x `shouldBe` one

    leftDistributivity =
      it "is left distributive over addition" $
        forAll ((,,) <$> genScalar <*> genScalar <*> genScalar) $ \(x, y, z) ->
          (x Ring.* (y Group.+ z)) `shouldBe` ((x Ring.* y) Group.+ (x Ring.* z))

    -- Left distributivity and commutativity together imply right distributivity.
    -- However, we are only doing empirical testing here, and it doesn't
    -- follow from the fact that tests of A pass and tests of B pass and (A&B)->C
    -- that tests of C will pass.
    rightDistributivity =
      it "is right distributive over addition" $
        forAll ((,,) <$> genScalar <*> genScalar <*> genScalar) $ \(x, y, z) ->
          ((x Group.+ y) Ring.* z) `shouldBe` ((x Ring.* z) Group.+ (y Ring.* z))
