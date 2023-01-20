module Stark.Spec.ScalarSpec (spec) where

import qualified Algebra.Additive as Group
import OSL.Spec.Gen (genScalar)
import Stark.Types.Scalar (zero)
import Test.Syd (Spec, describe, it, shouldBe)
import Test.QuickCheck (forAll)

spec :: Spec
spec =
  describe "Stark" $
    groupLaws

groupLaws :: Spec
groupLaws =
  describe "Group laws" $ do
    associativity
    commutativity
    leftCancellation
    rightCancellation
    inverseCancellation
  where
    associativity =
      it "is associative" $
        forAll ((,,) <$> genScalar <*> genScalar <*> genScalar) $ \(x,y,z) ->
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
