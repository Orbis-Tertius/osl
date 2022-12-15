{-# LANGUAGE OverloadedStrings #-}

module OSL.Spec.SimplifyTypeSpec (spec) where

import qualified Data.Map as Map
import OSL.Evaluation (checkValueIsInType)
import OSL.SimplifyType (simplifyType, simplifyValue, complexifyValue)
import OSL.Spec.Gen (genType, genValueOfType)
import OSL.Types.OSL (Declaration (Data), ValidContext (ValidContext), Type (N))
import OSL.Types.Value (Value (Fin'))
import Test.Syd (Spec, describe, shouldBe, expectationFailure, it)
import Test.Syd.Modify (modifyMaxSize)
import Test.QuickCheck (forAll)

spec :: Spec
spec =
  describe "OSL.SimplifyType"
    . modifyMaxSize (const 13) $
    do simplifyValueTypeSpec
       complexifyRoundTripSpec

exampleContext :: ValidContext t ()
exampleContext =
  ValidContext $
    Map.singleton "Foo" (Data (N ()))

simplifyValueTypeSpec :: Spec
simplifyValueTypeSpec =
  it "creates a value of the simplified type" $
    forAll (genType (pure ()) (pure "Foo")) $ \a ->
      forAll (genValueOfType exampleContext a) $ \x ->
        case simplifyType a of
          Nothing -> simplifyValue a x `shouldBe` Right (Fin' 0)
          Just a' ->
            case simplifyValue a x of
              Right x' ->
                checkValueIsInType exampleContext a' x'
                  `shouldBe` Right ()
              Left err -> expectationFailure (show err)

complexifyRoundTripSpec :: Spec
complexifyRoundTripSpec =
  it "round trips" $
    forAll (genType (pure ()) (pure "Foo")) $ \a ->
      forAll (genValueOfType exampleContext a) $ \x ->
         case simplifyValue a x of
           Right x' -> do
             case complexifyValue exampleContext a x' of
               Right x'' -> x'' `shouldBe` x
               Left err -> expectationFailure ("complexifyValue: " <> show err)
           Left err -> expectationFailure ("simplifyValue: " <> show err)
