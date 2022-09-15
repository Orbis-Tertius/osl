{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}


module OSL.Spec.OSLSpec (spec) where


import Control.Monad (forM_)
import Data.String (IsString)
import OSL.EntryPoint (runMain)
import Test.Syd (Spec, describe, it, shouldBe, liftIO)
import Text.RawString.QQ (r)


spec :: Spec
spec =
  describe "OSL" $
    forM_ testCases runTestCase


data TestCase = TestCase TestFile TestName Expectation


newtype TestFile = TestFile String
  deriving IsString


newtype TestName = TestName String
  deriving IsString


newtype Expectation = Expectation String
  deriving IsString


runTestCase :: TestCase -> Spec
runTestCase (TestCase (TestFile fileName) (TestName testName) (Expectation expected)) =
  it ("produces the expected result on " <> fileName
        <> " " <> testName) $ do
    result <- liftIO $ runMain ("examples/" <> fileName <> ".osl") testName
    result `shouldBe` expected


testCases :: [TestCase]
testCases =
  [ TestCase "false" "false"
    [r|Translated OSL:
(0 = 1)|]
  , TestCase "positive" "isPositive"
    [r|Translated OSL:
(1 <= 0^0)|]
  ]
