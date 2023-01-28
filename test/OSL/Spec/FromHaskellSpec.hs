{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}

module OSL.Spec.FromHaskellSpec (spec) where

import Data.Fixed (Fixed, Pico)
import Data.Proxy (Proxy (Proxy))
import Data.Time (Day, TimeOfDay, LocalTime)
import GHC.Generics (Generic)
import OSL.FromHaskell (ToOSLType (toOSLType))
import qualified OSL.Types.OSL as OSL
import Test.Syd (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "FromHaskell" $ do
    unitType
    unitProductType
    unitSumType
    integerType
    fixedType
    dayType
    picoType
    record2Type
    record3Type
    record4Type
    timeOfDayType
    localTimeType

unitType :: Spec
unitType =
  it "() -> Fin(1)" $
    toOSLType (Proxy @()) mempty
      `shouldBe` OSL.Fin () 1

unitProductType :: Spec
unitProductType =
  it "((), ()) -> Fin(1) * Fin(1)" $
    toOSLType (Proxy @((), ())) mempty
      `shouldBe` OSL.Product () (OSL.Fin () 1) (OSL.Fin () 1)

unitSumType :: Spec
unitSumType =
  it "Either () () -> Fin(1) + Fin(1)" $
    toOSLType (Proxy @(Either () ())) mempty
      `shouldBe` OSL.Coproduct () (OSL.Fin () 1) (OSL.Fin () 1)

integerType :: Spec
integerType =
  it "Integer -> Z" $
    toOSLType (Proxy @Integer) mempty
      `shouldBe` OSL.Z ()

fixedType :: Spec
fixedType =
  it "Fixed 4 -> Fin(4)" $
    toOSLType (Proxy @(Fixed 4)) mempty
      `shouldBe` OSL.Fin () 4

dayType :: Spec
dayType =
  it "Day -> Z" $
    toOSLType (Proxy @Day) mempty
      `shouldBe` OSL.N ()

picoType :: Spec
picoType =
  it "Pico -> Fin(1)" $
    toOSLType (Proxy @Pico) mempty
      `shouldBe` OSL.Fin () 1000000000000

data Record2 = Record2 Int Int
  deriving Generic

record2Type :: Spec
record2Type =
  it "Record2 -> Z * Z" $
    toOSLType (Proxy @Record2) mempty
      `shouldBe` OSL.Product () (OSL.Z ()) (OSL.Z ())

data Record3 = Record3 Int Int Int
  deriving Generic

record3Type :: Spec
record3Type =
  it "Record3 -> Z * Z * Z" $
    toOSLType (Proxy @Record3) mempty
      `shouldBe` OSL.Product () (OSL.Z ()) (OSL.Product () (OSL.Z ()) (OSL.Z ()))

data Record4 = Record4 Int Int Int Int
  deriving Generic

record4Type :: Spec
record4Type =
  it "Record4 -> Z * Z * Z * Z" $
    toOSLType (Proxy @Record4) mempty
      `shouldBe` OSL.Product () (OSL.Z ()) (OSL.Product () (OSL.Z ()) (OSL.Product () (OSL.Z ()) (OSL.Z ())))

timeOfDayType :: Spec
timeOfDayType =
  it "TimeOfDay -> _" $
    toOSLType (Proxy @TimeOfDay) mempty
      `shouldBe` OSL.Product () (OSL.Z ()) (OSL.Product () (OSL.Z ()) (OSL.Fin () 1000000000000))

localTimeType :: Spec
localTimeType =
  it "LocalTime -> _" $
    toOSLType (Proxy @LocalTime) mempty
      `shouldBe`
        OSL.Product () (OSL.N ())
          (OSL.Product () (OSL.Z ())
            (OSL.Product () (OSL.Z ())
              (OSL.Fin () 1000000000000)))
