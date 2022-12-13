module OSL.Spec.SimplifyTypeSpec (spec) where

import Test.Syd (Spec, describe)

spec :: Spec
spec =
  describe "OSL.SimplifyType" $
    complexifyRoundTripSpec

complexifyRoundTripSpec :: Spec
complexifyRoundTripSpec = do
  pure () -- TODO
