module OSL.Die (die) where


import Data.Text (unpack)
import qualified System.Exit as Exit
import System.IO.Unsafe (unsafePerformIO)


die :: Text -> a
die = unsafePerformIO . Exit.die . unpack
