module OSL.Debug (showTrace) where

import Debug.Trace (trace)

showTrace :: Show a => String -> a -> a
showTrace s x = trace (s <> show x) x
