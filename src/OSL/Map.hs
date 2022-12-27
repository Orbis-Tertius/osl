{-# LANGUAGE TupleSections #-}

module OSL.Map (mapKeysMaybe) where

import Data.Map (Map, fromList, toList)
import Data.Maybe (catMaybes)

mapKeysMaybe :: Ord k' => (k -> Maybe k') -> Map k a -> Map k' a
mapKeysMaybe f m =
  fromList . catMaybes $
    [(,v) <$> f k | (k, v) <- toList m]
