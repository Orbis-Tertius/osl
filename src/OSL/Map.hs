{-# LANGUAGE TupleSections #-}

module OSL.Map (mapKeysMaybe, inverseMap) where

import Data.Map (Map, fromList, toList)
import Data.Maybe (catMaybes)
import Data.Tuple (swap)

mapKeysMaybe :: Ord k' => (k -> Maybe k') -> Map k a -> Map k' a
mapKeysMaybe f m =
  fromList . catMaybes $
    [(,v) <$> f k | (k, v) <- toList m]

inverseMap :: Ord b => Map a b -> Map b a
inverseMap = fromList . fmap swap . toList
