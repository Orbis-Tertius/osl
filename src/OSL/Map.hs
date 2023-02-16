{-# LANGUAGE TupleSections #-}

module OSL.Map (mapKeysMaybe, inverseMap, curryMap, uncurryMap) where

import Data.Map (Map, fromList, singleton, toList, unionsWith)
import Data.Maybe (catMaybes)
import Data.Tuple (swap)

mapKeysMaybe :: Ord k' => (k -> Maybe k') -> Map k a -> Map k' a
mapKeysMaybe f m =
  fromList . catMaybes $
    [(,v) <$> f k | (k, v) <- toList m]

inverseMap :: Ord b => Map a b -> Map b a
inverseMap = fromList . fmap swap . toList

uncurryMap :: (Ord a, Ord b) => Map a (Map b c) -> Map (a, b) c
uncurryMap m =
  fromList
    [ ((a, b), c)
      | (a, m') <- toList m,
        (b, c) <- toList m'
    ]

curryMap :: (Ord a, Ord b) => Map (a, b) c -> Map a (Map b c)
curryMap m =
  unionsWith (<>) $
    [ singleton a (singleton b c)
      | ((a, b), c) <- toList m
    ]
