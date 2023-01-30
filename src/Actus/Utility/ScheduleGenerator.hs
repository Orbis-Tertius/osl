{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Actus.Utility.ScheduleGenerator
  ( generateRecurrentSchedule,
    inf,
    sup,
    (<+>),
    (<->),
  )
where

import Actus.Domain (Cycle (..), ScheduleConfig (..), ShiftedSchedule, Stub (..), mkShiftedDay)
import Actus.Utility.DateShift (applyBDC, applyEOMC, shiftDate)
import qualified Data.List as L (delete, init, last, length)
import Data.Maybe (fromMaybe)
import Data.Time (LocalTime (..))
import Die (die)
import Safe (atMay)

{-# ANN maximumMaybe ("HLint: ignore No maximum" :: String) #-}
maximumMaybe :: Ord a => [a] -> Maybe a
maximumMaybe [] = Nothing
maximumMaybe xs = Just $ maximum xs

{-# ANN minimumMaybe ("HLint: ignore No minimum" :: String) #-}
minimumMaybe :: Ord a => [a] -> Maybe a
minimumMaybe [] = Nothing
minimumMaybe xs = Just $ minimum xs

inf :: (Ord a) => [a] -> a -> Maybe a
inf set threshold =
  minimumMaybe [t | t <- set, t > threshold]

sup :: (Ord a) => [a] -> a -> Maybe a
sup set threshold =
  maximumMaybe [t | t <- set, t < threshold]

correction :: Cycle -> LocalTime -> LocalTime -> [LocalTime] -> [LocalTime]
correction
  Cycle
    { stub = ShortStub,
      includeEndDay = False
    }
  anchorDate
  endDate
  schedule
    | endDate == anchorDate =
      L.delete anchorDate $ L.init schedule
correction
  Cycle
    { stub = ShortStub
    }
  _
  _
  schedule = L.init schedule
correction
  Cycle
    { stub = LongStub,
      includeEndDay = True
    }
  _
  endDate
  schedule
    | endDate /= L.last schedule =
      let s = L.init schedule
          l = L.length s
       in if l > 2
            then L.delete (fromMaybe (die msg) (s `atMay` (l - 1))) s
            else s
    where
      msg = "Actus.Utility.ScheduleGenerator.correction: something impossible happened"
correction
  Cycle
    { stub = LongStub,
      includeEndDay = True
    }
  _
  _
  schedule = L.init schedule
correction
  Cycle
    { stub = LongStub,
      includeEndDay = False
    }
  anchorDate
  endDate
  schedule
    | endDate == anchorDate
        && endDate /= L.last schedule =
      let s = L.delete anchorDate $ L.init schedule
          l = L.length s
       in if l > 2
            then L.delete (fromMaybe (die msg) (s `atMay` (l - 1))) s
            else s
    where
      msg = "Actus.Utility.ScheduleGenerator.correction: something impossible happened"
correction
  Cycle
    { stub = LongStub,
      includeEndDay = False
    }
  anchorDate
  endDate
  schedule
    | endDate == anchorDate =
      let s = L.delete anchorDate $ L.init schedule
          l = L.length s
       in if l > 2
            then L.delete (fromMaybe (die msg) (s `atMay` (l - 1))) s
            else s
    where
      msg = "Actus.Utility.ScheduleGenerator.correction: something impossible happened"
correction
  Cycle
    { stub = LongStub,
      includeEndDay = False
    }
  _
  endDate
  schedule
    | endDate /= L.last schedule =
      let s = L.init schedule
          l = L.length s
       in if l > 2
            then L.delete (fromMaybe (die msg) (s `atMay` (l - 1))) s
            else s
    where
      msg = "Actus.Utility.ScheduleGenerator.correction: something impossible happened"
correction
  Cycle
    { stub = LongStub,
      includeEndDay = False
    }
  _
  _
  schedule = L.init schedule

addEndDay :: Bool -> LocalTime -> ShiftedSchedule -> ShiftedSchedule
addEndDay True endDate schedule = schedule ++ [mkShiftedDay endDate]
addEndDay _ _ schedule = schedule

generateRecurrentSchedule' :: Cycle -> LocalTime -> LocalTime -> [LocalTime]
generateRecurrentSchedule' Cycle {..} anchorDate endDate =
  let go :: LocalTime -> Integer -> [LocalTime] -> [LocalTime]
      go current k acc =
        if current >= endDate || n == 0
          then acc ++ [current]
          else
            let current' = shiftDate anchorDate (k * n) p
             in go current' (k + 1) (acc ++ [current])
   in go anchorDate 1 []

generateRecurrentSchedule ::
  -- | Anchor date
  LocalTime ->
  -- | Cycle
  Cycle ->
  -- | End date
  LocalTime ->
  -- | Schedule config
  ScheduleConfig ->
  -- | New schedule
  ShiftedSchedule
generateRecurrentSchedule
  a
  c
  e
  ScheduleConfig
    { endOfMonthConvention = Just eomc,
      calendar = Just cal,
      businessDayConvention = Just bdc
    } =
    addEndDay (includeEndDay c) e
      . fmap (applyBDC bdc cal . applyEOMC a c eomc)
      . correction c a e
      $ generateRecurrentSchedule' c a e
generateRecurrentSchedule _ _ _ _ = []

(<+>) :: LocalTime -> Cycle -> LocalTime
(<+>) d c = shiftDate d (n c) (p c)

(<->) :: LocalTime -> Cycle -> LocalTime
(<->) d c = shiftDate d (-n c) (p c)
