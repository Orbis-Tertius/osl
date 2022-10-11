{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}

module Semicircuit.Gensyms
  ( deBruijnToGensyms,
  )
where

import Control.Lens ((^.))
import Control.Monad.State (State, evalState, get, put)
import Data.Functor ((<&>))
import Data.Map (Map)
import qualified Data.Map as Map
import OSL.Sigma11 (incrementDeBruijnIndices)
import OSL.Types.Arity (Arity (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import qualified OSL.Types.Sigma11 as DB
import qualified Semicircuit.Types.Sigma11 as GS

-- Rename the de Bruijn indices in the given formula
-- to gensyms.
deBruijnToGensyms :: DB.Formula -> GS.Formula
deBruijnToGensyms a =
  evalState (deBruijnToGensyms' a) (S 0 mempty)

newtype NextSym = NextSym Int
  deriving (Eq, Num)

data S = S NextSym (Map DB.Name GS.Name)

deBruijnToGensyms' ::
  DB.Formula ->
  State S GS.Formula
deBruijnToGensyms' =
  \case
    DB.Equal a b ->
      GS.Equal <$> term a <*> term b
    DB.LessOrEqual a b ->
      GS.LessOrEqual <$> term a <*> term b
    DB.Predicate p xs ->
      GS.Predicate p <$> mapM term xs
    DB.Not p -> GS.Not <$> rec p
    DB.And p q -> GS.And <$> rec p <*> rec q
    DB.Or p q -> GS.Or <$> rec p <*> rec q
    DB.Implies p q -> GS.Implies <$> rec p <*> rec q
    DB.Iff p q -> GS.Iff <$> rec p <*> rec q
    DB.ForAll b p -> do
      b' <- bound b
      pushIndices (Arity 0)
      x <- mapName (DB.Name (Arity 0) (DeBruijnIndex 0))
      r <- GS.ForAll x b' <$> rec p
      popIndices (Arity 0)
      pure r
    DB.ForSome (DB.Some n bs b) p -> do
      b' <-
        GS.OutputBound
          <$> bound (b ^. #unOutputBound)
      bs' <-
        mapM
          ( \b'' ->
              GS.InputBound
                <$> (GS.Name (Arity 0) <$> nextSym)
                <*> bound b''
          )
          (bs <&> (^. #unInputBound))
      let arity = Arity (length bs)
      pushIndices arity
      x <- mapName (DB.Name arity (DeBruijnIndex 0))
      r <- GS.ForSome (GS.Some x n bs' b') <$> rec p
      popIndices arity
      pure r
    DB.ForSome (DB.SomeP n b0 b1) p -> do
      b0' <-
        GS.InputBound
          <$> (GS.Name 0 <$> nextSym)
          <*> bound (b0 ^. #unInputBound)
      b1' <-
        GS.OutputBound
          <$> bound (b1 ^. #unOutputBound)
      pushIndices (Arity 1)
      x <- mapName (DB.Name (Arity 1) (DeBruijnIndex 0))
      r <- GS.ForSome
        (GS.SomeP x n b0' b1')
        <$> rec p
      popIndices (Arity 1)
      pure r
  where
    rec = deBruijnToGensyms'

bound :: DB.Bound -> State S GS.Bound
bound =
  \case
    DB.TermBound x -> GS.TermBound <$> term x
    DB.FieldMaxBound -> pure GS.FieldMaxBound

term :: DB.Term -> State S GS.Term
term =
  \case
    DB.App f xs ->
      GS.App <$> mapName f <*> mapM term xs
    DB.AppInverse f x ->
      GS.AppInverse <$> mapName f <*> term x
    DB.Add x y -> GS.Add <$> term x <*> term y
    DB.Mul x y -> GS.Mul <$> term x <*> term y
    DB.IndLess x y -> GS.IndLess <$> term x <*> term y
    DB.Const x -> pure (GS.Const x)

mapName :: DB.Name -> State S GS.Name
mapName x@(DB.Name arity _) = do
  S _ m <- get
  case Map.lookup x m of
    Just y -> pure y
    Nothing -> do
      sym <- nextSym
      S n _ <- get
      let y = GS.Name arity sym
      put (S n (Map.insert x y m))
      pure y

nextSym :: State S Int
nextSym = do
  S (NextSym sym) m <- get
  put (S (NextSym (sym + 1)) m)
  pure sym

pushIndices :: Arity -> State S ()
pushIndices arity = do
  S n m <- get
  put (S n (Map.mapKeys (incrementDeBruijnIndices arity 1) m))

popIndices :: Arity -> State S ()
popIndices arity = do
  S n m <- get
  put (S n (Map.mapKeys (incrementDeBruijnIndices arity (-1))
             (Map.delete (DB.Name arity 0) m)))
