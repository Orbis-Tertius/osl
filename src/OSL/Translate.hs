{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.Translate
  ( translate
  ) where


import qualified Data.Map as Map

import OSL.Term (termAnnotation)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.Translation (Translation (Formula, Term, Mapping))
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..), LeftMapping (..), RightMapping (..))


-- Provides a translation for the given term in
-- the given context.
translate
  :: TranslationContext ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) Translation
translate ctx@(TranslationContext _ mappings) =
  \case
    OSL.NamedTerm ann name ->
      case Map.lookup name mappings of
        Just (ScalarMapping n) -> return (Term (S11.Var n))
        Just m -> return (Mapping (S11.Var <$> m))
        Nothing -> Left (ErrorMessage ann "un-mapped name")
    OSL.Apply _ (OSL.Apply _ (OSL.AddN _) a) b ->
      Term <$> (S11.Add <$> translateToTerm ctx a
                        <*> translateToTerm ctx b)
    OSL.Apply _ (OSL.Apply _ (OSL.MulN _) a) b ->
      Term <$> (S11.Mul <$> translateToTerm ctx a
                        <*> translateToTerm ctx b)
    OSL.Apply _ (OSL.Apply _ (OSL.AddZ _) a) b ->
      Term <$> (S11.Add <$> translateToTerm ctx a
                        <*> translateToTerm ctx b)
    OSL.Apply _ (OSL.Apply _ (OSL.MulZ _) a) b ->
      Term <$> (S11.Mul <$> translateToTerm ctx a
                        <*> translateToTerm ctx b)
    OSL.ConstN _ x -> return (Term (S11.Const x))
    OSL.ConstZ _ x -> return (Term (S11.Const x))
    OSL.ConstFin _ x -> return (Term (S11.Const x))
    OSL.Apply _ (OSL.Apply _ (OSL.Pair _) a) b ->
      Mapping <$>
        (ProductMapping
          <$> (LeftMapping <$> translateToMapping ctx a)
          <*> (RightMapping <$> translateToMapping ctx b))

translateToMapping
  :: TranslationContext ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) (Mapping S11.Term)
translateToMapping c t =
  case translate c t of
    Right (Mapping m) -> return m
    Right (Term t') -> return (ScalarMapping t')
    

translateToTerm
  :: TranslationContext ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) S11.Term
translateToTerm c t =
  case translate c t of
    Right (Term t') -> return t'
    Right _ -> Left (ErrorMessage (termAnnotation t)
                 "expected a term denoting a scalar")
    Left err -> Left err


todo :: a
todo = todo
