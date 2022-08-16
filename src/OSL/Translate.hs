{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.Translate
  ( translate
  ) where


import qualified Data.Map as Map

import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.Translation (Translation (Formula, Term, Mapping))
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..))


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
        Just m -> return (Mapping m)
        Nothing -> Left (ErrorMessage ann "un-mapped name")
    OSL.Apply _ (OSL.Apply _ (OSL.AddN _) a) b ->
      Term <$> (S11.Add <$> translateTerm ctx a
                        <*> translateTerm ctx b)
    OSL.Apply _ (OSL.Apply _ (OSL.MulN _) a) b ->
      Term <$> (S11.Mul <$> translateTerm ctx a
                        <*> translateTerm ctx b)
    OSL.Apply _ (OSL.Apply _ (OSL.AddZ _) a) b ->
      Term <$> (S11.Add <$> translateTerm ctx a
                        <*> translateTerm ctx b)
    OSL.Apply _ (OSL.Apply _ (OSL.MulZ _) a) b ->
      Term <$> (S11.Mul <$> translateTerm ctx a
                        <*> translateTerm ctx b)
    OSL.ConstN _ x -> return (Term (S11.Const x))
    OSL.ConstZ _ x -> return (Term (S11.Const x))
    OSL.ConstFin _ x -> return (Term (S11.Const x))


translateTerm
  :: TranslationContext ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) S11.Term
translateTerm c t =
  case translate c t of
    Right (Term t') -> return t'
    Left err -> Left err

todo :: a
todo = todo
