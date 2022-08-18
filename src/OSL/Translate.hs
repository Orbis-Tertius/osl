{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.Translate
  ( translate
  ) where


import qualified Data.Map as Map
import Data.Text (pack)

import OSL.Term (termAnnotation)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.Translation (Translation (Formula, Term, Mapping))
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..), LeftMapping (..), RightMapping (..), ChoiceMapping (..), ValuesMapping (..))
import OSL.ValidContext (getDeclaration)
import OSL.ValidateContext (inferType)


-- Provides a translation for the given term in
-- the given context.
translate
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) Translation
translate ctx@(TranslationContext
          decls@(OSL.ValidContext declsMap) mappings)
          termType =
  \case
    OSL.NamedTerm ann name ->
      case Map.lookup name mappings of
        Just (ScalarMapping x) -> return (Term x)
        Just m -> return (Mapping m)
        Nothing -> Left (ErrorMessage ann "un-mapped name")
    OSL.Apply ann (OSL.Apply _ (OSL.AddN _) a) b ->
      Term <$> (S11.Add <$> translateToTerm ctx (OSL.N ann) a
                        <*> translateToTerm ctx (OSL.N ann) b)
    OSL.Apply ann (OSL.Apply _ (OSL.MulN _) a) b ->
      Term <$> (S11.Mul <$> translateToTerm ctx (OSL.N ann) a
                        <*> translateToTerm ctx (OSL.N ann) b)
    OSL.Apply ann (OSL.Apply _ (OSL.AddZ _) a) b ->
      Term <$> (S11.Add <$> translateToTerm ctx (OSL.Z ann) a
                        <*> translateToTerm ctx (OSL.Z ann) b)
    OSL.Apply ann (OSL.Apply _ (OSL.MulZ _) a) b ->
      Term <$> (S11.Mul <$> translateToTerm ctx (OSL.Z ann) a
                        <*> translateToTerm ctx (OSL.Z ann) b)
    OSL.ConstN _ x -> return (Term (S11.Const x))
    OSL.ConstZ _ x -> return (Term (S11.Const x))
    OSL.ConstFin _ x -> return (Term (S11.Const x))
    OSL.Apply ann (OSL.NamedTerm _ fName) x ->
      case getDeclaration decls fName of
        Just (OSL.Defined _ f) -> translate ctx termType (OSL.Apply ann f x)
        Just _ -> Left (ErrorMessage ann "expected the name of a defined function")
    OSL.Apply ann (OSL.Apply _ (OSL.Pair _) a) b ->
      case termType of
        OSL.Product _ aType bType -> do
          Mapping <$>
            (ProductMapping
              <$> (LeftMapping <$> translateToMapping ctx aType a)
              <*> (RightMapping <$> translateToMapping ctx bType b))
        _ -> Left (ErrorMessage ann $
          "expected a " <> pack (show termType))
    OSL.Apply ann (OSL.Pi1 _) a -> do
      aT <- inferType decls a
      aM <- translateToMapping ctx aT a
      case aM of
        ProductMapping (LeftMapping m) _ ->
          return (Mapping m)
        _ -> Left (ErrorMessage ann "expected a pair")
    OSL.Apply ann (OSL.Pi2 _) a -> do
      aT <- inferType decls a
      aM <- translateToMapping ctx aT a
      case aM of
        ProductMapping _ (RightMapping m) ->
          return (Mapping m)
        _ -> Left (ErrorMessage ann "expected a pair")
    OSL.Apply ann (OSL.Iota1 _) a ->
      case termType of
        OSL.Coproduct _ b c -> do
          aM <- translateToMapping ctx b a
          bM <- getArbitraryMapping decls c
          return . Mapping
            $ CoproductMapping
              (ChoiceMapping (S11.Const 0))
              (LeftMapping aM)
              (RightMapping bM)
        _ -> Left (ErrorMessage ann "expected a coproduct")
    OSL.Apply ann (OSL.Iota2 _) a ->
      case termType of
        OSL.Coproduct _ b c -> do
          aM <- getArbitraryMapping decls b
          bM <- translateToMapping ctx c a
          return . Mapping
            $ CoproductMapping
              (ChoiceMapping (S11.Const 0))
              (LeftMapping aM)
              (RightMapping bM)
        _ -> Left (ErrorMessage ann "expected a coproduct")
    OSL.FunctionProduct ann f g ->
      case termType of
        OSL.F ann' a (OSL.Product _ b c) ->
          Mapping
          <$> (ProductMapping
            <$> (LeftMapping <$> translateToMapping ctx (OSL.F ann' a b) f)
            <*> (RightMapping <$> translateToMapping ctx (OSL.F ann' a c) g))
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show termType)
    OSL.FunctionCoproduct ann f g ->
      case termType of
        OSL.F ann' a (OSL.Coproduct _ b c) ->
          Mapping
          <$> (FunctionCoproductMapping
            <$> (LeftMapping <$> translateToMapping ctx (OSL.F ann' a b) f)
            <*> (RightMapping <$> translateToMapping ctx (OSL.F ann' a c) g))
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show termType)
    OSL.Apply ann (OSL.Lambda _ varName varType body) x -> do
      xM <- translateToMapping ctx varType x
      let decls' = (OSL.ValidContext
                     (Map.insert varName (OSL.Defined varType x) declsMap))
          ctx' = TranslationContext decls' (Map.insert varName xM mappings)
      bodyType <- inferType decls' body
      Mapping <$> translateToMapping ctx' bodyType body
    OSL.Apply _ (OSL.To ann typeName) x ->
      case getDeclaration decls typeName of
        Just (OSL.Data typeDef) -> translate ctx typeDef x
        Just _ -> Left (ErrorMessage ann "expected the name of a type")
        Nothing -> Left (ErrorMessage ann "undefined name")
    OSL.Apply _ (OSL.From ann typeName) x ->
      translate ctx (OSL.NamedType ann typeName) x
    -- NOTICE: what follows is the last Apply case. It is generic and must
    -- come last among all the Apply cases.
    OSL.Apply ann f x -> do
      fType <- inferType decls f
      case fType of
        OSL.F _ a _ -> do
          fM <- translateToMapping ctx fType f
          xM <- translateToMapping ctx a x
          Mapping <$> applyMappings ann fM xM
        _ -> Left (ErrorMessage ann "expected a function")


getArbitraryMapping
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Either (ErrorMessage ann) (Mapping S11.Term)
getArbitraryMapping ctx =
  \case
    OSL.Prop ann -> Left (ErrorMessage ann "expected a finite-dimensional type; got a Prop")
    OSL.F ann _ _ -> Left (ErrorMessage ann "expected a finite-dimensional type; got a function")
    OSL.N _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Z _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Fin _ _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Product _ a b ->
      ProductMapping
      <$> (LeftMapping <$> rec a)
      <*> (RightMapping <$> rec b)
    OSL.Coproduct _ a b ->
      CoproductMapping (ChoiceMapping (S11.Const 0))
      <$> (LeftMapping <$> rec a)
      <*> (RightMapping <$> rec b)
    OSL.Maybe _ a ->
      MaybeMapping (ChoiceMapping (S11.Const 0))
      . ValuesMapping <$> rec a
    OSL.NamedType ann a ->
      case getDeclaration ctx a of
        Just (OSL.Data b) -> rec b
        Just _ -> Left (ErrorMessage ann "expected the name of a type")
        Nothing -> Left (ErrorMessage ann "undefined name")
  where
    rec = getArbitraryMapping ctx      


translateToMapping
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) (Mapping S11.Term)
translateToMapping c tType t =
  case translate c tType t of
    Right (Mapping m) -> return m
    Right (Term t') -> return (ScalarMapping t')
    

translateToTerm
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) S11.Term
translateToTerm c tType t =
  case translate c tType t of
    Right (Term t') -> return t'
    Right (Mapping (ScalarMapping t')) -> return t'
    Right _ -> Left (ErrorMessage (termAnnotation t)
                 "expected a term denoting a scalar")
    Left err -> Left err


applyMappings
  :: ann
  -> Mapping S11.Term
  -> Mapping S11.Term
  -> Either (ErrorMessage ann) (Mapping S11.Term)
applyMappings ann f x =
  case (f, x) of
    (ScalarMapping f', ScalarMapping x') ->
      ScalarMapping <$> applyTerms ann f' x'
    (ProductMapping (LeftMapping f) (RightMapping g), x) ->
      ProductMapping
      <$> (LeftMapping <$> applyMappings ann f x)
      <*> (RightMapping <$> applyMappings ann g x)
    (FunctionCoproductMapping (LeftMapping f) (RightMapping g),
     CoproductMapping (ChoiceMapping a) (LeftMapping b) (RightMapping c)) ->
      CoproductMapping (ChoiceMapping a)
      <$> (LeftMapping <$> applyMappings ann f b)
      <*> (RightMapping <$> applyMappings ann g c)


applyTerms
  :: ann
  -> S11.Term
  -> S11.Term
  -> Either (ErrorMessage ann) S11.Term
applyTerms ann f x =
  case f of
    S11.Var f' -> pure $ S11.App f' [x]
    S11.App f' ys -> pure $ S11.App f' (ys <> [x])
    _ -> Left $ ErrorMessage ann "expected a function term"


todo :: a
todo = todo
