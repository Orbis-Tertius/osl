{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module OSL.Translate
  ( translate,
    translateToTerm,
    translateToFormula,
  )
where

import Control.Applicative (liftA2)
import Control.Lens ((^.))
import Control.Monad (forM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.State.Strict (StateT, execStateT, get, put)
import Data.Functor.Identity (runIdentity)
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (pack)
import Die (die)
import OSL.Bound (boundAnnotation)
import OSL.BuildTranslationContext (addFreeVariableMapping, addTermMapping, buildTranslationContext', getBoundS11NamesInContext, getFreeOSLName, getFreeS11Name)
import OSL.Sigma11 (incrementArities, incrementDeBruijnIndices, prependBounds)
import OSL.Term (termAnnotation)
import OSL.TranslationContext (linearizeMapping, mergeMapping, mergeMappings)
import OSL.Type (typeAnnotation)
import OSL.Types.Arity (Arity (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.Translation (Translation (Formula, Mapping, Term))
import OSL.Types.TranslationContext (ChoiceMapping (..), KeysMapping (..), LeftMapping (..), LengthMapping (..), Mapping (..), MappingDimensions (..), RightMapping (..), TranslationContext (..), ValuesMapping (..))
import OSL.ValidContext (addDeclaration, getDeclaration)
import OSL.ValidateContext (inferType)

-- Provides a translation for the given term in
-- the given context.
translate ::
  Show ann =>
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Type ann ->
  OSL.Term ann ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) (Translation ann)
translate
  gc@(TranslationContext gDecls _)
  lc@(TranslationContext decls@(OSL.ValidContext declsMap) mappings)
  termType =
    \case
      OSL.NamedTerm ann name ->
        case Map.lookup name mappings of
          Just (ScalarMapping x) -> return (Term x)
          Just m -> return (Mapping m)
          Nothing ->
            case Map.lookup name declsMap of
              Just (OSL.Defined defType def) -> do
                translate gc (TranslationContext decls mempty) defType def
              _ ->
                lift . Left . ErrorMessage ann $
                  "un-mapped name: " <> pack (show name)
      OSL.Apply ann (OSL.Apply _ (OSL.AddN _) a) b ->
        Term
          <$> ( S11.Add
                  <$> translateToTerm gc lc (OSL.N ann) a
                  <*> translateToTerm gc lc (OSL.N ann) b
              )
      OSL.Apply ann (OSL.Apply _ (OSL.MulN _) a) b ->
        Term
          <$> ( S11.Mul
                  <$> translateToTerm gc lc (OSL.N ann) a
                  <*> translateToTerm gc lc (OSL.N ann) b
              )
      OSL.Apply ann (OSL.Apply _ (OSL.AddZ _) a) b ->
        Term
          <$> ( S11.Add
                  <$> translateToTerm gc lc (OSL.Z ann) a
                  <*> translateToTerm gc lc (OSL.Z ann) b
              )
      OSL.Apply ann (OSL.Apply _ (OSL.MulZ _) a) b ->
        Term
          <$> ( S11.Mul
                  <$> translateToTerm gc lc (OSL.Z ann) a
                  <*> translateToTerm gc lc (OSL.Z ann) b
              )
      OSL.Apply ann (OSL.Apply _ (OSL.AddFp _) a) b ->
        Term
          <$> ( S11.Add
                  <$> translateToTerm gc lc (OSL.Fp ann) a
                  <*> translateToTerm gc lc (OSL.Fp ann) b
              )
      OSL.Apply ann (OSL.Apply _ (OSL.MulFp _) a) b ->
        Term
          <$> ( S11.Add
                  <$> translateToTerm gc lc (OSL.Fp ann) a
                  <*> translateToTerm gc lc (OSL.Fp ann) b
              )
      OSL.Apply _ (OSL.Cast _) a -> do
        aT <- lift $ inferType decls a
        translate gc lc aT a
      OSL.Apply _ (OSL.ListCast _) as -> do
        asT <- lift $ inferType decls as
        translate gc lc asT as
      OSL.Apply ann (OSL.Apply _ (OSL.Inverse _) f) x -> do
        fType <- lift $ inferType decls f
        fT <- translateToTerm gc lc fType f
        case (fType, fT) of
          (OSL.P _ _ _ xType, S11.App fT' []) -> do
            xT <- translateToTerm gc lc xType x
            pure (Term (S11.AppInverse fT' xT))
          _ -> lift . Left $ ErrorMessage ann "expected a permutation"
      OSL.ConstN _ x -> return (Term (S11.Const x))
      OSL.ConstZ _ x -> return (Term (S11.Const x))
      OSL.ConstFin _ x -> return (Term (S11.Const x))
      OSL.ConstFp _ x -> return (Term (S11.Const x))
      OSL.ConstSet ann xs ->
        case termType of
          OSL.F _ _ xType (OSL.Prop _) -> do
            xDim <- lift $ getMappingDimensions decls xType
            case xDim of
              FiniteDimensions n -> do
                S11.AuxTables fTables pTables <- get
                cs <- forM xs $ lift . translateToConstant gDecls decls xType
                let s = Set.fromList (linearizeMapping <$> cs)
                nm <- case Map.toList (Map.filter (== s) pTables) of
                  ((nm, _) : _) -> pure nm
                  _ -> do
                    nm <- getFreeS11PredicateNameM (Arity n)
                    put $
                      S11.AuxTables
                        fTables
                        ( Map.insert
                            nm
                            (Set.fromList (linearizeMapping <$> cs))
                            pTables
                        )
                    pure nm
                pure (Mapping (PredicateMapping nm))
              InfiniteDimensions ->
                lift . Left . ErrorMessage ann $
                  "set literals must range over a finite-dimensional type but the contextual element type is " <> pack (show xType)
          _ ->
            lift . Left . ErrorMessage ann $
              "unexpected set literal; expected a " <> pack (show termType)
      OSL.ConstF ann fs ->
        case termType of
          OSL.F _ _ xType yType -> do
            dim <- lift $ getMappingDimensions decls xType
            case dim of
              InfiniteDimensions ->
                lift . Left $ ErrorMessage ann "domain type of a function table literal must be finite-dimensional"
              FiniteDimensions n -> do
                aux@(S11.AuxTables fTables pTables) <- get
                xs :: [[Integer]] <-
                  fmap linearizeMapping
                    <$> ( forM
                            (fst <$> fs)
                            (lift . translateToConstant gDecls decls xType)
                        )
                ys :: [[Integer]] <-
                  fmap linearizeMapping
                    <$> forM
                      (snd <$> fs)
                      (lift . translateToConstant gDecls decls yType)
                ys' :: [Integer] <- forM ys $
                  \case
                    [x] -> pure x
                    _ -> lift . Left $ ErrorMessage ann "expected function codomain to be scalar"
                let f = Map.fromList (zip xs ys')
                nm <- case Map.toList (Map.filter (== f) fTables) of
                  ((nm, _) : _) -> pure nm
                  _ -> do
                    let nm = getFreeS11NameM (Arity n) lc aux
                    put $
                      S11.AuxTables
                        (Map.insert nm f fTables)
                        pTables
                    pure nm
                pure (Mapping (ScalarMapping (S11.var nm)))
          _ ->
            lift . Left . ErrorMessage ann $
              "expected a "
                <> pack (show termType)
                <> " but got a function table literal"
      OSL.Apply ann (OSL.NamedTerm ann' fName) x ->
        case getDeclaration decls fName of
          Just (OSL.Defined fType@(OSL.F _ _ a _) f) -> do
            fM <- translateToMapping gc lc fType f
            xM <- translateToMapping gc lc a x
            Mapping <$> applyMappings ann termType fM xM
          Just (OSL.FreeVariable fType@(OSL.F _ _ a _)) -> do
            fM <- translateToMapping gc lc fType (OSL.NamedTerm ann' fName)
            xM <- translateToMapping gc lc a x
            Mapping <$> applyMappings ann termType fM xM
          Just (OSL.FreeVariable fType@(OSL.P _ _ a _)) -> do
            fM <- translateToMapping gc lc fType (OSL.NamedTerm ann' fName)
            xM <- translateToMapping gc lc a x
            Mapping <$> applyMappings ann termType fM xM
          Just _ -> lift . Left $ ErrorMessage ann' "expected the name of a function"
          Nothing -> lift . Left $ ErrorMessage ann' "undefined name"
      OSL.Apply ann (OSL.Apply _ (OSL.Pair _) a) b ->
        case termType of
          OSL.Product _ aType bType -> do
            Mapping
              <$> ( ProductMapping
                      <$> (LeftMapping <$> translateToMapping gc lc aType a)
                      <*> (RightMapping <$> translateToMapping gc lc bType b)
                  )
          _ ->
            lift . Left . ErrorMessage ann $
              "expected a "
                <> pack (show termType)
                <> " but got a pair"
      OSL.Apply ann (OSL.Pi1 _) a -> do
        aT <- lift $ inferType decls a
        aM <- translateToMapping gc lc aT a
        case aM of
          ProductMapping (LeftMapping m) _ ->
            return (Mapping m)
          _ -> lift . Left $ ErrorMessage ann "expected a pair"
      OSL.Apply ann (OSL.Pi2 _) a -> do
        aT <- lift $ inferType decls a
        aM <- translateToMapping gc lc aT a
        case aM of
          ProductMapping _ (RightMapping m) ->
            return (Mapping m)
          _ -> lift . Left $ ErrorMessage ann "expected a pair"
      OSL.Apply ann (OSL.Iota1 _) a ->
        case termType of
          OSL.Coproduct _ b c -> do
            aM <- translateToMapping gc lc b a
            bM <- lift $ getArbitraryMapping decls c
            return . Mapping $
              CoproductMapping
                (ChoiceMapping (ScalarMapping (S11.Const 0)))
                (LeftMapping aM)
                (RightMapping bM)
          _ -> lift . Left $ ErrorMessage ann "expected a coproduct"
      OSL.Apply ann (OSL.Iota2 _) a ->
        case termType of
          OSL.Coproduct _ b c -> do
            aM <- lift $ getArbitraryMapping decls b
            bM <- translateToMapping gc lc c a
            return . Mapping $
              CoproductMapping
                (ChoiceMapping (ScalarMapping (S11.Const 0)))
                (LeftMapping aM)
                (RightMapping bM)
          _ -> lift . Left $ ErrorMessage ann "expected a coproduct"
      OSL.FunctionProduct ann f g ->
        case termType of
          OSL.F ann' n a (OSL.Product _ b c) ->
            Mapping
              <$> ( ProductMapping
                      <$> (LeftMapping <$> translateToMapping gc lc (OSL.F ann' n a b) f)
                      <*> (RightMapping <$> translateToMapping gc lc (OSL.F ann' n a c) g)
                  )
          _ ->
            lift . Left . ErrorMessage ann $
              "expected a "
                <> pack (show termType)
                <> " but got a function product"
      OSL.FunctionCoproduct ann f g ->
        case termType of
          OSL.F ann' n (OSL.Coproduct _ a b) c ->
            Mapping
              <$> ( FunctionCoproductMapping
                      <$> (LeftMapping <$> translateToMapping gc lc (OSL.F ann' n a c) f)
                      <*> (RightMapping <$> translateToMapping gc lc (OSL.F ann' n b c) g)
                  )
          _ ->
            lift . Left . ErrorMessage ann $
              "expected a "
                <> pack (show termType)
                <> " but got a function coproduct"
      OSL.Lambda _ v vT t ->
        pure
          ( Mapping
              ( LambdaMapping
                  gc
                  ( TranslationContext
                      ( addDeclaration
                          v
                          (OSL.FreeVariable vT)
                          -- convert context of unknown type to local context
                          (OSL.ValidContext (OSL.unValidContext decls))
                      )
                      mappings
                  )
                  v
                  vT
                  t
              )
          )
      OSL.Apply _ (OSL.Lambda _ varName varType body) x -> do
        xM <- translateToMapping gc lc varType x
        let decls' =
              OSL.ValidContext
                (Map.insert varName (OSL.FreeVariable varType) declsMap)
            lc' = TranslationContext decls' (Map.insert varName xM mappings)
        translate gc lc' termType body
      OSL.Apply _ (OSL.To ann typeName) x ->
        case getDeclaration decls typeName of
          Just (OSL.Data typeDef) -> translate gc lc typeDef x
          Just _ -> lift . Left $ ErrorMessage ann "expected the name of a type"
          Nothing -> lift . Left $ ErrorMessage ann "undefined name"
      OSL.Apply _ (OSL.From ann typeName) x ->
        translate gc lc (OSL.NamedType ann typeName) x
      OSL.Apply ann (OSL.IsNothing _) x -> do
        xT <- lift $ inferType decls x
        xM <- translateToMapping gc lc xT x
        case xM of
          MaybeMapping (ChoiceMapping (ScalarMapping cT)) _ ->
            pure (Formula (S11.Equal cT (S11.Const 0)))
          _ -> lift . Left $ ErrorMessage ann "expected a Maybe mapping"
      OSL.Apply ann (OSL.Just' _) x ->
        case termType of
          OSL.Maybe _ xType ->
            Mapping
              . MaybeMapping (ChoiceMapping (ScalarMapping (S11.Const 1)))
              . ValuesMapping
              <$> translateToMapping gc lc xType x
          _ ->
            lift . Left . ErrorMessage ann $
              "expected a "
                <> pack (show termType)
                <> " but got just(...)"
      OSL.Nothing' ann ->
        case termType of
          OSL.Maybe _ xType ->
            lift $
              Mapping
                . MaybeMapping (ChoiceMapping (ScalarMapping (S11.Const 0)))
                . ValuesMapping
                <$> getArbitraryMapping decls xType
          _ ->
            lift . Left . ErrorMessage ann $
              "expected a "
                <> pack (show termType)
                <> " but got nothing"
      OSL.Apply ann (OSL.Apply _ (OSL.Maybe' ann' f) b) a -> do
        fType <- lift $ inferType decls f
        case fType of
          OSL.F _ _ aType _ -> do
            aM <- translateToMapping gc lc (OSL.Maybe ann aType) a
            bT <- translateToTerm gc lc termType b
            fM <- translateToMapping gc lc fType f
            case aM of
              MaybeMapping
                (ChoiceMapping (ScalarMapping choiceT))
                (ValuesMapping vM) -> do
                  fvM <- applyMappings ann termType fM vM
                  case fvM of
                    ScalarMapping fvT ->
                      pure . Term $
                        (choiceT `S11.Mul` fvT)
                          `S11.Add` ( ( S11.Const 1
                                          `S11.Add` (S11.Const (-1) `S11.Mul` choiceT)
                                      )
                                        `S11.Mul` bT
                                    )
                    _ -> lift . Left . ErrorMessage ann $ "expected a scalar value"
              _ -> lift . Left . ErrorMessage ann $ "expected a maybe value"
          _ -> lift . Left . ErrorMessage ann' $ "expected a function"
      OSL.Apply ann (OSL.Exists _) mx -> do
        mxM <- translateToMapping gc lc (OSL.Maybe ann termType) mx
        case mxM of
          MaybeMapping _ (ValuesMapping xM) -> pure (Mapping xM)
          _ -> lift . Left . ErrorMessage ann $ "expected a maybe mapping"
      OSL.Apply ann (OSL.MaybePi1 _) x -> do
        xT <- lift $ inferType decls x
        xM <- translateToMapping gc lc xT x
        case xM of
          MaybeMapping
            choiceM
            (ValuesMapping (ProductMapping (LeftMapping aM) _)) ->
              pure . Mapping $ MaybeMapping choiceM (ValuesMapping aM)
          _ -> lift . Left $ ErrorMessage ann "expected a Maybe(_ * _) mapping"
      OSL.Apply ann (OSL.MaybePi2 _) x -> do
        xT <- lift $ inferType decls x
        xM <- translateToMapping gc lc xT x
        case xM of
          MaybeMapping
            choiceM
            (ValuesMapping (ProductMapping _ (RightMapping aM))) ->
              pure . Mapping $ MaybeMapping choiceM (ValuesMapping aM)
          _ -> lift . Left $ ErrorMessage ann "expected a Maybe(_ * _) mapping"
      OSL.Apply _ (OSL.MaybeFrom _ _) x -> do
        xT <- lift $ inferType decls x
        translate gc lc xT x
      OSL.Apply _ (OSL.MaybeTo _ _) x -> do
        xT <- lift $ inferType decls x
        translate gc lc xT x
      OSL.Apply ann (OSL.Length _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping (LengthMapping (ScalarMapping lT)) _ -> pure (Term lT)
          _ -> lift . Left $ ErrorMessage ann "expected a list"
      OSL.Apply ann (OSL.Apply _ (OSL.Nth _) xs) i -> do
        iM <- translateToMapping gc lc (OSL.N ann) i
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping _ (ValuesMapping vM) ->
            Mapping <$> applyMappings ann termType vM iM
          _ -> lift . Left $ ErrorMessage ann "nth expected a list mapping"
      OSL.Apply ann (OSL.ListPi1 _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping lM (ValuesMapping (ProductMapping (LeftMapping aM) _)) ->
            pure . Mapping $ ListMapping lM (ValuesMapping aM)
          _ -> lift . Left . ErrorMessage ann $ "List(pi1) expected a list of pairs"
      OSL.Apply ann (OSL.ListPi2 _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping lM (ValuesMapping (ProductMapping _ (RightMapping bM))) ->
            pure . Mapping $ ListMapping lM (ValuesMapping bM)
          _ -> lift . Left . ErrorMessage ann $ "expected a list of pairs"
      OSL.Apply ann (OSL.ListTo ann' name) xs -> do
        case getDeclaration decls name of
          Just (OSL.Data a) -> do
            xsType <- lift $ inferType decls xs
            case xsType of
              OSL.List _ n _ ->
                Mapping <$> translateToMapping gc lc (OSL.List ann' n a) xs
              _ -> lift . Left $ ErrorMessage ann "expected a list"
          Just _ -> lift . Left $ ErrorMessage ann' "expected the name of a type"
          Nothing -> lift . Left $ ErrorMessage ann' "undefined name"
      OSL.Apply ann (OSL.ListFrom ann' name) xs ->
        case getDeclaration decls name of
          Just (OSL.Data _) -> do
            xsType <- lift $ inferType decls xs
            case xsType of
              OSL.List _ n _ ->
                Mapping
                  <$> translateToMapping
                    gc
                    lc
                    (OSL.List ann' n (OSL.NamedType ann' name))
                    xs
              _ -> lift . Left $ ErrorMessage ann "expected a list"
          Just _ -> lift . Left $ ErrorMessage ann' "expected the name of a type"
          Nothing -> lift . Left $ ErrorMessage ann' "undefined name"
      OSL.Apply ann (OSL.ListLength _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping lM (ValuesMapping (ListMapping (LengthMapping xslM) _)) ->
            pure . Mapping $ ListMapping lM (ValuesMapping xslM)
          _ -> lift . Left $ ErrorMessage ann "expected a list of lists"
      OSL.Apply ann (OSL.ListMaybeTo ann' name) xs -> do
        case getDeclaration decls name of
          Just (OSL.Data a) -> do
            xsType <- lift $ inferType decls xs
            case xsType of
              OSL.List _ n (OSL.Maybe _ _) ->
                Mapping <$> translateToMapping gc lc (OSL.List ann' n a) xs
              _ -> lift . Left $ ErrorMessage ann "expected a list of maybe"
          Just _ -> lift . Left $ ErrorMessage ann' "expected the name of a type"
          Nothing -> lift . Left $ ErrorMessage ann' "undefined name"
      OSL.Apply ann (OSL.ListMaybeFrom ann' name) xs -> do
        case getDeclaration decls name of
          Just (OSL.Data _) -> do
            xsType <- lift $ inferType decls xs
            case xsType of
              OSL.List _ n (OSL.Maybe _ _) ->
                Mapping
                  <$> translateToMapping
                    gc
                    lc
                    (OSL.List ann' n (OSL.NamedType ann' name))
                    xs
              _ -> lift . Left $ ErrorMessage ann "expected a list of maybe"
          Just _ -> lift . Left $ ErrorMessage ann' "expected the name of a type"
          Nothing -> lift . Left $ ErrorMessage ann' "undefined name"
      OSL.Apply ann (OSL.ListMaybePi1 _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping
            lM
            ( ValuesMapping
                ( MaybeMapping
                    cM
                    ( ValuesMapping
                        (ProductMapping (LeftMapping aM) (RightMapping _))
                      )
                  )
              ) -> do
              pure . Mapping $
                ListMapping
                  lM
                  ( ValuesMapping
                      (MaybeMapping cM (ValuesMapping aM))
                  )
          _ -> lift . Left $ ErrorMessage ann "expected a list of maybe pair"
      OSL.Apply ann (OSL.ListMaybePi2 _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping
            lM
            ( ValuesMapping
                ( MaybeMapping
                    cM
                    ( ValuesMapping
                        (ProductMapping (LeftMapping _) (RightMapping bM))
                      )
                  )
              ) -> do
              pure . Mapping $
                ListMapping
                  lM
                  ( ValuesMapping
                      (MaybeMapping cM (ValuesMapping bM))
                  )
          _ -> lift . Left $ ErrorMessage ann "expected a list of maybe pair"
      OSL.Apply ann (OSL.ListMaybeLength _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsM of
          ListMapping
            lM
            ( ValuesMapping
                ( MaybeMapping
                    cM
                    (ValuesMapping (ListMapping (LengthMapping xslM) _))
                  )
              ) ->
              pure . Mapping $
                ListMapping
                  lM
                  (ValuesMapping (MaybeMapping cM (ValuesMapping xslM)))
          _ -> lift . Left $ ErrorMessage ann "expected a list of maybe list"
      OSL.Apply ann (OSL.Sum _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsType of
          OSL.List _ (OSL.Cardinality n) (OSL.List _ (OSL.Cardinality m) _) ->
            case xsM of
              ListMapping
                (LengthMapping (ScalarMapping lT))
                ( ValuesMapping
                    ( ListMapping
                        (LengthMapping (ScalarMapping rT))
                        ( ValuesMapping
                            ( MaybeMapping
                                (ChoiceMapping (ScalarMapping cT))
                                (ValuesMapping (ScalarMapping vT))
                              )
                          )
                      )
                  ) ->
                  lift $
                    Term
                      <$> foldl
                        (liftA2 (S11.Add))
                        (pure (S11.Const 0))
                        [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                            . (S11.IndLess (S11.Const j) rT `S11.Mul`)
                            <$> ( S11.Mul
                                    <$> ( flip (applyTerms ann) (S11.Const j)
                                            =<< applyTerms ann vT (S11.Const i)
                                        )
                                    <*> ( flip (applyTerms ann) (S11.Const j)
                                            =<< applyTerms ann cT (S11.Const i)
                                        )
                                )
                          | i <- [0 .. n - 1],
                            j <- [0 .. m - 1]
                        ]
              ListMapping
                (LengthMapping (ScalarMapping lT))
                ( ValuesMapping
                    ( ListMapping
                        (LengthMapping (ScalarMapping rT))
                        ( ValuesMapping
                            (ScalarMapping vT)
                          )
                      )
                  ) ->
                  lift $
                    Term
                      <$> foldl
                        (liftA2 (S11.Add))
                        (pure (S11.Const 0))
                        [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                            . (S11.IndLess (S11.Const j) rT `S11.Mul`)
                            <$> ( flip (applyTerms ann) (S11.Const j)
                                    =<< applyTerms ann vT (S11.Const i)
                                )
                          | i <- [0 .. n - 1],
                            j <- [0 .. m - 1]
                        ]
              _ -> lift . Left $ ErrorMessage ann "expected a list mapping"
          OSL.List _ (OSL.Cardinality n) _ ->
            case xsM of
              ListMapping
                (LengthMapping (ScalarMapping lT))
                ( ValuesMapping
                    ( MaybeMapping
                        (ChoiceMapping (ScalarMapping cT))
                        (ValuesMapping (ScalarMapping vT))
                      )
                  ) ->
                  lift $
                    Term
                      <$> foldl
                        (liftA2 (S11.Add))
                        (pure (S11.Const 0))
                        [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                            <$> ( S11.Mul
                                    <$> applyTerms ann cT (S11.Const i)
                                    <*> applyTerms ann vT (S11.Const i)
                                )
                          | i <- [0 .. n - 1]
                        ]
              ListMapping
                (LengthMapping (ScalarMapping lT))
                (ValuesMapping (ScalarMapping xsT)) ->
                  lift $
                    Term
                      <$> foldl
                        (liftA2 (S11.Add))
                        (pure (S11.Const 0))
                        [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                            <$> applyTerms ann xsT (S11.Const i)
                          | i <- [0 .. n - 1]
                        ]
              _ -> lift . Left $ ErrorMessage ann "expected a list mapping"
          OSL.Map _ (OSL.Cardinality n) _ _ ->
            case xsM of
              MapMapping
                (LengthMapping (ScalarMapping lT))
                (KeysMapping (ScalarMapping kT))
                (ValuesMapping (ScalarMapping vT)) ->
                  lift $
                    Term
                      <$> foldl
                        (liftA2 (S11.Add))
                        (pure (S11.Const 0))
                        [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                            <$> (applyTerms ann vT =<< applyTerms ann kT (S11.Const i))
                          | i <- [0 .. n - 1]
                        ]
              _ -> lift . Left $ ErrorMessage ann "expected a map mapping"
          _ -> lift . Left $ ErrorMessage ann "expected a list or map type"
      OSL.Apply ann (OSL.Apply _ (OSL.Lookup _) k) xs -> do
        xsType <- lift $ inferType decls xs
        case xsType of
          OSL.Map _ _ kType vType -> do
            xsM <- translateToMapping gc lc xsType xs
            kM <- translateToMapping gc lc kType k
            case xsM of
              MapMapping _ _ (ValuesMapping vM) -> do
                vM' <- applyMappings ann vType vM kM
                pure (Mapping vM')
              _ -> lift . Left $ ErrorMessage ann "expected a map mapping"
          _ -> lift . Left $ ErrorMessage ann "expected a map"
      OSL.Apply ann (OSL.MapPi1 _) xs -> do
        xsType <- lift $ inferType decls xs
        case xsType of
          OSL.Map _ _ _ (OSL.Product _ _ _) -> do
            xsM <- translateToMapping gc lc xsType xs
            case xsM of
              MapMapping
                lM
                kM
                ( ValuesMapping
                    (ProductMapping (LeftMapping aM) _)
                  ) ->
                  pure . Mapping $ MapMapping lM kM (ValuesMapping aM)
              _ -> lift . Left $ ErrorMessage ann "expected a map mapping"
          _ -> lift . Left $ ErrorMessage ann "expected a map"
      OSL.Apply ann (OSL.MapPi2 _) xs -> do
        xsType <- lift $ inferType decls xs
        case xsType of
          OSL.Map _ _ _ (OSL.Product _ _ _) -> do
            xsM <- translateToMapping gc lc xsType xs
            case xsM of
              MapMapping
                lM
                kM
                ( ValuesMapping
                    (ProductMapping _ (RightMapping bM))
                  ) ->
                  pure . Mapping $ MapMapping lM kM (ValuesMapping bM)
              _ -> lift . Left $ ErrorMessage ann "expected a map mapping"
          _ -> lift . Left $ ErrorMessage ann "expected a map"
      OSL.Apply _ (OSL.MapTo _ _) xs -> do
        xsType <- lift $ inferType decls xs
        translate gc lc xsType xs
      OSL.Apply _ (OSL.MapFrom _ _) xs -> do
        xsType <- lift $ inferType decls xs
        translate gc lc xsType xs
      OSL.Apply ann (OSL.Keys _) xs -> do
        xsType <- lift $ inferType decls xs
        case xsType of
          OSL.Map _ _ _ _ -> do
            xsM <- translateToMapping gc lc xsType xs
            case xsM of
              MapMapping lM (KeysMapping kM) _ ->
                pure . Mapping $ ListMapping lM (ValuesMapping kM)
              _ -> lift . Left $ ErrorMessage ann "expected a map mapping"
          _ -> lift . Left $ ErrorMessage ann "expected a map"
      OSL.Apply ann (OSL.SumMapLength _) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsType of
          OSL.Map _ (OSL.Cardinality n) _ (OSL.List _ _ _) ->
            case xsM of
              MapMapping
                (LengthMapping (ScalarMapping lT))
                (KeysMapping _)
                ( ValuesMapping
                    ( ListMapping
                        (LengthMapping (ScalarMapping mT))
                        (ValuesMapping _)
                      )
                  ) ->
                  lift $
                    Term
                      <$> foldl
                        (liftA2 (S11.Add))
                        (pure (S11.Const 0))
                        [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                            <$> applyTerms ann mT (S11.Const i)
                          | i <- [0 .. n - 1]
                        ]
              _ -> lift . Left $ ErrorMessage ann "expected a map of scalar to scalar"
          _ -> lift . Left $ ErrorMessage ann "expected a map of list"
      OSL.Apply ann (OSL.SumListLookup _ k) xs -> do
        xsType <- lift $ inferType decls xs
        xsM <- translateToMapping gc lc xsType xs
        case xsType of
          OSL.List _ (OSL.Cardinality n) mapType@(OSL.Map _ _ kType _) -> do
            kM <- translateToMapping gc lc kType k
            case xsM of
              ListMapping
                (LengthMapping (ScalarMapping lT))
                ( ValuesMapping
                    ( MapMapping
                        (LengthMapping _)
                        (KeysMapping _)
                        (ValuesMapping vM)
                      )
                  ) ->
                  Term
                    <$> foldl
                      (liftA2 (S11.Add))
                      (pure (S11.Const 0))
                      [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                          <$> ( lift . mappingToTerm ann
                                  =<< flip (applyMappings ann kType) kM
                                  =<< applyMappings ann mapType vM (ScalarMapping (S11.Const i))
                              )
                        | i <- [0 .. n - 1]
                      ]
              _ -> lift . Left $ ErrorMessage ann "could not translate sumListLookup application"
          _ -> lift . Left $ ErrorMessage ann "type error in sumListLookup application"
      -- NOTICE: what follows is the last Apply case. It is generic and must
      -- come last among all the Apply cases.
      OSL.Apply ann f x -> do
        fType <- lift $ inferType decls f
        case fType of
          OSL.F _ _ a _ -> do
            fM <- translateToMapping gc lc fType f
            xM <- translateToMapping gc lc a x
            Mapping <$> applyMappings ann termType fM xM
          OSL.P _ _ a _ -> do
            fM <- translateToMapping gc lc fType f
            xM <- translateToMapping gc lc a x
            Mapping <$> applyMappings ann termType fM xM
          _ -> lift . Left $ ErrorMessage ann "expected a function or permutation"
      OSL.Let _ varName varType varDef body -> do
        varDefM <- translateToMapping gc lc varType varDef
        let decls' =
              OSL.ValidContext
                (Map.insert varName (OSL.Defined varType varDef) declsMap)
            lc' = TranslationContext decls' (Map.insert varName varDefM mappings)
        translate gc lc' termType body
      OSL.Equal ann x y -> do
        xType <- lift $ inferType decls x
        Formula <$> translateEquality ann gc lc xType x y
      OSL.LessOrEqual _ x y -> do
        xType <- lift $ inferType decls x
        Formula
          <$> ( S11.LessOrEqual
                  <$> translateToTerm gc lc xType x
                  <*> translateToTerm gc lc xType y
              )
      OSL.And _ p q ->
        Formula
          <$> ( S11.And
                  <$> translateToFormula gc lc p
                  <*> translateToFormula gc lc q
              )
      OSL.Or _ p q ->
        Formula
          <$> ( S11.Or
                  <$> translateToFormula gc lc p
                  <*> translateToFormula gc lc q
              )
      OSL.Not _ p ->
        Formula . S11.Not <$> translateToFormula gc lc p
      OSL.Implies _ p q ->
        Formula
          <$> ( S11.Implies
                  <$> translateToFormula gc lc p
                  <*> translateToFormula gc lc q
              )
      OSL.Iff _ p q ->
        Formula
          <$> ( S11.Iff
                  <$> translateToFormula gc lc p
                  <*> translateToFormula gc lc q
              )
      OSL.ForAll ann varName varType varBound p -> do
        varDim <- lift $ getMappingDimensions decls varType
        case varDim of
          FiniteDimensions n -> do
            let decls' =
                  OSL.ValidContext $
                    Map.insert varName (OSL.FreeVariable varType) declsMap
            TranslationContext _ qCtx <-
              lift $ buildTranslationContext' decls' [varName]
            let lc' =
                  TranslationContext
                    decls'
                    (qCtx `Map.union` (incrementDeBruijnIndices (Arity 0) n <$> mappings))
            bounds <- translateBound gc lc varType varBound
            Formula . foldl (.) id (S11.ForAll <$> bounds)
              <$> translateToFormula gc lc' p
          InfiniteDimensions ->
            lift . Left $ ErrorMessage ann "universal quantification over an infinite-dimensional type"
      OSL.ForSome _ varName varType varBound p -> do
        let decls' =
              OSL.ValidContext $
                Map.insert varName (OSL.FreeVariable varType) declsMap
        varDim <- lift $ getMappingDimensions decls varType
        case varDim of
          FiniteDimensions n -> do
            TranslationContext _ qCtx <-
              lift $ buildTranslationContext' decls' [varName]
            let lc' =
                  TranslationContext
                    decls'
                    (qCtx `Map.union` (incrementDeBruijnIndices (Arity 0) n <$> mappings))
            bounds <- translateBound gc lc varType varBound
            Formula . foldl (.) id (S11.ForSome . S11.someFirstOrder <$> bounds)
              <$> translateToFormula gc lc' p
          InfiniteDimensions -> do
            (qs, newMapping) <-
              getExistentialQuantifierStringAndMapping gc lc varType
                =<< lift (getExplicitOrInferredBound decls varType varBound)
            let lc' =
                  TranslationContext
                    decls'
                    (mergeMappings (Map.singleton varName newMapping) mappings)
            Formula . (\f -> foldl' (flip S11.ForSome) f qs)
              <$> translateToFormula gc lc' p
      term ->
        lift . Left . ErrorMessage (termAnnotation term) $
          "could not translate term: " <> pack (show term)

getExplicitOrInferredBound ::
  OSL.ValidContext t ann ->
  OSL.Type ann ->
  Maybe (OSL.Bound ann) ->
  Either (ErrorMessage ann) (OSL.Bound ann)
getExplicitOrInferredBound ctx t =
  maybe (inferBound ctx t) pure

getExistentialQuantifierStringAndMapping ::
  Show ann =>
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Type ann ->
  OSL.Bound ann ->
  StateT
    S11.AuxTables
    (Either (ErrorMessage ann))
    ([S11.ExistentialQuantifier], Mapping ann S11.Term)
getExistentialQuantifierStringAndMapping gc lc@(TranslationContext decls mappings) varType varBound =
  case varType of
    OSL.Prop ann -> lift . Left $ ErrorMessage ann "cannot quantify over Prop"
    OSL.N _ -> scalarResult
    OSL.Z _ -> scalarResult
    OSL.Fp _ -> scalarResult
    OSL.Fin _ _ -> scalarResult
    OSL.F ann mCardinality a b -> do
      aDim <- lift $ getMappingDimensions decls a
      case (aDim, varBound) of
        (FiniteDimensions n, OSL.FunctionBound _ (OSL.DomainBound aBound) (OSL.CodomainBound bBound)) -> do
          cardinality <- case mCardinality of
            Just m -> pure m
            Nothing -> lift . Left $ ErrorMessage ann "missing function type cardinality (required for quantification)"
          (bQs, bM) <- getExistentialQuantifierStringAndMapping gc lc b bBound
          let fM = incrementArities n bM
          aBounds <-
            fmap S11.InputBound
              <$> translateBound gc lc a (Just aBound)
          let fQs = prependBounds cardinality aBounds <$> bQs
          pure (fQs, fM)
        (FiniteDimensions _, _) ->
          lift . Left $
            ErrorMessage
              (boundAnnotation varBound)
              "expected a function bound"
        (InfiniteDimensions, _) ->
          lift . Left $
            ErrorMessage
              (typeAnnotation a)
              "expected a finite-dimensional type"
    OSL.P ann mCardinality a b -> do
      cardinality <- case mCardinality of
        Just n -> pure n
        Nothing -> lift . Left . ErrorMessage ann $ "missing permutation type cardinality (required for quantification)"
      case varBound of
        OSL.FunctionBound _ (OSL.DomainBound aBound) (OSL.CodomainBound bBound) -> do
          bBoundTs <-
            fmap S11.OutputBound
              <$> translateBound gc lc a (Just bBound)
          (_, bM) <- getExistentialQuantifierStringAndMapping gc lc b bBound
          let fM = incrementArities 1 bM
          aBoundTs <-
            fmap S11.InputBound
              <$> translateBound gc lc a (Just aBound)
          case (aBoundTs, bBoundTs) of
            ([aBoundT], [bBoundT]) ->
              pure ([S11.SomeP cardinality aBoundT bBoundT], fM)
            _ -> lift . Left $ ErrorMessage ann "non-scalar bounds for a permutation; this is a compiler bug"
        _ ->
          lift . Left $
            ErrorMessage
              (boundAnnotation varBound)
              "expected a function bound"
    OSL.Product _ a b ->
      case varBound of
        OSL.ProductBound _ (OSL.LeftBound aBound) (OSL.RightBound bBound) -> do
          (aQs, aM) <- getExistentialQuantifierStringAndMapping gc lc a aBound
          (bQs, bM) <- getExistentialQuantifierStringAndMapping gc lc b bBound
          pure
            ( aQs <> bQs,
              mergeMapping
                (\aM' bM' -> ProductMapping (LeftMapping aM') (RightMapping bM'))
                aM
                bM
            )
        _ -> lift . Left $ ErrorMessage (boundAnnotation varBound) "expected a product bound"
    OSL.Coproduct ann a b ->
      case varBound of
        OSL.CoproductBound _ (OSL.LeftBound aBound) (OSL.RightBound bBound) -> do
          let cQ = S11.someFirstOrder (S11.TermBound (S11.Const 2))
              cT = S11.var (S11.Name 0 0)
              cM = ChoiceMapping (ScalarMapping cT)
              cSym = getFreeOSLName lc
              decls' = addDeclaration cSym (OSL.FreeVariable (OSL.Fin ann 2)) decls
              lc' = TranslationContext decls' mappings
          -- TODO: can this result in overlap between cM and bM/aM?
          lc'' <-
            lift . runIdentity . runExceptT $
              execStateT (addFreeVariableMapping cSym) lc'
          (aQs, aM) <- getExistentialQuantifierStringAndMapping gc lc'' a aBound
          (bQs, bM) <- getExistentialQuantifierStringAndMapping gc lc'' b bBound
          pure
            ( [cQ] <> aQs <> bQs,
              mergeMapping
                (\bM' aM' -> CoproductMapping cM (LeftMapping aM') (RightMapping bM'))
                bM
                aM
            )
        _ -> lift . Left $ ErrorMessage (boundAnnotation varBound) "expected a coproduct bound"
    OSL.NamedType ann name ->
      case varBound of
        OSL.ToBound _ name' aBound ->
          if name == name'
            then case getDeclaration decls name of
              Just (OSL.Data a) ->
                getExistentialQuantifierStringAndMapping gc lc a aBound
              _ -> lift . Left $ ErrorMessage ann "expected the name of a type"
            else lift . Left $ ErrorMessage ann "named type mismatch in bound"
        OSL.ScalarBound _ _ -> scalarResult
        _ ->
          lift . Left . ErrorMessage ann $
            "expected a "
              <> pack (show name)
              <> " bound but got "
              <> pack (show varBound)
    OSL.Maybe _ a ->
      case varBound of
        OSL.MaybeBound _ (OSL.ValuesBound aBound) -> do
          let cQ = S11.someFirstOrder (S11.TermBound (S11.Const 2))
              cM = ScalarMapping (S11.var (S11.Name 0 0))
          (vQs, vM) <- getExistentialQuantifierStringAndMapping gc lc a aBound
          pure (cQ : vQs, MaybeMapping (ChoiceMapping cM) (ValuesMapping vM))
        _ -> lift . Left $ ErrorMessage (boundAnnotation varBound) "expected a maybe bound"
    OSL.List ann (OSL.Cardinality n) a ->
      case varBound of
        OSL.ListBound _ (OSL.ValuesBound aBound) -> do
          let lQ = S11.someFirstOrder (S11.TermBound (S11.Const n))
              lT = S11.var (S11.Name 0 0)
              lSym = getFreeOSLName lc
              decls' = addDeclaration lSym (OSL.FreeVariable (OSL.N ann)) decls
              lc' = TranslationContext decls' mappings
          lc'' <-
            lift . runIdentity . runExceptT $
              execStateT (addFreeVariableMapping lSym) lc'
          (vQs, vM) <-
            getExistentialQuantifierStringAndMapping
              gc
              lc''
              (OSL.F ann (Just (OSL.Cardinality n)) (OSL.N ann) a)
              ( OSL.FunctionBound
                  ann
                  (OSL.DomainBound (OSL.ScalarBound ann (OSL.NamedTerm ann lSym)))
                  (OSL.CodomainBound aBound)
              )
          pure
            ( lQ : vQs,
              ListMapping
                (LengthMapping (ScalarMapping lT))
                (ValuesMapping vM)
            )
        _ -> lift . Left $ ErrorMessage (boundAnnotation varBound) "expected a list bound"
    OSL.Map ann (OSL.Cardinality n) a b ->
      case varBound of
        OSL.MapBound _ (OSL.KeysBound aBound) (OSL.ValuesBound bBound) -> do
          (kQs, kM) <-
            getExistentialQuantifierStringAndMapping
              gc
              lc
              (OSL.List ann (OSL.Cardinality n) a)
              (OSL.ListBound ann (OSL.ValuesBound aBound))
          (vQs, vM) <-
            getExistentialQuantifierStringAndMapping
              gc
              lc
              (OSL.F ann (Just (OSL.Cardinality n)) a b)
              ( OSL.FunctionBound
                  ann
                  (OSL.DomainBound aBound)
                  (OSL.CodomainBound bBound)
              )
          pure
            ( kQs <> vQs,
              mergeMapping
                ( curry
                    ( \case
                        ( ListMapping (LengthMapping lM) (ValuesMapping kM''),
                          vM''
                          ) ->
                            MapMapping
                              (LengthMapping lM)
                              (KeysMapping kM'')
                              (ValuesMapping vM'')
                        d ->
                          die $
                            "logical impossibility in map quantifier translation: "
                              <> pack (show d)
                    )
                )
                kM
                vM
            )
        _ -> lift . Left $ ErrorMessage ann "expected a map bound"
  where
    scalarResult =
      case varBound of
        OSL.ScalarBound _ _ -> do
          bTs <- translateBound gc lc varType (Just varBound)
          case bTs of
            [bT] ->
              pure
                ( [S11.someFirstOrder bT],
                  ScalarMapping (S11.var (S11.Name 0 0))
                )
            _ ->
              lift . Left . ErrorMessage (boundAnnotation varBound) $
                "expected a scalar bound but got " <> pack (show bTs)
        OSL.FieldMaxBound _ ->
          pure
            ( [S11.someFirstOrder S11.FieldMaxBound],
              ScalarMapping (S11.var (S11.Name 0 0))
            )
        _ ->
          lift . Left . ErrorMessage (boundAnnotation varBound) $
            "expected a scalar bound but got " <> pack (show varBound)

getMappingDimensions ::
  OSL.ValidContext t ann ->
  OSL.Type ann ->
  Either (ErrorMessage ann) MappingDimensions
getMappingDimensions ctx t =
  case t of
    OSL.Prop ann -> Left (ErrorMessage ann "expected a quantifiable type; got Prop")
    OSL.F _ _ _ _ -> pure InfiniteDimensions
    OSL.P _ _ _ _ -> pure InfiniteDimensions
    OSL.N _ -> pure (FiniteDimensions 1)
    OSL.Z _ -> pure (FiniteDimensions 1)
    OSL.Fp _ -> pure (FiniteDimensions 1)
    OSL.Fin _ _ -> pure (FiniteDimensions 1)
    OSL.Product _ a b ->
      (<>)
        <$> getMappingDimensions ctx a
        <*> getMappingDimensions ctx b
    OSL.Coproduct _ a b ->
      (FiniteDimensions 1 <>)
        <$> ( (<>)
                <$> getMappingDimensions ctx a
                <*> getMappingDimensions ctx b
            )
    OSL.Maybe _ a ->
      (FiniteDimensions 1 <>) <$> getMappingDimensions ctx a
    OSL.NamedType ann a ->
      case getDeclaration ctx a of
        Just (OSL.Data b) -> getMappingDimensions ctx b
        _ -> Left (ErrorMessage ann "expected the name of a type")
    OSL.List _ _ _ -> pure InfiniteDimensions
    OSL.Map _ _ _ _ -> pure InfiniteDimensions

getArbitraryMapping ::
  OSL.ValidContext t ann ->
  OSL.Type ann ->
  Either (ErrorMessage ann) (Mapping ann S11.Term)
getArbitraryMapping ctx =
  \case
    OSL.Prop _ -> pure $ PropMapping (S11.Equal (S11.Const 0) (S11.Const 1))
    OSL.N _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Z _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Fp _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Fin _ _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Product _ a b ->
      ProductMapping
        <$> (LeftMapping <$> rec a)
        <*> (RightMapping <$> rec b)
    OSL.Coproduct _ a b ->
      CoproductMapping (ChoiceMapping (ScalarMapping (S11.Const 0)))
        <$> (LeftMapping <$> rec a)
        <*> (RightMapping <$> rec b)
    OSL.Maybe _ a ->
      MaybeMapping (ChoiceMapping (ScalarMapping (S11.Const 0)))
        . ValuesMapping
        <$> rec a
    OSL.NamedType ann a ->
      case getDeclaration ctx a of
        Just (OSL.Data b) -> rec b
        Just _ -> Left (ErrorMessage ann "expected the name of a type")
        Nothing -> Left (ErrorMessage ann "undefined name")
    OSL.List ann n a ->
      ListMapping
        <$> (LengthMapping <$> rec (OSL.N ann))
        <*> (ValuesMapping <$> rec (OSL.F ann (Just n) (OSL.N ann) a))
    OSL.Map ann n a b ->
      MapMapping
        <$> (LengthMapping <$> rec (OSL.N ann))
        <*> (KeysMapping <$> rec a)
        <*> (ValuesMapping <$> rec (OSL.F ann (Just n) a b))
    OSL.F ann _ a b ->
      case getMappingDimensions ctx a of
        Left err -> Left err
        Right (FiniteDimensions m) ->
          incrementArities m <$> getArbitraryMapping ctx b
        Right InfiniteDimensions ->
          Left (ErrorMessage ann "expected a finite-dimensional domain type")
    OSL.P _ _ _ _ -> pure $ ScalarMapping (S11.var (S11.Name 1 0))
  where
    rec = getArbitraryMapping ctx

translateToMapping ::
  Show ann =>
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Type ann ->
  OSL.Term ann ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) (Mapping ann S11.Term)
translateToMapping gc lc tType t = do
  trans <- translate gc lc tType t
  case trans of
    Mapping m -> pure m
    Term t' -> pure (ScalarMapping t')
    Formula p -> pure (PropMapping p)

translateToTerm ::
  Show ann =>
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Type ann ->
  OSL.Term ann ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) S11.Term
translateToTerm gc lc tType t = do
  trans <- translate gc lc tType t
  case trans of
    Term t' -> return t'
    Mapping m -> lift $ mappingToTerm (termAnnotation t) m
    m ->
      lift . Left . ErrorMessage (termAnnotation t) $
        "expected a term or scalar mapping; got: " <> pack (show m)

translateToFormula ::
  Show ann =>
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Term ann ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) S11.Formula
translateToFormula gc lc@(TranslationContext decls mappings) t = do
  trans <- translate gc lc (OSL.Prop (termAnnotation t)) t
  case trans of
    Formula f -> pure f
    Mapping (PropMapping f) -> pure f
    Mapping (LambdaMapping _ _ _ _ _) ->
      case t of
        OSL.Lambda _ varName varType body -> do
          let decls' = addDeclaration varName (OSL.FreeVariable varType) decls
              lc' = TranslationContext decls' mappings
          lc'' <-
            lift . runIdentity . runExceptT $
              execStateT (addFreeVariableMapping varName) lc'
          translateToFormula gc lc'' body
        _ ->
          lift . Left $
            ErrorMessage
              (termAnnotation t)
              "lambda mapping for a non-lambda (this is a compiler bug)"
    _ ->
      lift . Left $
        ErrorMessage
          (termAnnotation t)
          "expected a term denoting a Prop"

mappingToTerm ::
  Show ann =>
  ann ->
  Mapping ann S11.Term ->
  Either (ErrorMessage ann) S11.Term
mappingToTerm ann =
  \case
    ScalarMapping t -> pure t
    m ->
      Left . ErrorMessage ann $
        "expected a mapping denoting a scalar but got "
          <> pack (show m)

applyMappings ::
  Show ann =>
  ann ->
  OSL.Type ann ->
  Mapping ann S11.Term ->
  Mapping ann S11.Term ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) (Mapping ann S11.Term)
applyMappings ann goalType f x =
  case (f, x) of
    (LambdaMapping gc lc v _ t, _) -> do
      lc' <-
        lift . runIdentity . runExceptT $
          execStateT (addTermMapping v x) lc
      translateToMapping gc lc' goalType t
    (ScalarMapping f', ScalarMapping x') ->
      lift $ ScalarMapping <$> applyTerms ann f' x'
    (ScalarMapping _, ProductMapping (LeftMapping x') (RightMapping y')) -> do
      f' <- rec f x'
      rec f' y'
    ( ScalarMapping _,
      CoproductMapping
        (ChoiceMapping cM)
        (LeftMapping lM)
        (RightMapping rM)
      ) -> do
        f' <- rec f cM
        f'' <- rec f' lM
        rec f'' rM
    ( ScalarMapping _,
      MaybeMapping
        (ChoiceMapping cM)
        (ValuesMapping vM)
      ) -> do
        f' <- rec f cM
        rec f' vM
    (ListMapping (LengthMapping lM) (ValuesMapping vM), _) ->
      ListMapping (LengthMapping lM) . ValuesMapping
        <$> rec vM x
    (MapMapping (LengthMapping lM) (KeysMapping kM) (ValuesMapping vM), _) ->
      -- TODO: why this?
      MapMapping (LengthMapping lM) (KeysMapping kM)
        . ValuesMapping
        <$> rec vM x
    ( CoproductMapping
        (ChoiceMapping cM)
        (LeftMapping lM)
        (RightMapping rM),
      _
      ) ->
        CoproductMapping
          <$> (ChoiceMapping <$> rec cM x)
          <*> (LeftMapping <$> rec lM x)
          <*> (RightMapping <$> rec rM x)
    (ProductMapping (LeftMapping g) (RightMapping h), x') ->
      ProductMapping
        <$> (LeftMapping <$> rec g x')
        <*> (RightMapping <$> rec h x')
    (MaybeMapping (ChoiceMapping g) (ValuesMapping h), x') ->
      MaybeMapping
        <$> (ChoiceMapping <$> rec g x')
        <*> (ValuesMapping <$> rec h x')
    ( FunctionCoproductMapping (LeftMapping g) (RightMapping h),
      CoproductMapping (ChoiceMapping a) (LeftMapping b) (RightMapping c)
      ) -> do
        aT <- lift $ mappingToTerm ann a
        bT <- lift . mappingToTerm ann =<< applyMappings ann goalType g b
        cT <- lift . mappingToTerm ann =<< applyMappings ann goalType h c
        pure . ScalarMapping $
          S11.Add
            (S11.Mul aT bT)
            ( S11.Mul
                ( S11.Add
                    (S11.Const 1)
                    (S11.Mul (S11.Const (-1)) aT)
                )
                cT
            )
    (PredicateMapping p, xM) -> do
      pure . PropMapping . S11.Predicate p $
        linearizeMapping xM
    _ -> lift . Left $ ErrorMessage ann ("unable to apply mappings:\n" <> pack (show f) <> "\n<---\n" <> pack (show x))
  where
    rec = applyMappings ann goalType

applyTerms ::
  ann ->
  S11.Term ->
  S11.Term ->
  Either (ErrorMessage ann) S11.Term
applyTerms ann f x =
  case f of
    S11.App f' ys -> pure $ S11.App f' (ys <> [x])
    _ ->
      Left $
        ErrorMessage
          ann
          ("expected a function term; got " <> pack (show f))

translateBound ::
  Show ann =>
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Type ann ->
  Maybe (OSL.Bound ann) ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) [S11.Bound]
translateBound gc lc@(TranslationContext decls _) t =
  \case
    Just (OSL.ScalarBound _ term) ->
      (: []) . S11.TermBound <$> translateToTerm gc lc t term
    Just (OSL.FieldMaxBound _) -> pure [S11.FieldMaxBound]
    Just (OSL.ProductBound ann (OSL.LeftBound aBound) (OSL.RightBound bBound)) ->
      case t of
        OSL.Product _ a b ->
          (<>)
            <$> translateBound gc lc a (Just aBound)
            <*> translateBound gc lc b (Just bBound)
        _ -> lift . Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.ToBound ann name bound) ->
      case getDeclaration decls name of
        Just (OSL.Data a) -> translateBound gc lc a (Just bound)
        Just _ -> lift . Left . ErrorMessage ann $ "expected the name of a type"
        Nothing -> lift . Left . ErrorMessage ann $ "undefined name"
    Just (OSL.CoproductBound ann (OSL.LeftBound aBound) (OSL.RightBound bBound)) ->
      case t of
        OSL.Coproduct _ a b ->
          (<>)
            <$> translateBound gc lc a (Just aBound)
            <*> translateBound gc lc b (Just bBound)
        _ -> lift . Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just
      ( OSL.FunctionBound
          ann
          (OSL.DomainBound aBound)
          (OSL.CodomainBound bBound)
        ) ->
        case t of
          OSL.F _ _ a b ->
            (<>)
              <$> translateBound gc lc a (Just aBound)
              <*> translateBound gc lc b (Just bBound)
          _ -> lift . Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.ListBound ann (OSL.ValuesBound vBound)) ->
      case t of
        OSL.List ann' n'@(OSL.Cardinality n) a ->
          let lBound = OSL.ScalarBound ann' (OSL.ConstN ann n)
           in (<>)
                <$> translateBound gc lc (OSL.N ann') (Just lBound)
                <*> translateBound
                  gc
                  lc
                  (OSL.F ann' (Just n') (OSL.N ann') a)
                  ( Just
                      ( OSL.FunctionBound
                          ann
                          (OSL.DomainBound lBound)
                          (OSL.CodomainBound vBound)
                      )
                  )
        _ -> lift . Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.MaybeBound ann (OSL.ValuesBound vBound)) ->
      case t of
        OSL.Maybe _ a ->
          ((S11.TermBound (S11.Const 2)) :) <$> translateBound gc lc a (Just vBound)
        _ -> lift . Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just
      ( OSL.MapBound
          ann
          (OSL.KeysBound kBound)
          (OSL.ValuesBound vBound)
        ) ->
        case t of
          OSL.Map ann' n'@(OSL.Cardinality n) k v ->
            mconcatM
              [ translateBound gc lc (OSL.N ann') (Just (OSL.ScalarBound ann' (OSL.ConstN ann' n))),
                translateBound
                  gc
                  lc
                  (OSL.F ann' (Just n') (OSL.N ann') k)
                  ( Just
                      ( OSL.FunctionBound
                          ann'
                          (OSL.DomainBound (OSL.ScalarBound ann' (OSL.ConstN ann' n)))
                          (OSL.CodomainBound kBound)
                      )
                  ),
                translateBound
                  gc
                  lc
                  (OSL.F ann' (Just n') k (OSL.N ann'))
                  ( Just
                      ( OSL.FunctionBound
                          ann'
                          (OSL.DomainBound kBound)
                          (OSL.CodomainBound (OSL.ScalarBound ann' (OSL.ConstN ann' 2)))
                      )
                  ),
                translateBound
                  gc
                  lc
                  (OSL.F ann' (Just n') k v)
                  ( Just
                      ( OSL.FunctionBound
                          ann'
                          (OSL.DomainBound kBound)
                          (OSL.CodomainBound vBound)
                      )
                  )
              ]
          _ -> lift . Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Nothing -> translateBound gc lc t . Just =<< lift (inferBound decls t)

inferBound ::
  OSL.ValidContext t ann ->
  OSL.Type ann ->
  Either (ErrorMessage ann) (OSL.Bound ann)
inferBound ctx =
  \case
    OSL.Prop ann -> Left (ErrorMessage ann "expected a quantifiable type but got Prop")
    OSL.F ann _ a b ->
      OSL.FunctionBound ann
        <$> (OSL.DomainBound <$> inferBound ctx a)
        <*> (OSL.CodomainBound <$> inferBound ctx b)
    OSL.P ann _ a b ->
      OSL.FunctionBound ann
        <$> (OSL.DomainBound <$> inferBound ctx a)
        <*> (OSL.CodomainBound <$> inferBound ctx b)
    OSL.N ann -> Left (ErrorMessage ann "cannot infer bound for N")
    OSL.Z ann -> Left (ErrorMessage ann "cannot infer bound for Z")
    OSL.Fp ann -> pure (OSL.FieldMaxBound ann)
    OSL.Fin ann n -> pure (OSL.ScalarBound ann (OSL.ConstN ann n))
    OSL.Product ann a b ->
      OSL.ProductBound ann
        <$> (OSL.LeftBound <$> inferBound ctx a)
        <*> (OSL.RightBound <$> inferBound ctx b)
    OSL.Coproduct ann a b ->
      OSL.CoproductBound ann
        <$> (OSL.LeftBound <$> inferBound ctx a)
        <*> (OSL.RightBound <$> inferBound ctx b)
    OSL.NamedType ann name ->
      case getDeclaration ctx name of
        Just (OSL.Data a) ->
          OSL.ToBound ann name <$> inferBound ctx a
        _ -> Left (ErrorMessage ann "expected the name of a type")
    OSL.Maybe ann a ->
      OSL.MaybeBound ann . OSL.ValuesBound
        <$> inferBound ctx a
    OSL.List ann _ a ->
      OSL.ListBound ann . OSL.ValuesBound
        <$> inferBound ctx a
    OSL.Map ann _ a b ->
      OSL.MapBound ann
        <$> (OSL.KeysBound <$> inferBound ctx a)
        <*> (OSL.ValuesBound <$> inferBound ctx b)

translateEquality ::
  Show ann =>
  ann ->
  TranslationContext 'OSL.Global ann ->
  TranslationContext 'OSL.Local ann ->
  OSL.Type ann ->
  OSL.Term ann ->
  OSL.Term ann ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) S11.Formula
translateEquality ann gc lc@(TranslationContext decls _) t x y = do
  xM <- translateToMapping gc lc t x
  yM <- translateToMapping gc lc t y
  lift $ applyEqualityToMappings ann decls t x xM y yM

applyEqualityToMappings ::
  Show ann =>
  ann ->
  OSL.ValidContext t ann ->
  OSL.Type ann ->
  OSL.Term ann ->
  Mapping ann S11.Term ->
  OSL.Term ann ->
  Mapping ann S11.Term ->
  Either (ErrorMessage ann) S11.Formula
applyEqualityToMappings ann ctx t xSrc x ySrc y =
  case (x, y, t) of
    (_, _, OSL.NamedType ann' name) ->
      case getDeclaration ctx name of
        Just (OSL.Data a) -> rec a x y
        _ -> Left (ErrorMessage ann' "expected the name of a type")
    (ScalarMapping xT, ScalarMapping yT, _) ->
      pure (S11.Equal xT yT)
    ( ProductMapping (LeftMapping xlM) (RightMapping xrM),
      ProductMapping (LeftMapping ylM) (RightMapping yrM),
      OSL.Product _ a b
      ) ->
        S11.And
          <$> rec a xlM ylM
          <*> rec b xrM yrM
    ( CoproductMapping
        (ChoiceMapping (ScalarMapping xcM))
        (LeftMapping xlM)
        (RightMapping xrM),
      CoproductMapping
        (ChoiceMapping (ScalarMapping ycM))
        (LeftMapping ylM)
        (RightMapping yrM),
      OSL.Coproduct _ a b
      ) ->
        S11.And (S11.Equal xcM ycM)
          <$> ( S11.Or
                  <$> ( S11.And (S11.Equal xcM (S11.Const 0))
                          <$> rec a xlM ylM
                      )
                  <*> ( S11.And (S11.Equal xcM (S11.Const 1))
                          <$> rec b xrM yrM
                      )
              )
    ( MaybeMapping
        (ChoiceMapping (ScalarMapping xcM))
        (ValuesMapping xvM),
      MaybeMapping
        (ChoiceMapping (ScalarMapping ycM))
        (ValuesMapping yvM),
      OSL.Maybe _ a
      ) ->
        S11.And (S11.Equal xcM ycM)
          . S11.Or (S11.Equal xcM (S11.Const 0))
          <$> rec a xvM yvM
    _ ->
      Left . ErrorMessage ann $
        "cannot compare these things for equality: "
          <> pack (show (xSrc, x, ySrc, y, t))
  where
    rec a x' y' = applyEqualityToMappings ann ctx a xSrc x' ySrc y'

translateToConstant ::
  Show ann =>
  OSL.ValidContext 'OSL.Global ann ->
  OSL.ValidContext 'OSL.Local ann ->
  OSL.Type ann ->
  OSL.Term ann ->
  Either (ErrorMessage ann) (Mapping ann Integer)
translateToConstant gc lc@(OSL.ValidContext decls) termType =
  \case
    OSL.NamedTerm ann name ->
      case Map.lookup name decls of
        Just (OSL.Defined defType def) ->
          -- TODO: this is not quite right; a local context switch should occur
          translateToConstant gc lc defType def
        _ -> Left (ErrorMessage ann "expected the name of a constant")
    OSL.ConstN _ i -> pure (ScalarMapping i)
    OSL.ConstZ _ i -> pure (ScalarMapping i)
    OSL.ConstFp _ i -> pure (ScalarMapping i)
    OSL.ConstFin _ i -> pure (ScalarMapping i)
    OSL.Apply ann (OSL.Apply _ (OSL.AddN _) x) y -> do
      xs <- translateToConstant gc lc termType x
      ys <- translateToConstant gc lc termType y
      case (xs, ys) of
        (ScalarMapping x', ScalarMapping y') ->
          pure (ScalarMapping (x' + y'))
        _ -> Left $ ErrorMessage ann "+N applied to non-scalars (this is a compiler bug)"
    OSL.Apply ann (OSL.Apply _ (OSL.AddZ _) x) y -> do
      xs <- translateToConstant gc lc termType x
      ys <- translateToConstant gc lc termType y
      case (xs, ys) of
        (ScalarMapping x', ScalarMapping y') ->
          pure (ScalarMapping (x' + y'))
        _ -> Left $ ErrorMessage ann "+Z applied to non-scalars (this is a compiler bug)"
    OSL.Apply ann (OSL.Apply _ (OSL.MulN _) x) y -> do
      xs <- translateToConstant gc lc termType x
      ys <- translateToConstant gc lc termType y
      case (xs, ys) of
        (ScalarMapping x', ScalarMapping y') ->
          pure (ScalarMapping (x' * y'))
        _ -> Left $ ErrorMessage ann "*N applied to non-scalars (this is a compiler bug)"
    OSL.Apply ann (OSL.Apply _ (OSL.MulZ _) x) y -> do
      xs <- translateToConstant gc lc termType x
      ys <- translateToConstant gc lc termType y
      case (xs, ys) of
        (ScalarMapping x', ScalarMapping y') ->
          pure (ScalarMapping (x' * y'))
        _ -> Left $ ErrorMessage ann "*Z applied to non-scalars (this is a compiler bug)"
    OSL.Apply _ (OSL.Cast _) x -> do
      xType <- inferType lc x
      translateToConstant gc lc xType x
    OSL.Apply ann (OSL.Apply _ (OSL.Pair _) x) y -> do
      case termType of
        OSL.Product _ a b ->
          ProductMapping
            <$> (LeftMapping <$> translateToConstant gc lc a x)
            <*> (RightMapping <$> translateToConstant gc lc b y)
        _ ->
          Left . ErrorMessage ann $
            "unexpected pair; expected a "
              <> pack (show termType)
    OSL.Apply ann (OSL.Pi1 _) x -> do
      xType <- inferType lc x
      xT <- translateToConstant gc lc xType x
      case xT of
        ProductMapping (LeftMapping a) _ -> pure a
        _ -> Left (ErrorMessage ann "translating pi1 did not result in a product mapping; this is a compiler bug")
    OSL.Apply ann (OSL.Pi2 _) x -> do
      xType <- inferType lc x
      xT <- translateToConstant gc lc xType x
      case xT of
        ProductMapping _ (RightMapping a) -> pure a
        _ -> Left (ErrorMessage ann "translating pi2 did not result in a product mapping; this is a compiler bug")
    OSL.Apply _ (OSL.To ann' name) x -> do
      case Map.lookup name decls of
        Just (OSL.Data a) -> translateToConstant gc lc a x
        _ -> Left (ErrorMessage ann' "expected the name of a type")
    OSL.Apply _ (OSL.From ann' name) x -> do
      case Map.lookup name decls of
        Just (OSL.Data _) -> translateToConstant gc lc (OSL.NamedType ann' name) x
        _ -> Left (ErrorMessage ann' "expected the name of a type")
    t -> Left $ ErrorMessage (termAnnotation t) "sorry, I was not taught how to translate this term to a constant"

getFreeS11PredicateNameM ::
  Arity ->
  StateT S11.AuxTables (Either (ErrorMessage ann)) S11.PredicateName
getFreeS11PredicateNameM arity = do
  S11.AuxTables _ ps <- get
  pure
    . fromMaybe (S11.PredicateName arity (DeBruijnIndex 0))
    . fmap (S11.PredicateName arity . (+ 1) . (^. #deBruijnIndex))
    . Set.lookupMax
    $ Map.keysSet ps

getFreeS11NameM ::
  Arity ->
  TranslationContext 'OSL.Local ann ->
  S11.AuxTables ->
  S11.Name
getFreeS11NameM arity ctx (S11.AuxTables fs _) = do
  getFreeS11Name
    arity
    ( getBoundS11NamesInContext arity ctx
        `Set.union` Map.keysSet fs
    )

mconcatM :: Monad m => Monoid a => [m a] -> m a
mconcatM [] = return mempty
mconcatM (xM : xMs) = do
  x <- xM
  (x <>) <$> mconcatM xMs
