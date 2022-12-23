{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module OSL.Argument (toSigma11Argument) where

import Cast (intToInteger)
import Control.Lens ((^.))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified OSL.Sigma11 as S11
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Evaluation (decodeScalar)
import qualified OSL.Term as OSL
import qualified OSL.Type as OSL
import qualified OSL.Types.ArgumentForm as OSL
import qualified OSL.Types.Argument as OSL
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Value as OSL
import qualified OSL.Types.Sigma11.Argument as S11
import qualified OSL.Types.Sigma11.Value as S11
import qualified OSL.Types.Sigma11.ValueTree as S11
import qualified OSL.ValidContext as OSL
import qualified OSL.Value as OSL
import Safe (atMay)
import Stark.Types.Scalar (Scalar, zero, one, integerToScalar)

toSigma11Argument ::
  OSL.ValidContext t ann ->
  OSL.ArgumentForm ->
  OSL.Argument ->
  OSL.Term () ->
  Either (ErrorMessage ()) S11.Argument
toSigma11Argument c af a x =
  S11.Argument
    <$> toSigma11Statement c (af ^. #statementType) (a ^. #statement)
    <*> toSigma11Witness c (af ^. #witnessType) (a ^. #witness) x
toSigma11Statement ::
  OSL.ValidContext t ann ->
  OSL.StatementType ->
  OSL.Statement ->
  Either (ErrorMessage ()) S11.Statement
toSigma11Statement c (OSL.StatementType t) (OSL.Statement s) =
  S11.Statement <$> toSigma11Values c t s

scalarValue :: Scalar -> S11.Value
scalarValue = S11.Value . Map.singleton []

toSigma11Witness ::
  OSL.ValidContext t ann ->
  OSL.WitnessType ->
  OSL.Witness ->
  OSL.Term () ->
  Either (ErrorMessage ()) S11.Witness
toSigma11Witness c (OSL.WitnessType t) (OSL.Witness w) x =
  S11.Witness <$> toSigma11ValueTree gc lc mempty t w x
  where
    gc = OSL.ValidContext (c ^. #unValidContext)
    lc = OSL.ValidContext (OSL.dropDeclarationAnnotations <$> (c ^. #unValidContext))

toSigma11ValueTree ::
  OSL.ValidContext 'OSL.Global ann ->
  OSL.ValidContext 'OSL.Local () ->
  Map OSL.Name (OSL.ValidContext 'OSL.Local ()) ->
  OSL.Type () ->
  OSL.Value ->
  OSL.Term () ->
  Either (ErrorMessage ()) S11.ValueTree
toSigma11ValueTree gc lc lcs t val term =
  case (t,val,term) of
    (_, _, OSL.Apply {}) ->
      -- the logic for this case works based on the assumption
      -- that the application head is a defined term which is
      -- a Prop-valued lambda abstraction with the same number
      -- of arguments as it is applied to in the term.
      -- TODO: also support applications of set literals and names
      -- denoting set literals.
      case OSL.applicationHead term of
        OSL.NamedTerm _ name ->
          case Map.lookup name (lc ^. #unValidContext) of
            Just (OSL.Defined _ def) ->
              let lc' = case Map.lookup name lcs of
                          Just lc'' -> lc''
                          Nothing -> OSL.ValidContext (OSL.dropDeclarationAnnotations <$> (gc ^. #unValidContext)) in
              toSigma11ValueTree gc lc' lcs t val (OSL.lambdaBody (OSL.dropTermAnnotations def))
            _ -> Left (ErrorMessage () "expected application head to be the name of a defined predicate")
        _ -> Left (ErrorMessage () "expected application head to be the name of a defined predicate")
    (_, _, OSL.Let _ name a d y) ->
      let lc' = lc <> OSL.ValidContext (Map.singleton name (OSL.Defined a d))
          lcs' = Map.insert name lc lcs in
      toSigma11ValueTree gc lc' lcs' t val y
    (OSL.Product _ a b, OSL.Pair' x y, OSL.And _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.And {}) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y, OSL.Or _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.Or {}) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y, OSL.Implies _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.Implies {}) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y, OSL.Iff _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.Iff {}) -> typeMismatch
    (_, _, OSL.Equal {}) -> pure emptyTree
    (_, _, OSL.LessOrEqual {}) -> pure emptyTree
    (_, _, OSL.Top _) -> pure emptyTree
    (_, _, OSL.Bottom _) -> pure emptyTree
    (OSL.Prop _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.N _) b, OSL.Fun f, OSL.ForAll _ _ (OSL.N _) _ p) ->
      forAllScalar b f p
    (OSL.F _ _ (OSL.N _) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Z _) b, OSL.Fun f, OSL.ForAll _ _ (OSL.Z _) _ p) ->
      forAllScalar b f p
    (OSL.F _ _ (OSL.Z _) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Fp _) b, OSL.Fun f, OSL.ForAll _ _ (OSL.Fp _) _ p) ->
       forAllScalar b f p
    (OSL.F _ _ (OSL.Fp _) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Fin {}) b, OSL.Fun f, OSL.ForAll _ _ (OSL.Fin {}) _ p) ->
      forAllScalar b f p
    (OSL.F _ _ (OSL.Fin {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Product _ a b) d, OSL.Fun f, OSL.ForAll _ x (OSL.Product {}) _ p) -> do
      f' <- curryFun f
      rec (OSL.F () Nothing a (OSL.F () Nothing b d))
        (OSL.Fun f')
        -- Note that this step, and similar steps below, corrupt the input term by changing the usage of x,
        -- and also by removing any bounds on x, but none of that matters for this algorithm,
        -- where the atomic formulas and also the quantifier bounds are irrelevant.
        (OSL.ForAll () x a Nothing (OSL.ForAll () x b Nothing p))
    (OSL.F _ _ (OSL.Product {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Coproduct _ a b) d, OSL.Fun f, OSL.ForAll _ x (OSL.Coproduct {}) _ p) -> do
      defaultA <- OSL.defaultValue gc a
      defaultB <- OSL.defaultValue gc b
      f' <- curryCoproductFun (defaultA, defaultB) f
      rec (OSL.F () Nothing (OSL.N ()) (OSL.F () Nothing a (OSL.F () Nothing b d)))
        (OSL.Fun f')
        (OSL.ForAll () x (OSL.N ()) Nothing
          (OSL.ForAll () x a Nothing
            (OSL.ForAll () x b Nothing p)))
    (OSL.F _ _ (OSL.Coproduct {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Maybe _ a) b, OSL.Fun f, OSL.ForAll _ x (OSL.Maybe {}) _ p) -> do
      defaultA <- OSL.defaultValue gc a
      f' <- curryMaybeFun defaultA f
      rec (OSL.F () Nothing (OSL.N ()) (OSL.F () Nothing a b))
        (OSL.Fun f')
        (OSL.ForAll () x (OSL.N ()) Nothing (OSL.ForAll () x a Nothing p))
    (OSL.F _ _ (OSL.Maybe {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.NamedType _ name) b, OSL.Fun f, OSL.ForAll _ x (OSL.NamedType {}) _ p) ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (OSL.Data a) ->
          let f' = OSL.Fun $ Map.mapMaybe OSL.toInverse f
              a' = OSL.dropTypeAnnotations a in
          rec (OSL.F () Nothing a' b) f' (OSL.ForAll () x a' Nothing p)
        _ -> Left (ErrorMessage () "expected the name of a type")
    (OSL.F _ _ (OSL.NamedType {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Prop _) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.F {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.P {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.List {}) _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.Map {}) _, _, _) -> typeMismatch
    -- The following patterns ((_, OSL.Nat _, _), etc.) are correct because every
    -- OSL witness is either a pair, a function, or fin(0) (in which case it should
    -- be caught by an earlier pattern matching the formula, which would be an atomic formula).
    (_, OSL.Nat _, _) -> typeMismatch
    (_, OSL.Int _, _) -> typeMismatch
    (_, OSL.Fp' _, _) -> typeMismatch
    (_, OSL.Fin' {}, _) -> typeMismatch
    (_, OSL.Iota1' {}, _) -> typeMismatch
    (_, OSL.Iota2' {}, _) -> typeMismatch
    (_, OSL.To' {}, _) -> typeMismatch
    (_, OSL.Maybe'' {}, _) -> typeMismatch
    (_, OSL.List'' {}, _) -> typeMismatch
    (_, OSL.Map'' {}, _) -> typeMismatch
    (_, OSL.Bool {}, _) -> typeMismatch
    (_, OSL.Predicate {}, _) -> typeMismatch
    (OSL.Product () (OSL.Prop _) _, _, _) -> typeMismatch
    (OSL.Product () (OSL.N _) b, OSL.Pair' x y, OSL.ForSome _ _ (OSL.N _) _ p) ->
      forSomeScalar b x y p
    (OSL.Product () (OSL.N _) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product () (OSL.Z _) b, OSL.Pair' x y, OSL.ForSome _ _ (OSL.Z _) _ p) ->
      forSomeScalar b x y p
    (OSL.Product () (OSL.Z _) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product () (OSL.Fp _) b, OSL.Pair' x y, OSL.ForSome _ _ (OSL.Fp _) _ p) ->
      forSomeScalar b x y p
    (OSL.Product () (OSL.Fp _) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product () (OSL.Fin {}) b, OSL.Pair' x y, OSL.ForSome _ _ (OSL.Fin {}) _ p) ->
      forSomeScalar b x y p
    (OSL.Product () (OSL.Fin {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product () (OSL.Product _ a b) d, OSL.Pair' (OSL.Pair' x y) z, OSL.ForSome ann v (OSL.Product {}) _ p) ->
      rec (OSL.Product () a (OSL.Product () b d))
        (OSL.Pair' x (OSL.Pair' y z))
        (OSL.ForSome ann v a Nothing (OSL.ForSome ann v b Nothing p))
    (OSL.Product () (OSL.Product {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product _ (OSL.Coproduct _ a b) d, OSL.Pair' (OSL.Iota1' x) y, OSL.ForSome ann v (OSL.Coproduct {}) _ p) -> do
      defaultB <- OSL.defaultValue gc b
      rec (OSL.Product () (OSL.N ()) (OSL.Product () a (OSL.Product () b d)))
        (OSL.Pair' (OSL.Nat zero) (OSL.Pair' x (OSL.Pair' defaultB y)))
        (OSL.ForSome ann v (OSL.N ()) Nothing
          (OSL.ForSome ann v a Nothing
            (OSL.ForSome ann v b Nothing p)))
    (OSL.Product _ (OSL.Coproduct _ a b) d, OSL.Pair' (OSL.Iota2' x) y, OSL.ForSome ann v (OSL.Coproduct {}) _ p) -> do
      defaultA <- OSL.defaultValue gc a
      rec (OSL.Product () (OSL.N ()) (OSL.Product () a (OSL.Product () b d)))
        (OSL.Pair' (OSL.Nat one) (OSL.Pair' defaultA (OSL.Pair' x y)))
        (OSL.ForSome ann v (OSL.N ()) Nothing
          (OSL.ForSome ann v a Nothing
            (OSL.ForSome ann v b Nothing p)))
    (OSL.Product () (OSL.Coproduct {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product _ (OSL.Maybe _ a) b, OSL.Pair' (OSL.Maybe'' Nothing) y, OSL.ForSome ann v (OSL.Maybe {}) _ p) -> do
      defaultA <- OSL.defaultValue gc a
      rec (OSL.Product () (OSL.N ()) (OSL.Product () a b))
        (OSL.Pair' (OSL.Nat zero) (OSL.Pair' defaultA y))
        (OSL.ForSome ann v (OSL.N ()) Nothing
          (OSL.ForSome ann v a Nothing p))
    (OSL.Product _ (OSL.Maybe _ a) b, OSL.Pair' (OSL.Maybe'' (Just x)) y, OSL.ForSome ann v (OSL.Maybe {}) _ p) -> do
      rec (OSL.Product () (OSL.N ()) (OSL.Product () a b))
        (OSL.Pair' (OSL.Nat one) (OSL.Pair' x y))
        (OSL.ForSome ann v (OSL.N ()) Nothing
          (OSL.ForSome ann v a Nothing p))
    (OSL.Product _ (OSL.Maybe {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product _ (OSL.List _ _ a) b, OSL.Pair' (OSL.List'' xs) y, OSL.ForSome ann v (OSL.List {}) _ p) -> do
      n <- fromInt (length xs)
      f <- OSL.Fun . Map.fromList <$> sequence
           [ (,x) . OSL.Nat <$> fromInt i
           | (i,x) <- zip [0..] xs
           ]
      rec (OSL.Product () (OSL.N ()) (OSL.Product () (OSL.F () Nothing (OSL.N ()) a) b))
        (OSL.Pair' (OSL.Nat n) (OSL.Pair' f y))
        (OSL.ForSome ann v (OSL.N ann) Nothing
          (OSL.ForSome ann v (OSL.F ann Nothing (OSL.N ()) a) Nothing p))
    (OSL.Product _ (OSL.List {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product _ (OSL.Map _ _ a b) d, OSL.Pair' (OSL.Map'' m) y, OSL.ForSome ann v (OSL.Map {}) _ p) -> do
      n <- OSL.Nat <$> fromInt (Map.size m)
      ks <- OSL.Fun . Map.fromList <$> sequence
            [ (,x) . OSL.Nat <$> fromInt i
            | (i,x) <- zip [0..] (Map.keys m)
            ]
      rec
        (OSL.Product () (OSL.N ())
          (OSL.Product () (OSL.F () Nothing (OSL.N ()) a)
            (OSL.Product () (OSL.F () Nothing a b) d)))
        (OSL.Pair' n (OSL.Pair' ks (OSL.Pair' (OSL.Fun m) y)))
        (OSL.ForSome ann v (OSL.N ann) Nothing
          (OSL.ForSome ann v (OSL.F ann Nothing (OSL.N ann) a) Nothing
            (OSL.ForSome ann v (OSL.F ann Nothing a b) Nothing p)))
    (OSL.Product _ (OSL.Map {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case
    (OSL.Product _ (OSL.NamedType _ name) b, OSL.Pair' (OSL.To' _ x) y, OSL.ForSome ann v (OSL.NamedType {}) _ p) ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (OSL.Data a) ->
          let a' = OSL.dropTypeAnnotations a in
          rec (OSL.Product () a' b) (OSL.Pair' x y) (OSL.ForSome ann v a' Nothing p)
        _ -> Left (ErrorMessage () "expected the name of a type")
    (OSL.Product _ (OSL.NamedType {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case; careful moving it
    (OSL.Product _ (OSL.F _ _ a (OSL.N _)) b, OSL.Pair' (OSL.Fun f) y, OSL.ForSome _ _ (OSL.F {}) _ p) ->
      forSomeScalarFun a (OSL.N ()) b f y p
    (OSL.Product _ (OSL.F _ _ a (OSL.Z _)) b, OSL.Pair' (OSL.Fun f) y, OSL.ForSome _ _ (OSL.F {}) _ p) ->
      forSomeScalarFun a (OSL.Z ()) b f y p
    (OSL.Product _ (OSL.F _ _ a (OSL.Fp _)) b, OSL.Pair' (OSL.Fun f) y, OSL.ForSome _ _ (OSL.F {}) _ p) ->
      forSomeScalarFun a (OSL.Fp ()) b f y p
    (OSL.Product _ (OSL.F _ _ a (OSL.Fin _ n)) b, OSL.Pair' (OSL.Fun f) y, OSL.ForSome _ _ (OSL.F {}) _ p) ->
      forSomeScalarFun a (OSL.Fin () n) b f y p
    (OSL.Product _ (OSL.F _ _ a (OSL.Product _ b d)) e, OSL.Pair' (OSL.Fun f) y, OSL.ForSome ann v (OSL.F {}) _ p) -> do
      let f0 = OSL.Fun $ Map.mapMaybe OSL.fstOfPairMay f
          f1 = OSL.Fun $ Map.mapMaybe OSL.sndOfPairMay f
      rec
        (OSL.Product () (OSL.F () Nothing a b)
          (OSL.Product () (OSL.F () Nothing a d) e))
        (OSL.Pair' f0 (OSL.Pair' f1 y))
        (OSL.ForSome ann v (OSL.F ann Nothing a b) Nothing
          (OSL.ForSome ann v (OSL.F ann Nothing a d) Nothing p))
    (OSL.Product _ (OSL.F _ _ a (OSL.List _ _ b)) d, OSL.Pair' (OSL.Fun f) y, OSL.ForSome ann v (OSL.F {}) _ p) ->
      let fLengths = OSL.Fun $ Map.mapMaybe OSL.listLength f
          fValues = OSL.Fun $ Map.mapMaybe OSL.listFun f in
      rec
        (OSL.Product () (OSL.F () Nothing a (OSL.N ()))
          (OSL.Product () (OSL.F () Nothing a (OSL.F () Nothing (OSL.N ()) b)) d))
        (OSL.Pair' fLengths (OSL.Pair' fValues y))
        (OSL.ForSome ann v (OSL.F ann Nothing a (OSL.N ann)) Nothing
          (OSL.ForSome ann v (OSL.F ann Nothing a (OSL.F ann Nothing (OSL.N ann) b)) Nothing p))
    (OSL.Product _ (OSL.F _ _ a (OSL.Map _ _ b d)) e, OSL.Pair' (OSL.Fun f) y, OSL.ForSome ann v (OSL.F {}) _ p) ->
      let fSizes = OSL.Fun $ Map.mapMaybe OSL.mapSize f
          fKeys = OSL.Fun $ Map.mapMaybe OSL.mapKeys f
          fValues = OSL.Fun $ Map.mapMaybe OSL.mapFun f in
      rec
        (OSL.Product () (OSL.F () Nothing a (OSL.N ()))
          (OSL.Product () (OSL.F () Nothing a (OSL.F () Nothing (OSL.N ()) b))
            (OSL.Product () (OSL.F () Nothing a (OSL.F () Nothing a b)) e)))
        (OSL.Pair' fSizes (OSL.Pair' fKeys (OSL.Pair' fValues y)))
        (OSL.ForSome ann v (OSL.F ann Nothing a (OSL.N ann)) Nothing
          (OSL.ForSome ann v (OSL.F ann Nothing a (OSL.F ann Nothing (OSL.N ann) a)) Nothing
            (OSL.ForSome ann v (OSL.F ann Nothing a (OSL.F ann Nothing b d)) Nothing p)))
    (OSL.Product _ (OSL.F _ _ a (OSL.F _ _ b d)) e, OSL.Pair' (OSL.Fun f) y, OSL.ForSome _ v (OSL.F {}) _ p) ->
      rec
        (OSL.Product () (OSL.F () Nothing (OSL.Product () a b) d) e)
        (OSL.Pair' (OSL.Fun (OSL.uncurryFun f)) y)
        (OSL.ForSome () v (OSL.F () Nothing (OSL.Product () a b) d) Nothing p)
    (OSL.Product _ (OSL.F {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case; careful moving it
    (OSL.Product _ (OSL.P _ _ a b) d, OSL.Pair' (OSL.Fun f) y, OSL.ForSome _ _ (OSL.P {}) _ p) ->
      forSomeScalarFun a b d f y p
    (OSL.Product _ (OSL.P {}) _, _, _) -> typeMismatch -- NOTE: this is a fallthrough case; careful moving it
    (OSL.P {}, _, _) -> typeMismatch
    (OSL.N {}, _, _) -> typeMismatch
    (OSL.Z {}, _, _) -> typeMismatch
    (OSL.Fp {}, _, _) -> typeMismatch
    (OSL.Fin {}, _, _) -> typeMismatch
    (OSL.Coproduct {}, _, _) -> typeMismatch
    (OSL.NamedType {}, _, _) -> typeMismatch
    (OSL.Maybe {}, _, _) -> typeMismatch
    (OSL.List {}, _, _) -> typeMismatch
    (OSL.Map {}, _, _) -> typeMismatch
  where
    rec = toSigma11ValueTree gc lc lcs

    pairTree x y = S11.ValueTree Nothing [x, y]

    emptyTree = S11.ValueTree Nothing []

    forAllScalar b f p =
      -- we are relying on Map.elems outputting the elements in ascending
      -- order of their keys
      S11.ValueTree Nothing <$> sequence
        [ rec b y p | y <- Map.elems f ]

    forSomeScalar b x y p =
      S11.ValueTree <$> (Just . S11.Value . Map.singleton [] <$> decodeScalar () x)
                    <*> ((:[]) <$> rec b y p)

    forSomeScalarFun a b d f y p = do
      f' <- toSigma11Values lc (OSL.F () Nothing a b) (OSL.Fun f)
      case f' of
        [f''] -> S11.ValueTree (Just f'') . (:[]) <$> rec d y p
        _ -> Left (ErrorMessage () "forSomeScalarFun: pattern match failure (this is a compiler bug)")

curryFun :: Map OSL.Value OSL.Value -> Either (ErrorMessage ()) (Map OSL.Value OSL.Value)
curryFun f =
  fmap OSL.Fun . Map.unionsWith (<>) <$> sequence
    [ case x of
        OSL.Pair' x0 x1 -> pure (Map.singleton x0 (Map.singleton x1 y))
        _ -> typeMismatch
    | (x,y) <- Map.toList f
    ]

curryCoproductFun :: (OSL.Value, OSL.Value) -> Map OSL.Value OSL.Value -> Either (ErrorMessage ()) (Map OSL.Value OSL.Value)
curryCoproductFun (defaultLeft, defaultRight) f =
  fmap OSL.Fun . fmap (fmap OSL.Fun) . Map.unionsWith (Map.unionWith (<>)) <$> sequence
    [ case x of
        OSL.Iota1' x' -> pure (Map.singleton (OSL.Nat zero) (Map.singleton x' (Map.singleton defaultRight y)))
        OSL.Iota2' x' -> pure (Map.singleton (OSL.Nat one) (Map.singleton defaultLeft (Map.singleton x' y)))
        _ -> typeMismatch
    | (x,y) <- Map.toList f
    ]

curryMaybeFun :: OSL.Value -> Map OSL.Value OSL.Value -> Either (ErrorMessage ()) (Map OSL.Value OSL.Value)
curryMaybeFun defaultValue f =
  fmap OSL.Fun . Map.unionsWith (<>) <$> sequence
    [ case x of
        OSL.Maybe'' Nothing -> pure (Map.singleton (OSL.Nat zero) (Map.singleton defaultValue y))
        OSL.Maybe'' (Just x') -> pure (Map.singleton (OSL.Nat one) (Map.singleton x' y))
        _ -> typeMismatch
    | (x,y) <- Map.toList f
    ]

toSigma11Values ::
  OSL.ValidContext t ann ->
  OSL.Type () ->
  OSL.Value ->
  Either (ErrorMessage ()) [S11.Value]
toSigma11Values c t v =
  case (t, v) of
    (OSL.N _, OSL.Nat x) -> pure [scalarValue x]
    (OSL.N _, _) -> typeMismatch
    (OSL.Z _, OSL.Int x) -> pure [scalarValue x]
    (OSL.Z _, _) -> typeMismatch
    (OSL.Fp _, OSL.Fp' x) -> pure [scalarValue x]
    (OSL.Fp _, _) -> typeMismatch
    (OSL.Fin {}, OSL.Fin' x) -> pure [scalarValue x]
    (OSL.Fin {}, _) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y) ->
      (<>) <$> rec a x <*> rec b y
    (OSL.Product {}, _) -> typeMismatch
    (OSL.Coproduct _ a b, OSL.Iota1' x) ->
      mconcat <$> sequence
        [ pure [scalarValue zero],
          rec a x,
          defaultSigma11Values c b
        ]
    (OSL.Coproduct _ a b, OSL.Iota2' x) ->
      mconcat <$> sequence
        [ pure [scalarValue one],
          defaultSigma11Values c a,
          rec b x
        ]
    (OSL.Coproduct {}, _) -> typeMismatch
    (OSL.F _ _ a (OSL.N ann), f) ->
      scalarFunction a (OSL.N ann) f
    (OSL.F _ _ a (OSL.Z ann), f) ->
      scalarFunction a (OSL.Z ann) f
    (OSL.F _ _ a (OSL.Fin n ann), f) ->
      scalarFunction a (OSL.Fin n ann) f
    (OSL.F _ _ a (OSL.Fp ann), f) ->
      scalarFunction a (OSL.Fp ann) f
    (OSL.F ann n a (OSL.Product _ b d), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a b) . OSL.Fun =<< mapM OSL.fstOfPair f,
          rec (OSL.F ann n a d) . OSL.Fun =<< mapM OSL.sndOfPair f
        ]
    (OSL.F _ _ _ (OSL.Product {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.Coproduct _ b d), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) . OSL.Nat <$> iotaIndex y
              | (x, y) <- Map.toList f
              ],
          rec (OSL.F ann n a b) . OSL.Fun . Map.fromList . catMaybes $
            [ case y of
                OSL.Iota1' y' -> pure (x, y')
                _ -> Nothing
            | (x,y) <- Map.toList f
            ],
          rec (OSL.F ann n a d) . OSL.Fun . Map.fromList . catMaybes $
            [ case y of
                OSL.Iota2' y' -> pure (x, y')
                _ -> Nothing
            | (x,y) <- Map.toList f
            ]
        ]
    (OSL.F _ _ _ (OSL.Coproduct {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.Maybe _ b), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) . OSL.Nat <$> maybeIndex y
              | (x,y) <- Map.toList f
              ],
          do rec (OSL.F ann n a b) . OSL.Fun . Map.fromList
               =<< sequence
                 [ case y of
                     OSL.Maybe'' (Just y') -> pure (x, y')
                     OSL.Maybe'' Nothing -> (x,) <$> OSL.defaultValue c b
                     _ -> Left (ErrorMessage () "expected a maybe value")
                 | (x, y) <- Map.toList f
                 ]
        ]
    (OSL.F _ _ _ (OSL.Maybe {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.NamedType _ name), OSL.Fun f) ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data b) ->
          rec (OSL.F ann n a (OSL.dropTypeAnnotations b)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> fromTo y
              | (x,y) <- Map.toList f
              ]
        _ -> Left . ErrorMessage () $ "expected the name of a type"
    (OSL.F _ _ _ (OSL.NamedType {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.List _ m b), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> OSL.Nat <$> listLength y
              | (x,y) <- Map.toList f
              ],
          rec (OSL.F ann n a (OSL.F ann (Just m) (OSL.N ann) b)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> listElems y
              | (x,y) <- Map.toList f
              ]
        ]
    (OSL.F _ _ _ (OSL.List {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.Map _ m b d), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> OSL.Nat <$> mapSize y
              | (x,y) <- Map.toList f
              ],
          rec (OSL.F ann n a (OSL.F ann (Just m) (OSL.N ann) b)) . OSL.Fun . Map.fromList
            =<< sequence
              [ do ks <- mapKeys g
                   (x,) . OSL.Fun . Map.fromList <$> sequence
                     [ (,y) . OSL.Nat <$> fromInt i
                     | (i,y) <- zip [0..] ks
                     ]
              | (x,g) <- Map.toList f
              ],
          rec (OSL.F ann n a (OSL.F ann (Just m) b d)) (OSL.Fun f)
        ]
    (OSL.F _ _ _ (OSL.Map {}), _) -> typeMismatch
    (OSL.F ann _ a (OSL.F _ m b d), OSL.Fun f) -> do
      xs <- Map.fromList <$> sequence
        [(x,) <$> (toScalars =<< rec a x) | x <- Map.keys f]
      fs <- mapM (rec (OSL.F ann m b d)) f
      case Map.toList fs of
        (fs0:_) ->
          pure 
            [ S11.Value . Map.fromList $
              [ (x' <> y, z)
              | (x',fs') <- Map.elems (Map.intersectionWith (,) xs fs),
                (y,z) <- Map.toList . (^. #unValue) $ fromMaybe mempty (fs' `atMay` i)
              ]
            | i <- [0 .. length fs0 - 1]
            ]
        _ -> pure mempty
    (OSL.F _ _ _ (OSL.F {}), _) -> typeMismatch
    (OSL.F _ _ _ (OSL.P {}), _) ->
      Left . ErrorMessage () $ "unsupported: family of permutations"
    (OSL.F _ _ _ (OSL.Prop _), _) ->
      Left . ErrorMessage () $ "unsupported: Prop in function codomain"
    (OSL.P _ _ a b, f) ->
      scalarFunction a b f
    (OSL.Prop _, OSL.Bool x) -> pure [scalarValue (S11.boolToScalar x)]
    (OSL.Prop _, _) -> typeMismatch
    (OSL.Maybe _ a, OSL.Maybe'' Nothing) ->
      mconcat <$> sequence
        [ pure [scalarValue zero],
          defaultSigma11Values c a
        ]
    (OSL.Maybe _ a, OSL.Maybe'' (Just x)) ->
      mconcat <$> sequence
        [ pure [scalarValue one],
          rec a x
        ]
    (OSL.Maybe {}, _) -> typeMismatch
    (OSL.NamedType _ name, OSL.To' _ x) ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data a) -> rec (OSL.dropTypeAnnotations a) x
        _ -> Left . ErrorMessage () $ "expected the name of a type"
    (OSL.NamedType {}, _) -> typeMismatch
    (OSL.List ann n a, OSL.List'' xs) -> do
      mconcat <$> sequence
        [ (:[]) . scalarValue <$> fromInt (length xs),
          rec (OSL.F ann (Just n) (OSL.N ann) a)
            . OSL.Fun . Map.fromList =<< sequence
            [ (,x) <$> (OSL.Nat <$> fromInt i)
            | (i, x) <- zip [0..] xs
            ]
        ]
    (OSL.List {}, _) -> typeMismatch
    (OSL.Map ann n a b, OSL.Map'' xs) -> do
      mconcat <$> sequence
        [ (:[]) . scalarValue <$> fromInt (Map.size xs),
          rec (OSL.F ann (Just n) (OSL.N ann) a)
            . OSL.Fun . Map.fromList =<< sequence
            [ (,x) <$> (OSL.Nat <$> fromInt i)
            | (i, x) <- zip [0..] (Map.keys xs)
            ],
          rec (OSL.F ann (Just n) a b)
            (OSL.Fun xs)
        ]
    (OSL.Map {}, _) -> typeMismatch
  where
    scalarFunction a b (OSL.Fun f) =
      (:[]) . S11.Value . Map.fromList <$> sequence
        [ (,) <$> (toScalars =<< rec a x) <*> (toScalar =<< rec b y)
        | (x,y) <- Map.toList f
        ]
    scalarFunction _ _ _ = typeMismatch

    rec = toSigma11Values c

    iotaIndex :: OSL.Value -> Either (ErrorMessage ()) Scalar
    iotaIndex =
      \case
        OSL.Iota1' _ -> pure zero
        OSL.Iota2' _ -> pure one
        _ -> Left (ErrorMessage () "expected a coproduct value")

    maybeIndex :: OSL.Value -> Either (ErrorMessage ()) Scalar
    maybeIndex =
      \case
        OSL.Maybe'' Nothing -> pure zero
        OSL.Maybe'' (Just _) -> pure one
        _ -> Left (ErrorMessage () "expected a maybe value")

    listLength :: OSL.Value -> Either (ErrorMessage ()) Scalar
    listLength =
      \case
        OSL.List'' xs -> fromInt (length xs)
        _ -> Left (ErrorMessage () "expected a list")

    listElems :: OSL.Value -> Either (ErrorMessage ()) OSL.Value
    listElems =
      \case
        OSL.List'' xs ->
          OSL.Fun . Map.fromList <$> sequence
            [ (,x) . OSL.Nat <$> fromInt i
            | (i,x) <- zip [0..] xs
            ]
        _ -> Left (ErrorMessage () "expected a list")

    mapSize :: OSL.Value -> Either (ErrorMessage ()) Scalar
    mapSize =
      \case
        OSL.Map'' xs -> fromInt (Map.size xs)
        _ -> Left (ErrorMessage () "expected a map")

    mapKeys :: OSL.Value -> Either (ErrorMessage ()) [OSL.Value]
    mapKeys =
      \case
        OSL.Map'' xs -> pure (Map.keys xs)
        _ -> Left (ErrorMessage () "expected a map")

    fromTo :: OSL.Value -> Either (ErrorMessage ()) OSL.Value
    fromTo =
      \case
        OSL.To' _ x -> pure x
        _ -> Left (ErrorMessage () "expected a To value")


typeMismatch :: Either (ErrorMessage ()) a
typeMismatch = Left . ErrorMessage () $ "type mismatch"

fromInt :: Int -> Either (ErrorMessage ()) Scalar
fromInt x =
  maybe (Left (ErrorMessage () "int out of range of scalar field"))
    pure (integerToScalar (intToInteger x))

toScalars :: [S11.Value] -> Either (ErrorMessage ()) [Scalar]
toScalars = mapM (toScalar . (:[]))

toScalar :: [S11.Value] -> Either (ErrorMessage ()) Scalar
toScalar [S11.Value u] =
  case Map.lookup [] u of
    Just u' -> pure u'
    Nothing -> Left . ErrorMessage () $ "expected a scalar"
toScalar _ = Left . ErrorMessage () $ "expected a scalar"

defaultSigma11Values ::
  OSL.ValidContext t ann ->
  OSL.Type () ->
  Either (ErrorMessage ()) [S11.Value]
defaultSigma11Values c =
  \case
    OSL.NamedType _ name ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data a) -> rec (OSL.dropTypeAnnotations a)
        _ -> Left (ErrorMessage () "expected the name of a type")
    OSL.Prop _ -> pure scalarDefault
    OSL.N _ -> pure scalarDefault
    OSL.Z _ -> pure scalarDefault
    OSL.Fp _ -> pure scalarDefault
    OSL.Fin {} -> pure scalarDefault
    OSL.F _ _ _ (OSL.P {}) ->
      Left (ErrorMessage () "unsupported: families of permutations")
    OSL.F _ _ _ (OSL.Prop _) ->
      Left (ErrorMessage () "unsupported: Prop in function codomain")
    OSL.F _ _ _ t ->
      fmap (const (S11.Value mempty)) <$> rec t
    OSL.P {} -> pure [S11.Value mempty]
    OSL.Product _ a b ->
      (<>) <$> rec a <*> rec b
    OSL.Coproduct _ a b ->
      mconcat <$> sequence
        [ pure scalarDefault,
          rec a,
          rec b
        ]
    OSL.Maybe _ a ->
      (scalarDefault <>) <$> rec a
    OSL.List ann n a ->
      (scalarDefault <>) <$> rec (OSL.F ann (Just n) (OSL.N ann) a)
    OSL.Map ann n a b ->
      mconcat <$> sequence
        [ pure scalarDefault,
          rec (OSL.F ann (Just n) (OSL.N ann) a),
          rec (OSL.F ann (Just n) a b)
        ]
  where
    rec = defaultSigma11Values c

    scalarDefault = [S11.Value (Map.singleton [] zero)]
