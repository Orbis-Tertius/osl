{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module OSL.Parse (parseContext) where

import Control.Monad (guard, mzero)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack, unpack)
import Die (die)
import OSL.Bound (boundAnnotation)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.Keyword as K
import OSL.Types.OSL (Bound (..), Cardinality (..), CodomainBound (..), Context (..), Declaration (..), DomainBound (..), KeysBound (..), LeftBound (..), Name, RightBound (..), Term (..), Type (..), ValuesBound (..))
import OSL.Types.Token (Token)
import qualified OSL.Types.Token as T
import Text.Parsec (Parsec, SourceName, SourcePos, choice, eof, getPosition, many, many1, option, optionMaybe, token, try, (<|>))
import qualified Text.Parsec.Prim as Prim

parseContext :: SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) (Context SourcePos)
parseContext = parse' context

type Parser = Parsec [(Token, SourcePos)] ()

parse' :: Parser a -> SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) a
parse' p n = mapLeft (ErrorMessage () . pack . show) . Prim.parse p n

consume :: ((Token, SourcePos) -> Maybe a) -> Parser a
consume = token (unpack . printToken . fst) snd

consumeExact :: Token -> (SourcePos -> a) -> Parser a
consumeExact tok tm =
  consume (\(t, p) -> guard (t == tok) >> pure (tm p))

consumeExact_ :: Token -> Parser ()
consumeExact_ tok = consumeExact tok (const ())

printToken :: Token -> Text
printToken = pack . show

context :: Parser (Context SourcePos)
context = do
  decls <- many declaration
  eof
  pure (Context decls)

declaration :: Parser (Name, Declaration SourcePos)
declaration =
  choice
    [ dataDeclaration,
      defDeclaration,
      freeDeclaration
    ]

dataDeclaration :: Parser (Name, Declaration SourcePos)
dataDeclaration = do
  consumeExact_ (T.Keyword K.Data)
  n <- name
  consumeExact_ T.Congruent
  t <- type0
  consumeExact_ T.Period
  pure (n, Data t)

defDeclaration :: Parser (Name, Declaration SourcePos)
defDeclaration = do
  consumeExact_ (T.Keyword K.Def)
  n <- name
  consumeExact_ T.Colon
  ty <- type0
  consumeExact_ T.DefEquals
  def <- term0
  consumeExact_ T.Period
  pure (n, Defined ty def)

freeDeclaration :: Parser (Name, Declaration SourcePos)
freeDeclaration = do
  n <- name
  consumeExact_ T.Colon
  t <- type0
  consumeExact_ T.Period
  pure (n, FreeVariable t)

name :: Parser Name
name =
  consume $
    \case
      (T.Var x, _) -> pure x
      _ -> mzero

type0 :: Parser (Type SourcePos)
type0 = do
  p <- getPosition
  t <- type1
  rest <- option Nothing $ do
    op <- consume $
      \case
        (T.ThinArrow, _) -> pure T.ThinArrow
        (T.LeftRightArrow, _) -> pure T.LeftRightArrow
        _ -> mzero
    case op of
      T.ThinArrow -> do
        n <- optionMaybe cardinality
        t' <- type0
        pure (Just (F p n t t'))
      T.LeftRightArrow -> do
        n <- optionMaybe cardinality
        t' <- type1
        pure (Just (P p n t t'))
      _ -> mzero
  case rest of
    Nothing -> pure t
    Just t' -> pure t'

type1 :: Parser (Type SourcePos)
type1 = do
  p <- getPosition
  t <- type2
  ts <- option Nothing ((Just . Left <$> productTail) <|> (Just . Right <$> coproductTail))
  case ts of
    Nothing -> pure t
    Just (Left ts') -> pure (Product p t ts')
    Just (Right ts') -> pure (Coproduct p t ts')

productTail :: Parser (Type SourcePos)
productTail = do
  p <- getPosition
  consumeExact_ T.ProductOp
  t <- type2
  ts <- option Nothing (Just <$> productTail)
  case ts of
    Nothing -> pure t
    Just ts' -> pure (Product p t ts')

coproductTail :: Parser (Type SourcePos)
coproductTail = do
  p <- getPosition
  consumeExact_ T.CoproductOp
  t <- type2
  ts <- option Nothing (Just <$> coproductTail)
  case ts of
    Nothing -> pure t
    Just ts' -> pure (Coproduct p t ts')

type2 :: Parser (Type SourcePos)
type2 =
  choice $
    try
      <$> [ consumeExact (T.Keyword K.Prop) Prop,
            consumeExact (T.Keyword K.N) N,
            consumeExact (T.Keyword K.Z) Z,
            consumeExact (T.Keyword K.F) Fp,
            NamedType <$> getPosition <*> name,
            parenthesizedType,
            finiteType,
            maybeType,
            listType,
            mapType
          ]

parenthesizedType :: Parser (Type SourcePos)
parenthesizedType = do
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  pure t

finiteType :: Parser (Type SourcePos)
finiteType = do
  consumeExact_ (T.Keyword K.Fin)
  consumeExact_ T.OpenParen
  t <- consume $
    \case
      (T.Const i, p) -> pure (Fin p i)
      _ -> mzero
  consumeExact_ T.CloseParen
  pure t

maybeType :: Parser (Type SourcePos)
maybeType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Maybe)
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  pure (Maybe p t)

listType :: Parser (Type SourcePos)
listType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.List)
  n <- cardinality
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  pure (List p n t)

mapType :: Parser (Type SourcePos)
mapType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Map)
  n <- cardinality
  consumeExact_ T.OpenParen
  t0 <- type0
  consumeExact_ T.Comma
  t1 <- type0
  consumeExact_ T.CloseParen
  pure (Map p n t0 t1)

term0 :: Parser (Term SourcePos)
term0 =
  choice $
    [ quantifier T.ForAll ForAll,
      quantifier T.ForSome ForSome,
      lambda,
      letExpr,
      term1
    ]

quantifier ::
  Token ->
  ( SourcePos ->
    Name ->
    Type (SourcePos) ->
    Maybe (Bound SourcePos) ->
    Term (SourcePos) ->
    Term SourcePos
  ) ->
  Parser (Term SourcePos)
quantifier tok ctor = do
  p <- getPosition
  consumeExact_ tok
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  varBound <- optionMaybe (consumeExact_ T.Less >> bound0)
  consumeExact_ T.Comma
  q <- term0
  pure (ctor p varName varType varBound q)

bound0 :: Parser (Bound SourcePos)
bound0 = do
  b0 <- bound1
  bs <-
    option
      Nothing
      ( Just
          <$> ( productBoundTail
                  <|> coproductBoundTail
                  <|> functionBoundTail
              )
      )
  case bs of
    Nothing -> pure b0
    Just bs' -> pure (appendBoundTail b0 bs')

-- The bound tail takes a constructor which takes the head
-- and pures the whole bound.
data BoundTail
  = ProductBoundTail [Bound SourcePos]
  | CoproductBoundTail [Bound SourcePos]
  | FunctionBoundTail [Bound SourcePos]

appendBoundTail :: Bound SourcePos -> BoundTail -> Bound SourcePos
appendBoundTail b0 =
  \case
    ProductBoundTail bs ->
      foldl
        ( \bAcc bNext ->
            ProductBound
              (boundAnnotation bAcc)
              (LeftBound bAcc)
              (RightBound bNext)
        )
        b0
        bs
    CoproductBoundTail bs ->
      foldl
        ( \bAcc bNext ->
            CoproductBound
              (boundAnnotation bAcc)
              (LeftBound bAcc)
              (RightBound bNext)
        )
        b0
        bs
    FunctionBoundTail bs ->
      foldl
        ( \bAcc bNext ->
            FunctionBound
              (boundAnnotation bAcc)
              (DomainBound bAcc)
              (CodomainBound bNext)
        )
        b0
        bs

productBoundTail :: Parser BoundTail
productBoundTail = boundTail T.ProductOp ProductBoundTail

coproductBoundTail :: Parser BoundTail
coproductBoundTail = boundTail T.CoproductOp CoproductBoundTail

functionBoundTail :: Parser BoundTail
functionBoundTail = boundTail T.ThinArrow FunctionBoundTail

boundTail ::
  T.Token ->
  ([Bound SourcePos] -> BoundTail) ->
  Parser BoundTail
boundTail op ctor =
  ctor <$> many1 (consumeExact_ op >> bound1)

bound1 :: Parser (Bound SourcePos)
bound1 =
  choice $
    [ scalarBound,
      listBound,
      maybeBound,
      mapBound,
      toBound,
      parenthesizedBound
    ]

parenthesizedBound :: Parser (Bound SourcePos)
parenthesizedBound = do
  consumeExact_ T.OpenParen
  b <- bound0
  consumeExact_ T.CloseParen
  pure b

scalarBound :: Parser (Bound SourcePos)
scalarBound = ScalarBound <$> getPosition <*> term1

listBound :: Parser (Bound SourcePos)
listBound =
  ListBound
    <$> getPosition
    <*> (ValuesBound <$> parenthesizedBound)

maybeBound :: Parser (Bound SourcePos)
maybeBound =
  MaybeBound
    <$> getPosition
    <*> (ValuesBound <$> parenthesizedBound)

mapBound :: Parser (Bound SourcePos)
mapBound =
  MapBound
    <$> getPosition
    <*> (KeysBound <$> (consumeExact_ T.OpenParen >> bound0))
    <*> ( ValuesBound
            <$> ( consumeExact_ T.Comma
                    >> bound0
                    `preceding` consumeExact_ T.CloseParen
                )
        )

preceding :: Monad m => m a -> m () -> m a
preceding f g = do
  r <- f
  g
  pure r

toBound :: Parser (Bound SourcePos)
toBound =
  ToBound
    <$> getPosition
    <*> (consumeExact_ T.OpenParen >> name)
    <*> (consumeExact_ T.Comma >> bound0 `preceding` consumeExact_ T.CloseParen)

lambda :: Parser (Term SourcePos)
lambda = do
  p <- getPosition
  consumeExact_ T.Lambda
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.ThickArrow
  y <- term0
  pure (Lambda p varName varType y)

letExpr :: Parser (Term SourcePos)
letExpr = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Let)
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.DefEquals
  def <- term0
  consumeExact_ T.Semicolon
  y <- term0
  pure (Let p varName varType def y)

term1 :: Parser (Term SourcePos)
term1 = do
  x <- term2
  try (operatorOn x) <|> pure x

operatorOn :: Term SourcePos -> Parser (Term SourcePos)
operatorOn x = do
  p <- getPosition
  op <- consume $
    \case
      (T.And, _) -> pure T.And
      (T.Or, _) -> pure T.Or
      (T.AddNOp, _) -> pure T.AddNOp
      (T.MulNOp, _) -> pure T.MulNOp
      (T.AddZOp, _) -> pure T.AddZOp
      (T.MulZOp, _) -> pure T.MulZOp
      (T.AddFpOp, _) -> pure T.AddFpOp
      (T.MulFpOp, _) -> pure T.MulFpOp
      (T.ProductOp, _) -> pure T.ProductOp
      (T.CoproductOp, _) -> pure T.CoproductOp
      (T.ThinArrow, _) -> pure T.ThinArrow
      (T.LeftRightArrow, _) -> pure T.LeftRightArrow
      (T.Equal, _) -> pure T.Equal
      (T.LessOrEqual, _) -> pure T.LessOrEqual
      _ -> Nothing
  xs <-
    if isAssociative op
      then do
        y <- term2
        ys <- many (consumeExact_ op >> term2)
        pure (y : ys)
      else (: []) <$> term2
  pure (foldl (opCtor op p) x xs)
  where
    opCtor =
      \case
        T.And -> And
        T.Or -> Or
        T.AddNOp -> applyBinaryOp AddN
        T.MulNOp -> applyBinaryOp MulN
        T.AddZOp -> applyBinaryOp AddZ
        T.MulZOp -> applyBinaryOp MulZ
        T.AddFpOp -> applyBinaryOp AddFp
        T.MulFpOp -> applyBinaryOp MulFp
        T.ProductOp -> FunctionProduct
        T.CoproductOp -> FunctionCoproduct
        T.ThinArrow -> Implies
        T.LeftRightArrow -> Iff
        T.Equal -> Equal
        T.LessOrEqual -> LessOrEqual
        _ -> error "opCtor called outside defined domain"

    isAssociative =
      \case
        T.And -> True
        T.Or -> True
        T.AddNOp -> True
        T.MulNOp -> True
        T.AddZOp -> True
        T.MulZOp -> True
        T.AddFpOp -> True
        T.MulFpOp -> True
        T.ProductOp -> True
        T.CoproductOp -> True
        T.ThinArrow -> False
        T.LeftRightArrow -> False
        T.Equal -> False
        T.LessOrEqual -> False
        _ -> error "isAssociative called outside defined domain"

term2 :: Parser (Term SourcePos)
term2 =
  choice $
    try
      <$> [ tuple,
            unaryOp term0 T.Not Not,
            functionApplication,
            term3
          ]

functionApplication :: Parser (Term SourcePos)
functionApplication = do
  p <- getPosition
  f <- term3
  consumeExact_ T.OpenParen
  arg <- term1
  args <- many (consumeExact_ T.Comma >> term1)
  consumeExact_ T.CloseParen
  pure (foldl (Apply p) f (arg : args))

parenthesizedTerm :: Parser (Term SourcePos)
parenthesizedTerm = do
  consumeExact_ T.OpenParen
  x <- term0
  consumeExact_ T.CloseParen
  pure x

functionTableLiteral :: Parser (Term SourcePos)
functionTableLiteral = do
  p <- getPosition
  consumeExact_ T.OpenBracket
  t <- ConstF p <$> functionTableBody
  consumeExact_ T.CloseBracket
  pure t

functionTableBody :: Parser [(Term SourcePos, Term SourcePos)]
functionTableBody = do
  mr0 <- optionMaybe functionTableRow
  case mr0 of
    Nothing -> pure []
    Just r0 -> (r0 :) <$> many (consumeExact_ T.Comma >> functionTableRow)

functionTableRow :: Parser (Term SourcePos, Term SourcePos)
functionTableRow = (,) <$> term1 <*> (consumeExact_ T.ThickArrow >> term1)

setLiteral :: Parser (Term SourcePos)
setLiteral = do
  p <- getPosition
  consumeExact_ T.OpenBrace
  t <- ConstSet p <$> setElements
  consumeExact_ T.CloseBrace
  pure t

setElements :: Parser [Term SourcePos]
setElements = do
  mx0 <- optionMaybe term1
  case mx0 of
    Nothing -> pure []
    Just x0 -> (x0 :) <$> many (consumeExact_ T.Comma >> term1)

term3 :: Parser (Term SourcePos)
term3 =
  choice $
    [ namedTerm,
      constant,
      parenthesizedTerm,
      functionTableLiteral,
      setLiteral,
      builtin K.Cast Cast,
      builtin K.Inverse Inverse,
      builtin K.Pi1 Pi1,
      builtin K.Pi2 Pi2,
      builtin K.Iota1 Iota1,
      builtin K.Iota2 Iota2,
      unaryOp name (T.Keyword K.To) To,
      unaryOp name (T.Keyword K.From) From,
      builtin K.IsNothing IsNothing,
      builtin K.Nothing' Nothing',
      builtin K.Just' Just',
      unaryOp term0 (T.Keyword K.Maybe') Maybe',
      builtin K.Exists Exists,
      builtin K.Length Length,
      builtin K.Nth Nth,
      functorApplication,
      builtin K.Lookup Lookup,
      builtin K.Keys Keys,
      builtin K.Sum Sum,
      builtin K.SumMapLength SumMapLength,
      sumListLookup
    ]

cardinality :: Parser Cardinality
cardinality = Cardinality <$> caretBound

caretBound :: Parser Integer
caretBound = do
  consumeExact_ T.Caret
  consume $
    \case
      (T.Const i, _) -> pure i
      _ -> mzero

sumListLookup :: Parser (Term SourcePos)
sumListLookup = do
  p <- getPosition
  consumeExact_ (T.Keyword K.SumListLookup)
  consumeExact_ T.OpenParen
  k <- term1
  v <- optionMaybe (consumeExact_ T.Comma >> term1)
  consumeExact_ T.CloseParen
  case v of
    Nothing -> pure (SumListLookup p k)
    Just v' -> pure (Apply p (SumListLookup p k) v')

namedTerm :: Parser (Term SourcePos)
namedTerm = do
  p <- getPosition
  NamedTerm p <$> name

constant :: Parser (Term SourcePos)
constant =
  consume $
    \case
      (T.ConstN i, p) -> pure (ConstN p i)
      (T.ConstZ i, p) -> pure (ConstZ p i)
      (T.ConstF i, p) -> pure (ConstFp p i)
      (T.ConstFin i, p) -> pure (ConstFin p i)
      _ -> Nothing

builtin ::
  K.Keyword ->
  (SourcePos -> Term SourcePos) ->
  Parser (Term SourcePos)
builtin k op = do
  p <- getPosition
  consumeExact_ (T.Keyword k)
  pure (op p)

functorApplication :: Parser (Term SourcePos)
functorApplication = do
  (f, p) <- consume $
    \case
      (T.Keyword K.List, p) -> pure (K.List, p)
      (T.Keyword K.Map, p) -> pure (K.Map, p)
      (T.Keyword K.Maybe, p) -> pure (K.Maybe, p)
      _ -> Nothing
  case f of
    K.Maybe -> do
      consumeExact_ T.OpenParen
      g <- consume $
        \case
          (T.Keyword K.Pi1, _) -> pure K.Pi1
          (T.Keyword K.Pi2, _) -> pure K.Pi2
          (T.Keyword K.To, _) -> pure K.To
          (T.Keyword K.From, _) -> pure K.From
          _ -> Nothing
      h <- case g of
        K.Pi1 -> pure (MaybePi1 p)
        K.Pi2 -> pure (MaybePi2 p)
        K.To -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          pure (MaybeTo p a)
        K.From -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          pure (MaybeFrom p a)
        _ -> mzero
      consumeExact_ T.CloseParen
      pure h
    K.List -> do
      consumeExact_ T.OpenParen
      g <- consume $
        \case
          (T.Keyword K.Cast, _) -> pure K.Cast
          (T.Keyword K.Pi1, _) -> pure K.Pi1
          (T.Keyword K.Pi2, _) -> pure K.Pi2
          (T.Keyword K.To, _) -> pure K.To
          (T.Keyword K.From, _) -> pure K.From
          (T.Keyword K.Length, _) -> pure K.Length
          (T.Keyword K.Maybe, _) -> pure K.Maybe
          _ -> Nothing
      h <- case g of
        K.Cast -> pure (ListCast p)
        K.Pi1 -> pure (ListPi1 p)
        K.Pi2 -> pure (ListPi2 p)
        K.To -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          pure (ListTo p a)
        K.From -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          pure (ListFrom p a)
        K.Length -> pure (ListLength p)
        K.Maybe -> do
          consumeExact_ T.OpenParen
          i <- consume $
            \case
              (T.Keyword K.Pi1, _) -> pure K.Pi1
              (T.Keyword K.Pi2, _) -> pure K.Pi2
              (T.Keyword K.Length, _) -> pure K.Length
              (T.Keyword K.To, _) -> pure K.To
              (T.Keyword K.From, _) -> pure K.From
              _ -> Nothing
          j <- case i of
            K.Pi1 -> pure (ListMaybePi1 p)
            K.Pi2 -> pure (ListMaybePi2 p)
            K.Length -> pure (ListMaybeLength p)
            K.To -> do
              consumeExact_ T.OpenParen
              x <- name
              consumeExact_ T.CloseParen
              pure (ListMaybeTo p x)
            K.From -> do
              consumeExact_ T.OpenParen
              x <- name
              consumeExact_ T.CloseParen
              pure (ListMaybeFrom p x)
            _ -> mzero
          consumeExact_ T.CloseParen
          pure j
        _ -> mzero
      consumeExact_ T.CloseParen
      pure h
    K.Map -> do
      consumeExact_ T.OpenParen
      g <- consume $
        \case
          (T.Keyword K.Pi1, _) -> pure K.Pi1
          (T.Keyword K.Pi2, _) -> pure K.Pi2
          (T.Keyword K.To, _) -> pure K.To
          (T.Keyword K.From, _) -> pure K.From
          _ -> Nothing
      h <- case g of
        K.Pi1 -> pure (MapPi1 p)
        K.Pi2 -> pure (MapPi2 p)
        K.To -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          pure (MapTo p a)
        K.From -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          pure (MapFrom p a)
        _ -> mzero
      consumeExact_ T.CloseParen
      pure h
    _ -> mzero

applyBinaryOp ::
  (SourcePos -> Term SourcePos) ->
  SourcePos ->
  Term SourcePos ->
  Term SourcePos ->
  Term SourcePos
applyBinaryOp op p x y = Apply p (Apply p (op p) x) y

unaryOp ::
  Parser a ->
  Token ->
  (SourcePos -> a -> Term SourcePos) ->
  Parser (Term SourcePos)
unaryOp subexpr opTok opCtor = do
  p <- getPosition
  consumeExact_ opTok
  consumeExact_ T.OpenParen
  x <- subexpr
  consumeExact_ T.CloseParen
  pure (opCtor p x)

tuple :: Parser (Term SourcePos)
tuple = do
  p <- getPosition
  consumeExact_ T.OpenParen
  x <- term1
  xs <- many1 (consumeExact_ T.Comma >> term1)
  consumeExact_ T.CloseParen
  case reverse (x : xs) of
    (x' : xs') ->
      pure
        ( foldr
            (\y z -> Apply p (Apply p (Pair p) y) z)
            x'
            xs'
        )
    [] -> die "logical impossibility: reverse of non-empty list is empty"
