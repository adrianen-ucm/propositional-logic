module Test.Prop where

import qualified Data.Set         as S
import qualified NaturalDeduction as Pr
import qualified Syntax           as P
import           Test.QuickCheck  (Arbitrary (arbitrary), chooseInt, elements,
                                   oneof, sized)

newtype Name = Name Char
  deriving (Show, Eq, Ord)

newtype Prop = Prop (P.Prop Name)
  deriving (Show, Eq, Ord)

newtype PropSet = PropSet (S.Set (P.Prop Name))
  deriving (Show, Eq)

newtype Proof = Proof (Pr.Proof Name, P.Prop Name)
  deriving (Show, Eq)

instance Arbitrary Name where
  arbitrary = Name <$> elements ['a'..'j']

instance Arbitrary Prop where
  arbitrary = Prop <$> sized s
    where
      bot = pure P.Bot
      ato = P.Ato <$> arbitrary
      s n
        | n <= 0    = bot
        | n == 1    = oneof [bot, ato]
        | otherwise = do
            k1 <- chooseInt (0, n)
            k2 <- chooseInt (0, n)
            oneof
              [ bot
              , ato
              , P.Neg <$> s k1
              , P.Con <$> s k1 <*> s k2
              , P.Dis <$> s k1 <*> s k2
              , P.Imp <$> s k1 <*> s k2
              ]

instance Arbitrary PropSet where
  arbitrary =
    PropSet .
    S.fromList .
    map (\(Prop p) -> p) <$>
    arbitrary

instance Arbitrary Proof where
  arbitrary = Proof <$> sized s
    where
      propGen = do
        Prop p <- arbitrary
        pure p

      assumption = do
          p <- propGen
          pure (Pr.Assumption p, p)

      conI n     = do
          k1 <- chooseInt (0, n)
          k2 <- chooseInt (0, n)
          (pr1, p1) <- s k1
          (pr2, p2) <- s k2
          pure (Pr.ConI pr1 pr2, P.Con p1 p2)

      conEL n    = do
          k <- chooseInt (0, n)
          (pr, p) <- conI k
          pure $ case p of
            P.Con pL _ -> (Pr.ConEL pr, pL)
            _          -> error "Not possible"

      conER n    = do
          k <- chooseInt (0, n)
          (pr, p) <- conI k
          pure $ case p of
            P.Con _ pR -> (Pr.ConER pr, pR)
            _          -> error "Not possible"

      negI n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure $ case p of
            P.Bot -> (Pr.NegI r pr, P.Neg r)
            _     -> (Pr.NegI r (Pr.Assumption P.Bot), P.Neg r)

      negE n     = do
          k1 <- chooseInt (0, n)
          k2 <- chooseInt (0, n)
          (pr1, p1) <- s k1
          (pr2, p2) <- s k2
          if P.contradicts p1 p2
            then pure (Pr.NegE pr1 pr2, P.Bot)
            else elements
              [ (Pr.NegE (Pr.Assumption (P.Neg p2)) pr2, P.Bot)
              , (Pr.NegE (Pr.Assumption (P.Neg p1)) pr1, P.Bot)
              ]

      disIL n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure (Pr.DisIL r pr, P.Dis r p)

      disIR n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure (Pr.DisIR r pr, P.Dis p r)

      disE n     = do
          k1 <- chooseInt (0, n)
          k2 <- chooseInt (0, n)
          k3 <- chooseInt (0, n)
          (pr1, p1) <- oneof [ disIL k1, disIR k1]
          (pr2, p2) <- s k2
          (pr3, p3) <- s k3
          case p1 of
            P.Dis _ _ | p2 == p3 ->
              pure (Pr.DisE pr1 pr2 pr3, p2)
            P.Dis _ _            ->
              elements
                [ (Pr.DisE pr1 pr2 pr2, p2)
                , (Pr.DisE pr1 pr3 pr3, p3)
                ]
            _                  ->
              error "Not possible"

      impI n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure (Pr.ImpI r pr, P.Imp r p)

      impE     n = do
        k1 <- chooseInt (0, n)
        k2 <- chooseInt (0, n)
        (pr1, p1) <- s k1
        (pr2, p2) <- impI k2
        pure $ case p2 of
          P.Imp a b | a == p1 -> (Pr.ImpE pr1 pr2, b)
          P.Imp a b           -> (Pr.ImpE (Pr.Assumption a) pr2, b)
          _                   -> error "Not possible"

      botE n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure $ case p of
            P.Bot -> (Pr.BotE r pr, r)
            _     -> (Pr.BotE r (Pr.Assumption P.Bot), r)

      s n
        | n <= 0    = assumption
        | otherwise = oneof
              [ assumption
              , conI n
              , conEL n
              , conER n
              , negI n
              , negE n
              , disIL n
              , disIR n
              , disE n
              , impI n
              , impE n
              , botE n
              ]
