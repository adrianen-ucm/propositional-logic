module Test.Prop where

import qualified Data.Set         as S
import           NaturalDeduction (Proof (..))
import           Syntax           (Prop (..), contradicts)
import           Test.QuickCheck  (Arbitrary (arbitrary), chooseInt, elements,
                                   oneof, sized)

newtype Name = Name Char
  deriving (Show, Eq, Ord)

newtype PropName = PropName (Prop Name)
  deriving (Show, Eq, Ord)

newtype PropNameSet = PropNameSet (S.Set (Prop Name))
  deriving (Show, Eq)

newtype ProofName = ProofName (Proof Name, Prop Name)
  deriving (Show, Eq)

instance Arbitrary Name where
  arbitrary = Name <$> elements ['a'..'j']

instance Arbitrary PropName where
  arbitrary = PropName <$> sized s
    where
      bot = pure Bot
      ato = Ato <$> arbitrary
      s n
        | n <= 0    = bot
        | n == 1    = oneof [bot, ato]
        | otherwise = do
            k1 <- chooseInt (0, n)
            k2 <- chooseInt (0, n)
            oneof
              [ bot
              , ato
              , Neg <$> s k1
              , Con <$> s k1 <*> s k2
              , Dis <$> s k1 <*> s k2
              , Imp <$> s k1 <*> s k2
              ]

instance Arbitrary PropNameSet where
  arbitrary =
    PropNameSet .
    S.fromList .
    map (\(PropName p) -> p) <$>
    arbitrary

instance Arbitrary ProofName where
  arbitrary = ProofName <$> sized s
    where
      propGen = do
        PropName p <- arbitrary
        pure p

      assumption = do
          p <- propGen
          pure (Assumption p, p)

      conI n     = do
          k1 <- chooseInt (0, n)
          k2 <- chooseInt (0, n)
          (pr1, p1) <- s k1
          (pr2, p2) <- s k2
          pure (ConI pr1 pr2, Con p1 p2)

      conEL n    = do
          k <- chooseInt (0, n)
          (pr, p) <- conI k
          pure $ case p of
            Con pL _ -> (ConEL pr, pL)
            _        -> error "Not possible"

      conER n    = do
          k <- chooseInt (0, n)
          (pr, p) <- conI k
          pure $ case p of
            Con _ pR -> (ConER pr, pR)
            _        -> error "Not possible"

      negI n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure $ case p of
            Bot -> (NegI r pr, Neg r)
            _   -> (NegI r (Assumption Bot), Neg r)

      negE n     = do
          k1 <- chooseInt (0, n)
          k2 <- chooseInt (0, n)
          (pr1, p1) <- s k1
          (pr2, p2) <- s k2
          if contradicts p1 p2
            then pure (NegE pr1 pr2, Bot)
            else elements
              [ (NegE (Assumption (Neg p2)) pr2, Bot)
              , (NegE (Assumption (Neg p1)) pr1, Bot)
              ]

      disIL n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure (DisIL r pr, Dis r p)

      disIR n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure (DisIR r pr, Dis p r)

      disE n     = do
          k1 <- chooseInt (0, n)
          k2 <- chooseInt (0, n)
          k3 <- chooseInt (0, n)
          (pr1, p1) <- oneof [ disIL k1, disIR k1]
          (pr2, p2) <- s k2
          (pr3, p3) <- s k3
          case p1 of
            Dis _ _ | p2 == p3 ->
              pure (DisE pr1 pr2 pr3, p2)
            Dis _ _            ->
              elements
                [ (DisE pr1 pr2 pr2, p2)
                , (DisE pr1 pr3 pr3, p3)
                ]
            _                  ->
              error "Not possible"

      impI n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure (ImpI r pr, Imp r p)

      impE     n = do
        k1 <- chooseInt (0, n)
        k2 <- chooseInt (0, n)
        (pr1, p1) <- s k1
        (pr2, p2) <- impI k2
        pure $ case p2 of
          Imp a b | a == p1 -> (ImpE pr1 pr2, b)
          Imp a b           -> (ImpE (Assumption a) pr2, b)
          _                 -> error "Not possible"

      botE n     = do
          k <- chooseInt (0, n)
          (pr, p) <- s k
          r <- propGen
          pure $ case p of
            Bot -> (BotE r pr, r)
            _   -> (BotE r (Assumption Bot), r)

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
