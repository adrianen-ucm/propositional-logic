{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import           Control.Monad    (unless)
import qualified Data.Set         as S
import           NaturalDeduction (runProof)
import           Semantics        (entails, sat, satSet, valid)
import qualified Syntax           as P
import           System.Exit      (exitFailure)
import           Test.Prop        (Proof (..), Prop (..), PropSet (..))
import           Test.QuickCheck  (quickCheckAll)

prop_DoubleNegation :: Prop -> Bool
prop_DoubleNegation (Prop p) =
  valid $ p `P.iff` P.Neg (P.Neg p)

prop_ImpAsDisNeg :: Prop -> Prop -> Bool
prop_ImpAsDisNeg (Prop p) (Prop q) =
  valid $ P.Imp p q `P.iff` P.Dis (P.Neg p) q

prop_ConAsDisNeg :: Prop -> Prop -> Bool
prop_ConAsDisNeg (Prop p) (Prop q) =
  valid $ P.Con p q `P.iff` P.Neg (P.Dis (P.Neg p) (P.Neg q))

prop_DisAsConNeg :: Prop -> Prop -> Bool
prop_DisAsConNeg (Prop p) (Prop q) =
  valid $ P.Dis p q `P.iff` P.Neg (P.Con (P.Neg p) (P.Neg q))

prop_EntailReflexive :: Prop -> Bool
prop_EntailReflexive (Prop p) =
  entails (S.singleton p) p

prop_EntailTransitive :: Prop -> Prop -> Prop -> Bool
prop_EntailTransitive (Prop p) (Prop q) (Prop r) =
  not (entails (S.singleton p) q && entails (S.singleton q) r)
    || entails (S.singleton p) r

prop_ValidSat :: Prop -> Bool
prop_ValidSat (Prop p) =
  not (valid p)
    || sat p

prop_ValidUnsatNeg :: Prop -> Bool
prop_ValidUnsatNeg (Prop p) =
  valid p == not (sat (P.Neg p))

prop_UnsatEntailsBot :: Prop -> Bool
prop_UnsatEntailsBot (Prop p) =
  sat p
    || entails (S.singleton p) P.Bot

prop_Deduction :: PropSet -> Prop -> Prop -> Bool
prop_Deduction (PropSet g) (Prop p) (Prop q) =
  entails g (P.Imp p q) == entails (S.insert p g) q

prop_Decomposition :: PropSet -> (Prop, PropSet) -> Prop -> Bool
prop_Decomposition (PropSet g) (Prop c, PropSet cs) (Prop p) =
  let cCon = foldr P.Con c $ S.toList cs
  in entails (S.insert cCon g) p == entails (S.union g $ S.insert c cs) p

prop_Contradiction1 :: PropSet -> Prop -> Bool
prop_Contradiction1 (PropSet g) (Prop p) =
  entails g p == not (satSet (S.insert (P.Neg p) g))

prop_Contradiction2 :: PropSet -> Bool
prop_Contradiction2 (PropSet g) =
  entails g P.Bot == not (satSet g)

prop_Valid :: PropSet -> Prop -> Bool
prop_Valid (PropSet g) (Prop p) =
  not (valid p) || entails g p

prop_Monotonicity :: PropSet -> PropSet -> Prop -> Bool
prop_Monotonicity (PropSet g1) (PropSet g2) (Prop p) =
  not (entails (S.intersection g1 g2) p) || entails g1 p

prop_CorrectProof :: Proof -> Bool
prop_CorrectProof (Proof (pr, p)) =
  Just p == (fst <$> runProof pr)

prop_SoundProof :: Proof -> Bool
prop_SoundProof (Proof (pr, _)) =
  case runProof pr of
    Just (p, assumptions) -> entails assumptions p
    Nothing               -> False

prop_ConsistentProof :: Proof -> Bool
prop_ConsistentProof (Proof (pr, _)) =
  case runProof pr of
    Just (P.Bot, assumptions) -> not (null assumptions)
    _                         -> True

return []
runTests :: IO Bool
runTests = $quickCheckAll

main :: IO ()
main = do
  success <- runTests
  unless success exitFailure
