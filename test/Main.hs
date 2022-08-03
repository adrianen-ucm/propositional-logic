{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import           Control.Monad    (unless)
import qualified Data.Set         as S
import           NaturalDeduction (runProof)
import           Semantics        (entails, sat, satSet, valid)
import           Syntax           (Prop (..), iff)
import           System.Exit      (exitFailure)
import           Test.Prop        (ProofName (..), PropName (..),
                                   PropNameSet (..))
import           Test.QuickCheck  (quickCheckAll)

prop_DoubleNegation :: PropName -> Bool
prop_DoubleNegation (PropName p) = valid $ p `iff` Neg (Neg p)

prop_ImpAsDisNeg :: PropName -> PropName -> Bool
prop_ImpAsDisNeg (PropName p) (PropName q) = valid $ Imp p q `iff` Dis (Neg p) q

prop_ConAsDisNeg :: PropName -> PropName -> Bool
prop_ConAsDisNeg (PropName p) (PropName q) = valid $ Con p q `iff` Neg (Dis (Neg p) (Neg q))

prop_DisAsConNeg :: PropName -> PropName -> Bool
prop_DisAsConNeg (PropName p) (PropName q) = valid $ Dis p q `iff` Neg (Con (Neg p) (Neg q))

prop_EntailRef :: PropName -> Bool
prop_EntailRef (PropName p) = entails (S.singleton p) p

prop_EntailTra :: PropName -> PropName -> PropName -> Bool
prop_EntailTra (PropName p) (PropName q) (PropName r) =
  not (entails (S.singleton p) q && entails (S.singleton q) r)
    || entails (S.singleton p) r

prop_ValidSat :: PropName -> Bool
prop_ValidSat (PropName p) =
  not (valid p)
    || sat p

prop_ValidUnsatNeg :: PropName -> Bool
prop_ValidUnsatNeg (PropName p) = valid p == not (sat (Neg p))

prop_UnsatEntailsBot :: PropName -> Bool
prop_UnsatEntailsBot (PropName p) =
  sat p
    || entails (S.singleton p) Bot

prop_Deduction :: PropNameSet -> PropName -> PropName -> Bool
prop_Deduction (PropNameSet g) (PropName p) (PropName q) =
  entails g (Imp p q) == entails (S.insert p g) q

prop_Decomposition :: PropNameSet -> (PropName, PropNameSet) -> PropName -> Bool
prop_Decomposition (PropNameSet g) (PropName c, PropNameSet cs) (PropName p) =
  let cCon = foldr Con c $ S.toList cs
  in entails (S.insert cCon g) p == entails (S.union g $ S.insert c cs) p

prop_Contradiction1 :: PropNameSet -> PropName -> Bool
prop_Contradiction1 (PropNameSet g) (PropName p) =
  entails g p == not (satSet (S.insert (Neg p) g))

prop_Contradiction2 :: PropNameSet -> Bool
prop_Contradiction2 (PropNameSet g) =
  entails g Bot == not (satSet g)

prop_Valid :: PropNameSet -> PropName -> Bool
prop_Valid (PropNameSet g) (PropName p) =
  not (valid p) || entails g p

prop_Monot :: PropNameSet -> PropNameSet -> PropName -> Bool
prop_Monot (PropNameSet g1) (PropNameSet g2) (PropName p) =
  not (entails (S.intersection g1 g2) p) || entails g1 p

prop_CorrectProof :: ProofName -> Bool
prop_CorrectProof (ProofName (pr, p)) = Just p == (fst <$> runProof pr)

prop_SoundProof :: ProofName -> Bool
prop_SoundProof (ProofName (pr, _)) =
  case runProof pr of
    Just (p, asP) -> entails asP p
    Nothing       -> False

prop_ConsistentProof :: ProofName -> Bool
prop_ConsistentProof (ProofName (pr, _)) =
  case runProof pr of
    Just (Bot, asP) -> not (null asP)
    _               -> True

return []
runTests :: IO Bool
runTests = $quickCheckAll

main :: IO ()
main = do
  success <- runTests
  unless success exitFailure
