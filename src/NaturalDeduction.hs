-- |
-- Module      : NaturalDeduction
-- Copyright   : (c) Adrián Enríquez Ballester, 2022
--
-- The natural deduction derivation system for propositional logic.

module NaturalDeduction
  ( Proof (..)
  , runProof
  ) where

import           Control.Monad (guard)
import qualified Data.Set      as S
import           Syntax        (Prop (..), contradicts, unCon, unDis, unImp)

-- | Data type of a natural deduction proof tree with atom names
-- of type @v@.
data Proof v
  -- | Assumption of a proposition
  = Assumption (Prop v)
  -- | Negation introduction rule: proves the negation of the given
  -- proposition if the given subproof conclusion is bottom, discharging
  -- the proposition
  | NegI       (Prop v)  (Proof v)
  -- | Negation elimination rule: proves bottom if the subproof
  -- results contradict each other
  | NegE       (Proof v) (Proof v)
  -- | Conjunction introduction rule
  | ConI       (Proof v) (Proof v)
  -- | Conjunction left-elimination rule: keeps the left
  | ConEL      (Proof v)
  -- | Conjunction right-elimination rule: keeps the right
  | ConER      (Proof v)
  -- | Disjunction left-introduction rule: introduces the given
  -- proposition to the right
  | DisIL      (Prop v)  (Proof v)
  -- | Disjunction right-introduction rule: introduces the given
  -- proposition to the left
  | DisIR      (Prop v)  (Proof v)
  -- | Disjunction elimination rule: proves the result of the second
  -- and third subproofs, discharging the corresponding assumptions
  -- from the first subproof conslusion
  | DisE       (Proof v) (Proof v) (Proof v)
  -- | Implication elimination rule: modus ponens
  | ImpE       (Proof v) (Proof v)
  -- | Implication introduction rule: proves the implication of
  -- the subproof conclusion by the given proposition, discharging
  -- its assumption from the subproof
  | ImpI       (Prop v)  (Proof v)
  -- | Bottom elimination rule: proves any given proposition by a subproof
  -- that results in bottom
  | BotE       (Prop v)  (Proof v)
  deriving (Eq, Show)

-- | Compute a pair with the conclusion of a given proof and the set
-- of undischarged assumptions, if the proof is well formed.
runProof :: Ord v => Proof v -> Maybe (Prop v, S.Set (Prop v))
runProof (Assumption p)      =
  pure (p, S.singleton p)
runProof (ConI prL prR)      = do
  (pL, asL) <- runProof prL
  (pR, asR) <- runProof prR
  pure (Con pL pR, asL <> asR)
runProof (ConEL pr)          = do
  (p, as) <- runProof pr
  (pL, _) <- unCon p
  pure (pL, as)
runProof (ConER pr)          = do
  (p, as) <- runProof pr
  (_, pR) <- unCon p
  pure (pR, as)
runProof (DisIL pL pr)       = do
  (p, as) <- runProof pr
  pure (Dis pL p, as)
runProof (DisIR pR pr)       = do
  (p, as) <- runProof pr
  pure (Dis p pR, as)
runProof (DisE pr prEL prER) = do
  (p, as) <- runProof pr
  (pL, pR) <- unDis p
  (eL, asL) <- runProof prEL
  (eR, asR) <- runProof prER
  guard $ eL == eR
  pure (eL, as <> S.delete pL asL <> S.delete pR asR)
runProof (NegI a pr)         = do
  (p, as) <- runProof pr
  guard $ p == Bot
  pure (Neg a, S.delete a as)
runProof (NegE prL prR)      = do
  (pL, asL) <- runProof prL
  (pR, asR) <- runProof prR
  guard $ contradicts pL pR
  pure (Bot, asL <> asR)
runProof (ImpE prL prR)      = do
  (pR, asR) <- runProof prR
  (a, b) <- unImp pR
  (pL, asL) <- runProof prL
  guard $ a == pL
  pure (b, asL <> asR)
runProof (ImpI a pr)         = do
  (p, as) <- runProof pr
  pure (Imp a p, S.delete a as)
runProof (BotE a pr)         = do
  (p, as) <- runProof pr
  guard $ p == Bot
  pure (a, as)
