-- |
-- Module      : Semantics
-- Copyright   : (c) Adrián Enríquez Ballester, 2022
--
-- Semantics of propositional logic.

module Semantics
  ( Assignment
  , sat
  , true
  , satSet
  , valid
  , entails
  ) where

import qualified Data.Map   as M
import           Data.Maybe (fromMaybe)
import qualified Data.Set   as S
import           Syntax     (Prop (..), vars)

-- | An assignment of truth values to atom names of type @v@.
type Assignment v = v -> Bool

-- | Compute the truth value of a proposition under an assignment.
true :: Assignment v -> Prop v -> Bool
true _          Bot       = False
true assignment (Ato v)   = assignment v
true assignment (Neg p)   = not $ true assignment p
true assignment (Con p q) = true assignment p && true assignment q
true assignment (Dis p q) = true assignment p || true assignment q
true assignment (Imp p q) = not (true assignment p) || true assignment q

-- | Naive check for the satisfiability of a given proposition.
sat :: Ord v => Prop v -> Bool
sat = satSet . S.singleton

-- | Naive check for the validity of a given proposition.
valid :: Ord v => Prop v -> Bool
valid = entails mempty

-- | Naive check for the satisfiability of a set of propositions.
satSet :: Ord v => S.Set (Prop v) -> Bool
satSet ps =
  any ((`all` ps) . true)
    $ variants
    $ S.unions
    $ S.map vars ps

-- | Naive check for the entailment of a proposition by a set of
-- given propositions.
entails :: Ord v => S.Set (Prop v) -> Prop v -> Bool
entails ps q =
  all (`true` q)
    $ filter ((`all` ps) . true)
    $ variants
    $ S.unions
    $ S.map vars
    $ S.insert q ps

-- | All the variant assignments with respect to a given set of
-- atom names.
variants :: Ord v => S.Set v -> [Assignment v]
variants = map ((fromMaybe False .) . flip M.lookup) . go . S.toList
  where
    go []     = [mempty]
    go (v:vs) = do
      assignment <- go vs
      [assignment, M.insert v True assignment]
