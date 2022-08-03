-- |
-- Module      : Syntax
-- Copyright   : (c) Adrián Enríquez Ballester, 2022
--
-- Syntax of propositional logic.

module Syntax
  ( Prop (..)
  , unCon
  , unDis
  , unImp
  , iff
  , top
  , vars
  , contradicts
  ) where

import qualified Data.Set as S

-- | Data type of a proposition with atom names of type
-- @v@. Although some of them can be defined by combining
-- others, the following are provided as data constructors:
data Prop v
  = Bot                   -- ^ Bottom
  | Ato v                 -- ^ Atom
  | Neg (Prop v)          -- ^ Negation
  | Con (Prop v) (Prop v) -- ^ Conjunction
  | Dis (Prop v) (Prop v) -- ^ Disjunction
  | Imp (Prop v) (Prop v) -- ^ Implication
  deriving (Eq, Ord, Show)

-- | The set of atom names that occur in a given proposition.
vars :: Ord v => Prop v -> S.Set v
vars Bot       = mempty
vars (Ato v)   = S.singleton v
vars (Neg p)   = vars p
vars (Con p q) = vars p <> vars q
vars (Dis p q) = vars p <> vars q
vars (Imp p q) = vars p <> vars q

-- | Double implication as a conjunction of implications.
iff :: Prop v -> Prop v -> Prop v
iff p q = Con (Imp p q) (Imp q p)

-- | Top as the negation of bottom.
top :: Prop v
top = Neg Bot

-- | Deconstruct a conjunction:
--
-- > unCon (Con p q) == Just (p, q)
unCon :: Prop v -> Maybe (Prop v, Prop v)
unCon (Con p q) = Just (p, q)
unCon _         = Nothing

-- | Deconstruct a disjunction:
--
-- > unDis (Dis p q) == Just (p, q)
unDis :: Prop v -> Maybe (Prop v, Prop v)
unDis (Dis p q) = Just (p, q)
unDis _         = Nothing

-- | Deconstruct an implication:
--
-- > unImp (Imp p q) == Just (p, q)
unImp :: Prop v -> Maybe (Prop v, Prop v)
unImp (Imp p q) = Just (p, q)
unImp _         = Nothing

-- | Check if two propositions have the syntactic
-- shape of a contradiction:
--
-- > contradicts (Neg p) p == contradicts p (Neg p) == True
contradicts :: Eq v => Prop v -> Prop v -> Bool
contradicts (Neg p) q | p == q = True
contradicts p (Neg q) | p == q = True
contradicts _ _                = False
