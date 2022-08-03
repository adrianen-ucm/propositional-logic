{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Main where

main :: IO ()
main = putStrLn "TODO an example"

-- * Syntax

-- | A data type to be promoted to the kind level
-- for specifying the shape of a proposition in its type.
data PropT
  = BotT
  | AtoT
  | NegT PropT
  | ConT PropT PropT

-- | GADT for a proposition with variable names of type @v@.
-- Each constructor reflects the shape of the resulting proposition
-- in a phantom type @s@ of kind 'PropT'.
data Prop (s :: PropT) v where
  Bot :: Prop 'BotT v
  Ato :: v -> Prop 'AtoT v
  Neg :: Prop s v -> Prop ('NegT s) v
  Con :: Prop s1 v-> Prop s2 v -> Prop ('ConT s1 s2) v

deriving instance Eq v => Eq (Prop s v)

deriving instance Show v => Show (Prop s v)

class PropsEq (p :: PropT) (q :: PropT) where
  propsEq :: Eq v => Prop p v -> Prop q v -> Bool

instance PropsEq s s where
  propsEq = (==)

instance PropsEq s1 s2 where
  propsEq _ _ = False

-- | A data type to be promoted to the kind level
-- for specifying the shape of an heterogeneous list of
-- propositions.
data PropListT
  = NilT
  | ConsT PropT PropListT

-- | An heterogeneous list of propositions.
data PropList (l :: PropListT) v where
  Nil  :: PropList 'NilT v
  Cons :: Prop s v -> PropList l v -> PropList ('ConsT s l) v

deriving instance Show v => Show (PropList l v)

-- | Concatenation for heterogeneous lists of propositions.
concatPropList :: PropList l1 v -> PropList l2 v -> PropList (ConcatPropList l1 l2) v
concatPropList Nil l2         = l2
concatPropList (Cons p l1) l2 = Cons p $ concatPropList l1 l2

type family ConcatPropList (a :: PropListT) (b :: PropListT) :: PropListT where
  ConcatPropList 'NilT b        = b
  ConcatPropList ('ConsT p l) b = 'ConsT p (ConcatPropList l b)

-- * Natural deduction proof

-- | A data type to be promoted to the kind level
-- for specifying the shape of the assumptions in a proof tree.
data AssumptionsT
  = EmptyT
  | OpenT PropT AssumptionsT
  | DischargeT PropT AssumptionsT
  | JoinT AssumptionsT AssumptionsT

-- | GADT for a natural deduction proof tree. It keeps track in the
-- phantom types @a@ and @s@ the shape of the assumptions and
-- conclusion respectively.
data Proof (a :: AssumptionsT) (s :: PropT) v where
  Assumption :: Prop s v -> Proof ('OpenT s 'EmptyT) s v
  NegI       :: Prop p v -> Proof a 'BotT v -> Proof ('DischargeT p a) ('NegT p) v
  NegE       :: Proof a1 p1 v -> Proof a2 p2 v -> Proof ('JoinT a1 a2) 'BotT v
  ConI       :: Proof a1 s1 v -> Proof a2 s2 v -> Proof ('JoinT a1 a2) ('ConT s1 s2) v
  ConEL      :: Proof a ('ConT s1 s2) v -> Proof a s1 v
  ConER      :: Proof a ('ConT s1 s2) v -> Proof a s2 v
  BotE       :: Prop p v -> Proof a 'BotT v -> Proof a p v

deriving instance Show v => Show (Proof a s v)

-- | Obtain the list of assumptions from a proof tree.
assumptions :: Proof a s v -> PropList (Assumptions a) v
assumptions (Assumption p) = Cons p Nil
assumptions (ConI pr1 pr2) = concatPropList (assumptions pr1) (assumptions pr2)
assumptions (ConEL pr)     = assumptions pr
assumptions (ConER pr)     = assumptions pr
assumptions (NegI _ pr)    = assumptions pr
assumptions (NegE pr1 pr2) = concatPropList (assumptions pr1) (assumptions pr2)
assumptions (BotE _ pr)    = assumptions pr

type family Assumptions (a :: AssumptionsT) :: PropListT where
  Assumptions 'EmptyT       = 'NilT
  Assumptions ('OpenT a as) = 'ConsT a (Assumptions as)
  Assumptions ('DischargeT a as) = Assumptions as
  Assumptions ('JoinT a1 a2) = ConcatPropList (Assumptions a1) (Assumptions a2)

-- | Check if a proposition is an open assumption in
-- a proof tree.
isOpenAssumption :: Eq v => Proof a s2 v -> Prop s1 v -> Bool
isOpenAssumption (Assumption p) q = not $ propsEq p q
isOpenAssumption (ConI pr1 pr2) q = isOpenAssumption pr1 q || isOpenAssumption pr2 q
isOpenAssumption (ConEL pr)     q = isOpenAssumption pr q
isOpenAssumption (ConER pr)     q = isOpenAssumption pr q
isOpenAssumption (NegI p pr)    q = not (propsEq p q) && isOpenAssumption pr q
isOpenAssumption (NegE pr1 pr2) q = isOpenAssumption pr1 q || isOpenAssumption pr2 q
isOpenAssumption (BotE _ pr)    q = isOpenAssumption pr q

-- | Check if a proof has any open assumption.
anyOpenAssumption :: Eq v => Proof a s v -> Bool
anyOpenAssumption pr = go pr $ assumptions pr
  where
    go :: Eq v => Proof a s v -> PropList l v -> Bool
    go _ Nil          = False
    go pr' (Cons p l) = isOpenAssumption pr' p || go pr' l

-- | Compute the conclusion of a proof.
conclusion :: Eq v => Proof a s v -> Prop s v
conclusion (Assumption p) = p
conclusion (ConI pr1 pr2) = Con (conclusion pr1) (conclusion pr2)
conclusion (ConEL pr)     =
  let Con p _ = conclusion pr
  in p
conclusion (ConER pr)     =
  let Con _ q = conclusion pr
  in q
conclusion (NegI a _)     = Neg a
conclusion (NegE pr1 pr2) =
  let p1 = conclusion pr1
      p2 = conclusion pr2
  in case (p1, p2) of
      (Neg p, q) | propsEq p q -> Bot
      (p, Neg q) | propsEq p q -> Bot
      _                        -> error ":("
conclusion (BotE a _)     = a
