# Propositional logic

A project to review some fundamental concepts about logic and deduction systems in a simple way. Specificaly, propositional logic and natural deduction.

As the semantic notions of propositional logic are decidable, some properties and theorems are used as QuickCheck tests, where propositions and natural deduction proofs are generated randomly:

```haskell
prop_SoundProof :: Proof -> Bool
prop_SoundProof (Proof (pr, _)) =
  case runProof pr of
    Just (p, assumptions) -> entails assumptions p
    Nothing               -> False
```

A type-level experiment with a disappointing ending is also provided. It tries to reflect some syntactic structure of a proposition in its type in order to 
enforce that a natural deduction proof tree is well formed, but some problems arise:

* It seems that all the syntactic information of a proposition should be reflected in the type for that purpose.
* Even by adding just a tiny piece of this information in the type, it involves boilerplate code and complications (e.g. type level counterpart for functions, heterogeneous data structures or existential types for working with propositions of different shapes, etc.)
