# Propositional logic

A project to review some fundamental concepts about logic and deduction systems in a simple way. Specificaly, propositional logic and natural deduction.

Some properties and theorems are used as QuickCheck tests, where propositions and proofs are generated randomly. 

A type-level experiment with a disappointing ending is also provided. It tries to reflect some syntactic structure of a proposition in order to provide a type-safe natural deduction proof tree, but it reveals two problems:

* It seems that all the syntactic information of a proposition should be reflected in the type for that purpose.
* Even by adding just a tiny piece of this information in the type, it involves boilerplate code and complications (e.g. type level counterpart for functions, heterogeneous data structures for storing propositions or existential types, etc.)
