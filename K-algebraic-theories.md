This is an attempt to provide a formalism similar to that of algebraic theories, for definitions of K-algebras over a generalised field `K`. We will be keeping in mind two kinds of generalised fields: the classical fields and the "field with one element" as defined by A. Connes in [Co1].


§ Category of Sets and Partial Maps seen as Vect_F1
---------------------------------------------------

In computer science, each well-typed programming language "L" defines a category of data types and well-formed programs as maps between them. Due to halting problem, each language either misses some computable maps (i.e. some of the computable maps cannot be expressed in the given language), or allows some well-typed programs that never yield a result in some cases (i.e. never "halt"), in the latter case one has to do with a category of sets and partial maps between them.

The category of sets and maps functions can be seen as a category of pointed sets and with point-preserving (total) maps. It is, sets are augmented with additional "sticky element" `⊥` and programs that never halt are formally assumed to return the "non-value" `⊥`. The "stickiness", means that each map returns `⊥` when applied to `⊥`: a function applied to an argument that would not evaluate in a finite time will also not evaluate in a finite time.




§ Partial Horn Theories
-----------------------

The eminent paper of Palmgren and Vickers “Partial Horn Theories and Cartesian Categories” defines a logic where
