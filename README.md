# Extended Algebraic Theories

## Introduction
Algebraic theories are (finitely or recursively generated) equational Horn theories over a multi-sorted algebraic signature, i.e. signatures containing no relations or predicates except equality which is considered to be part of surrounding logic, not the theory itself. Algebraic theories are about syntax (symbols and rules for manipluating them) and equations, which justifies the name. Instances of algebraic theories include monoids, groups and rings.

The syntactic nature of algebraic theories is represented by the fact that finitely generated free algebras `T<x,..,z>` (“algebras of terms with variables `x,...,z`”) for an algebraic theory `T` can be explicitly constructed, validity of a term remains checkable, and the free algebra `T<>` (the “algebra of terms with no variables”, “the term model of the given algebraic theory”) is the initial object in the category of models for the given algebraic theory.

Unfortunatelly, the formalizm of algebraic theories is too weak to deal with objects like categories, structured categories and category-like objects (multicategories, higher categories, etc), while these objects behave very much like monoids, rings etc. For this reason, there are generalizations seeking to encompass these examples.

Algebraic theories turn out to have a very natural semantics in terms of category theory. Every algebraic theory `T` can be seen as a (finite or recursively generated) presentation for a small finite-product-categories `CartCat<T>`. Models of the theory `T` (the `T`-algebras) correspond to product-preserving functors from `CartCat<T>`, homomorphisms between models to the natural transformations between these functors.

The formalism of essentially algebraic theories (EAT) is a generalization to algebraic theories where one can additionally have positive equational requirements in premises, say
<pre>
```
 f g : Mor   f.target = g.source
–––––––––————————————————————————–––
          fg : Mor
```</pre>

On the semantic side (EAT retain the functorial semantics described above) this amounts to allowing fibered products of sorts in addition to cartesian products as domains of operations. Thus an EAT `T` is a presentation of a finitely-complete category `LexCat<T>`, the models are given by finite-limit preserving functors, and homomorphisms between models by natural transformations between those. On the logical side, EATs are partial equational Horn theories with some additional restrictions ensuring existence of finitely generated free models. Furthermore it turns out, that arbitrary partial Horn theories can be interpreted in suitably constructed essentially algebraic theories.[PV2006]

Unfortunatelly, the framework of essentially algebraic theories does not retain syntacticality: it is not in possible in general to check if a term in an EAT is valid.

Note that algebraic theories can well have undecidable equality. To give an example, a finitely presented monoid known as the Combinatory Logic – a single-sorted algebraic theory with one binary operation, two constants and two simple axioms – was shown to have undecidable equality as early as 1936. In EATs we're allowed to require equality as a premise for validity of a rule, so if it happens that the sort we're requiring additional equality on, turns out to have undecidable equality in the resulting theory, there is no way to know if we can compose two terms into a new one.

Our goal is to provide a stratified formalism remedying this issue. It will turn out that it subsumes the formalizm of generalized algebraic theories with no equations on sorts, and is closely related to bidirectional dependent type systems.

## Syntactic formalism

We will provide the definition along with an example: the definition of a semicategory.

An Extended Algebraic Theory (XAT) is given by

1) a finite set of sorts some of which are distinguished as classifying sorts
``
––––––––––     –––––––––—
 Mor sort       Ob class 
``

2) a finite number of named “projections” between types
``
    f : Mor             f : Mor
–––––––––––––––     ———————————————
 f.source : Ob       f.target : Ob
``

3) a finite (or recursively generated) syntactic rules: premises are allowed to 
