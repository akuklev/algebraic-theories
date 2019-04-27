# Extended Algebraic Theories

## Introduction
Algebraic theories are (finitely or recursively generated) equational Horn theories over multi-sorted algebraic signatures, i.e. signatures containing no relations or predicates except equality which is considered to be part of surrounding logic, not the theory itself. Algebraic theories are about syntax and equations only, which justifies the name. Instances of algebraic theories include monoids, groups and rings.

The syntactic nature of algebraic theories is represented by the fact that finitely generated free algebras `T<x,..,z>` (“algebras of terms with variables `x,...,z`”) for an algebraic theory `T` can be explicitly constructed, validity of a term remains checkable, and the free algebra `T<>` (the “algebra of terms with no variables”, “the term model of the given algebraic theory”) is the initial object in the category of models for the given algebraic theory.

Unfortunatelly, the formalizm of algebraic theories is too weak to deal with objects like categories, structured categories and category-like objects (multicategories, higher categories, etc), while these objects behave very much like monoids, rings etc. For this reason, there are generalizations seeking to encompass these examples.

Algebraic theories turn out to have a very natural semantics in terms of category theory. Every algebraic theory `T` can be seen as a (finite or recursively generated) presentation for a small finite-product-categories `CartCat<T>`. Models of the theory `T` (the `T`-algebras) correspond to product-preserving functors from `CartCat<T>`, homomorphisms between models to the natural transformations between these functors.

The formalism of essentially algebraic theories (EAT) is a generalization to algebraic theories where one can additionally have positive equational requirements in premises, say
```
   f g : Mor    codom(f) = dom(g)
 –––––––––———————————————————————––
           fg : Mor
```

On the semantic side (EAT retain the functorial semantics described above) this amounts to allowing fibered products of sorts in addition to cartesian products as domains of operations. Thus an EAT `T` is a presentation of a finitely-complete category `LexCat<T>`, the models are given by finite-limit preserving functors, and homomorphisms between models by natural transformations between those. On the logical side, EATs are partial equational Horn theories with some additional restrictions ensuring existence of finitely generated free models. Furthermore it turns out, that arbitrary partial Horn theories can be interpreted in suitably constructed essentially algebraic theories.[PV2006]

Unfortunatelly, the framework of essentially algebraic theories does not retain syntacticality: it is not in possible in general to check if a term in an EAT is valid.

Note that algebraic theories can well have undecidable equality. To give an example, a finitely presented monoid known as the Combinatory Logic – a single-sorted algebraic theory with one binary operation, two constants and two simple axioms – was shown to have undecidable equality as early as 1936. In EATs we're allowed to require equality as a premise for validity of a rule, so if it happens that the sort we're requiring additional equality on, turns out to have undecidable equality in the resulting theory, there is no way to know if we can compose two terms into a new one.

Our goal is to provide a stratified formalism remedying this issue. It will turn out that it subsumes the formalizm of generalized algebraic theories with no equations on sorts, and is closely related to bidirectional dependent type systems.

## Preliminaries
A doctrine (also known as logical setting or “logic” in the narrow sense) is a extendable framework to formal theories and reason about them. First of all, a doctrine defines how a signature for theory has to be described, and, given a signature, how to build all well-formed sentences (both closed and with variables) in the formal language of the theory.

For example in the doctrine of single-sorted first order logic, a signature is a list of operators together with their arities (non-negative integers) called the algebraic part (because algebraic structures like groups, rings or fields are described in terms of operations like addition, negation, multiplication, and constants, being operators of zero arity) and a list of relations together with their arities (positive integers) called the geometric part (because formal Eucledian geometry and similar theories are mainly described in terms of relations like parallelity of lines and similarity of triangles, and predicates being the relations of arity 1). A sentence of a first-order theory is built from atomic sentences using logical connectives (“and”, “or”, “implies”) and quantifiers. The atomic sentences are either built from relations defined in the signature applied to expressions, or
...

## Syntactic formalism

We will provide the definition along with an example: the definition of a semicategory.

An Extended Algebraic Theory (XAT) is given by

1) a finite set of sorts some of which are distinguished as classifying sorts
```
––––––––––     –––––––––—
 Mor sort       Ob class 
```

2) a finite number of named “projections” between types (a distinguished class of function symbols)
```
    f : Mor             f : Mor
–––––––––––––––     ———————————————
 f.source : Ob       f.target : Ob
```

3) a finite (or recursively generated) set generative rules for function symbols and universal equational laws. Premises consist of zero or more typed variables and zero or more equational constraints of a special form: left hand side must be formed by a chain of projection applications to a variable while the right hand side must be an normal (no applications of projections on the outside) term of a sort belonging to a classifying type. Each generative rule has to be accompanied by equational rules of the form “newly-defined-term.projection = normal term” for each applicable projection. Equational laws are allowed only between terms, projections on which agree for all projections.

```
  X Y Z : Ob   f g : Mor   f.source = X   f.target = Y   g.source = Y   g.target = Z
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
       fg : Mor     (fg).source = X     (fg).target = Z
       
       
  (everything we need for fgh to exist)
–––––––––––––––––––––––––––––––––––––––––
             f(gh) = (fg)h
```

There are two additional restrictions:
4) Equational laws are allowed to affect only non-classifying sorts.
5) Rules producing a term belonging to a classifying sort are allowed to contain only variables belonging to classifying sorts.

Before we proceed to the restriction 6, note that the restrictions 4 and 5 guarantee that equality of the normal terms of classifying sorts is decidable (being just the syntactical sameness). 
The accompanying equations for the generative rules in 3 guarantee, that every closed expression is equal to a normal one
The rule 3 only allows to use equality over classifying sorts as a premise.

6) There must be a well-ordering on generative rules and their accompanying rules, ruling out circularity in the generative rules: the validity of premises for every generative rule and expressions in its accompanying rules must be checkable without relying on the accompanying rules being defined. This guarantees that the accompanying rules generate a confluent rewrite system eventually factoring any expression can be factored into projection-free part and a composition of projections, and thus, equality on classifying sorts is decidable. (? relaxing to semidecidability to include ML71 ?)

## Bidirectional example

```
       f : Mor
––––––––––––––––––––––––––
 lam(f) : Lam    apply(e)

```
