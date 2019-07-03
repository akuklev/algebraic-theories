# Extended Algebraic Theories

Making use of recently developed notion of weak model categories [Hen19], we propose a refinement for the notion of essentially algebraic theories (EATs) [PV07] that leads to more sophisticated functorial semantics yielding more relaxed notion of homomorphism of algebras. Similar to essentlially algebraic theories, our proposal encompases categories, yet with functors and equivalences as homomorphisms and isomorphisms respectively. For theories `T` admitting unbiased descriptions (ones where for every posible composite term there is exactly one equation law, identifying the composite term with an atomic one) we derive a notion of generic enrichment structure `G(T)` — for categories being virtual double categories – and `V`-enriched `T`-algebras, `V` being a fixed `G(T)`-algebra.

Much like algebraic theories and generalized algebraic theories without equations on sorts [Car81], yet in contrast to EATs, our proposal keeps applicability of formation rules decidable regardless of word problem decidablity for the respective theory, thus we argue it to be not only an essentially, but a truly algebraic formalism. Thus we pursue the approach of [Is17] regarding type theories as algebraic presentations of structured categories and category-like structures.

## Presentation of the Formalism
Please recall that a finitary algebraic theory can be identified with a finitely presented finite product category `T`. Syntactic description of an algebraic category is precisely the presentation of such a category in terms of generators and relations:
1) It provides a number of sorts: objects of `T` will be the finite products of these sorts;
2) It provides a number of formation rules of the form `f : S -> T`, where `S` is a finite product of sorts and `T` a single sort. Maps of `T` will be precisely the finite compositions of formation rules and structural maps inherent to a finite product category (permutation, duplication and discarding maps).
3) In provides a number of equations, which will be used to identify some of the morphisms generated above.

A model of an algebraic theory `T` can be identified with a product-preserving functor from `T`, a homomorphsim between theories can be identified with a natural transformation between corresponding functors.

Finitary essentially algebraic theories correspond to finitely presented lex categories, i.e. categories with all finite limits. Syntactically it means that `S` in formation rules `f : S -> T` are allowed not only to be finite products of sorts, but finite fibered products, allowing for rules like
```
 f : Map   g : Map   f.target = g.source
–––––––––––––––––––––––––––––––––––––––––
              fg : Map
```
Which are essential for definitions of category-like structures.

This approach has two drawbacks:
1) One requires existance of all fibered products while only few are required. Solution: consider categories with distinguished class of objects (“classifying sorts”) and maps (“projections“) and require only fibered products of the form `(x : X) ✕_Z (y : Y) {x.proj = f(y)}` where `proj` is a projection and `Z` is a classifying sort.
2) The identification of models and limit-preserving functors is not accurate: one actually only needs the functors to be defined on the full subcategory spanned by “esssential sorts” (the sort of maps in case of categories), while all other sorts (the sort of objects in case of categories) are there only to carry elusive compatibility structure of “substatial” objects and should be taken into account only to the extent they are indispensible. The solution is provided by the doctrine of weak model categories and Quillen pairs between them.

Extended algebraic theories will be identified to (a restricted form of) weak model categories as defined in [Hen19]. Weak model categories come with two distinguised classes of maps called fibrations `X ↠ Y` and cofibrations `A ↪ B` closed under compositions and subject to a number of further axioms. They are required to have initial and terminal objects with unique map between them being both fibration and cofibration. The objects for which the unique map `X ↠ 1` is a fibration are called fibrant, respectively the objects for which the unique map `0 ↪ X` is a cofibration are called cofibrant. In the framework of extended algebraic theories, the class of cofibrant objects is intended to be spanned by “substantial sorts”, the class of fibrant objects by “classifying sorts”, fibrations by projections, cofibrations by conversions (see below). Besides projections and constructions there are still the usual formation rules inherited from plain old algebraic theories. 

A syntactical description of an extended algebraic theory goes as follows:

1) a finite set of sorts marked as classifying, substantial or both
```
––––––––—     ––––––––
 Map ess       Ob cls 
```

2) a finite number of named projections and conversions (conversions are not required for the definition of plain categories)
```
    f : Map             f : Map
–––––––––––––––     ———————————————
 f.source : Ob       f.target : Ob
```

3) a finite (or recursively generated) set generative rules for function symbols and universal equational laws. Premises consist of zero or more typed variables `x, y,...,z` and zero or more equational constraints of a special form: left hand side must be formed by a projection-free expression followed by a chain of projection applications ultimately landing in classifying sort, while right hand side is any expression possibly containing variables `x, y,...,z`. Each generative rule has to be accompanied by equational rules of the form `newly-defined-term.proj = term` for each applicable projection `proj`. Furthermore for every conversion `conv` into a type one must provide a term implementing the generative rule. These accompanying rules are called β-reductions and η-expansions respectively and should generate a confluent rewrite system eventually rewriting any expression of a classifying sort a projection-free form. To rule out circularity (to prove normalization we need the applicability of rules to be checkable, which relies on normalization), we need to provide a well-ordering on generative rules and their accomanying rules.

Equational laws required to respect projections, i.e. they are allowed only between terms, projections on which agree for all projections.

```
  X Y Z : Ob   f g : Map   f.source = X   f.target = Y   g.source = Y   g.target = Z
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
       fg : Map     (fg).source = X     (fg).target = Z
       
       
  (everything we need for fgh to exist)                                O : Ob
–––––––––––––––––––––––––––––––––––––––––        –––––––––––––——————————————————————————————————————
             f(gh) = (fg)h                        id_O : Map  (id_O).source = O   (id_0).target = O

  (everything we need for f id_O to exist)          (everything we need for id_O f to exist)
—————————————————————————————————————————————      ——————————————————————————————————————————
               f id_O = f                                          id_O f = f
```

There are two additional restrictions:
– Equational laws are allowed to affect only non-classifying sorts.
– Rules producing a term belonging to a classifying sort are allowed to contain only variables belonging to classifying sorts.

These are to ensure decidability of equality on classifying sorts in the syntactic model, which is necessary for applicability of generational rules (and equational laws) to be decidable. 


## Bidirectional example

FinProd categories

```
                     p : Pair          p : Pair
————————————      —————————————      —————————————
 Pair cofib        p.fst : Map        p.snd : Map


 Г A B : Ob    f g : Map    f.source = Г   g.source = Г   f.target = A    g.target = B
————————————————————————————————————————————————————————————————————————————————————————
                <f, g> : Pair   <f, g>.fst = f    <f, g>.snd = g

  A B : Ob         Г A B : Ob    p : Map    p.source = Г   p.target = A × B
————————————      ——————————————————————————————————————————————————————————
 A × B : Ob                           p^eta : Pair     p^eta = <p1 p, p2 p>
 
                       A B : Ob
—————————————————————————————————————————————————————————————————
  p1[A,B] : Mor   p1[A,B].source = (A × B)    p1[A,B].targer = A


                       A B : Ob
—————————————————————————————————————————————————————————————————
  p1[A,B] : Mor   p1[A,B].source = (A × B)    p1[A,B].targer = B

```


Lex categories:

```
 A B Z : Ob   f g : Map   f.source = A   g.source = B   f.target = g.target = Z
————————————————————————————————————————————————————————————————————————————————
    
```


```
       f : Map
––––––––––––––––––––––––––
 lam(f) : Lam    apply(e)



```




## Introduction
Algebraic theories are about syntax and equations only, which justifies the name. Instances of algebraic theories include monoids, groups and rings.

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
A doctrine (also known as logical setting or simply “logic” in the narrow sense) is a extendable framework to formal theories and reason about them. First of all, a doctrine defines how a signature for theory has to be described, and, given a signature, how to build all well-formed sentences (both closed and with variables) in the formal language of the theory.

For example in the doctrine of (single-sorted) first order logic, a signature is a list of operators together with their arities (non-negative integers) called the algebraic part (because algebraic structures like groups, rings or fields are described in terms of operations like addition, negation, multiplication, and constants, being operators of zero arity) and a list of relations together with their arities (positive integers) called the geometric part (because formal Eucledian geometry and similar theories are mainly described in terms of relations like parallelity of lines and similarity of triangles, and predicates being the relations of arity 1). A sentence of a first-order theory is built from atomic sentences using logical connectives (“and”, “or”, “implies”) and quantifiers. The atomic sentences are either built from relations defined in the signature applied to expressions, or of the forms `expression1 = expression2`. Expressions formed by composing the operators defined in the signature respecting their arities, the atomic expressions being either constants (operators of zero arity) or variables. Many doctrines do not include inbuilt equality (in this case no sentencies can be formed in a theory without relations). In first order logic, variables are allowed to be used multiple times in the expression/sentence. Other doctrines (in particular linear, affine and relevant logics) may restrict multiple usage of variables, in expressions thus rendering sentences like “x ∘ ~x = e” non-well-formed while allowing “xy = yx”.

In multi-sorted first order logic, signature begins with a finite list of sorts, and arities of operators and relations are not mere numbers anymore, but lists of types of arguments (for operators, the resulting type must be specified as well).

Beyond syntax, a doctrine specifies the inference laws, in particular regarding inbuilt connectives and relations (i.e. equality in doctrines containing equality).

A formal theory is a set of sentences in a given formal language over a given doctrine, closed under inference rules of the doctrine.

Horn logic is a particularily well-behaved fragment of first order logic, where the form of sentences closely reassembles the signature.

...

[Hen19] Simon Henry, “Weak model categories in classical and constructive mathematics”, https://arxiv.org/abs/1807.02650
[PV07] Erik Palmgren, Steve Vickers, “Partial Horn logic and cartesian categories.” Annals of Pure and Applied Logic, 145(2007), 314-355. http://www2.math.uu.se/~palmgren/partialalgebras_pre.pdf
[Law3] F. William Lawvere, “Functorial Semantics of Algebraic Theories”, Proceedings of the National Academy of Sciences 50, No. 5 (November 1963), 869-872
[Is17] Isaev, V., 2017 “Algebraic Presentations of Dependent Type Theories”, https://arxiv.org/abs/1602.08504
