# Extended Algebraic Theories

Making use of recently developed notion of weak model categories [Hen19], we propose a refinement for the notion of essentially algebraic theories (EATs) [PV07] that leads to more sophisticated functorial semantics yielding more relaxed notion of homomorphism of algebras. Similar to essentlially algebraic theories, our proposal encompases categories, yet with functors and equivalences as homomorphisms and isomorphisms respectively. For theories `T` admitting unbiased descriptions (ones where for every composite tree there is exactly one equation, identifying the composite tree with an atomic one) we derive a notion of generic enrichment structure `G(T)` — for categories being virtual double categories – and `V`-enriched `T`-algebras, `V` being a fixed `G(T)`-algebra.

Much like algebraic theories and generalized algebraic theories without equations on sorts [Car81], yet in contrast to EATs, our proposal keeps applicability of formation rules decidable regardless of word problem decidablity for the respective theory, thus we argue it to be not only an essentially, but a truly algebraic formalism. Thus we pursue the approach of [Is17] regarding type theories as algebraic presentations of structured categories and category-like structures.

## Presentation of the Formalism
Please recall that a finitary algebraic theory can be identified with a finitely presented finite product category `T`. Syntactic description of an algebraic category is precisely the presentation of such a category in terms of generators and relations:
1) It provides a number of sorts: objects of `T` will be the finite products of these sorts;
2) It provides a number of formation rules of the form `f : S -> T`, where `S` is a finite product of sorts and `T` a single sort. Maps of `T` will be precisely the finite compositions of formation rules and structural maps inherent to a finite product category (permutation, duplication and discarding maps).
3) In provides a number of equations, which will be used to identify some of the morphisms generated above.

A model of an algebraic theory `T` can be identified with a functor from `T`, a homomorphsim between theories can be identified with a natural transformation between corresponding functors.

Finitary essentially algebraic theories correspond to finitely presented lex categories, i.e. categories with all finite limits. Syntactically it means that `S` in formation rules `f : S -> T` are allowed not only to be finite products of sorts, but finite fibered products, allowing for rules like
```
 f : Mor   g : Mor   f.target = g.source
–––––––––––––––––––––––––––––––––––––––––
              fg : Mor
```
Which are essential for definitions of category-like structures.

Extended algebraic theories will be identified with weak model categories as defined in [Hen19]. A weak model category is not required to have fibered products or even finite products of all of its objects. At first it is only required to have an initial and a terminal object. Weak model categories come with two distinguised classes of maps called fibrations `X ↠ Y` and cofibrations `A ↪ B` closed under compositions and subject to a number of further axioms. One of the axioms states that the fibered product `(x : X) ✕_Z (y : Y) {x.proj = f(y)}` exists for any object `X`, map `f` and fibration `proj` if `Y` and `Z` are fibrant objects (the objects for which the unique map `X ↠ 1` is a fibration).

When describing an extended algebraic theory, we'll be listing sorts explicitly saying if they are to be fibrant, cofibrant or both. Formation rules will generate the class of cofibrations. We'll introduce new kind of rules for describing projections (like `f.source` and `f.target` in the above example); they will be generating the class of fibrations.




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
