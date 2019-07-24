Extended Algebraic Theories
---------------------------

Making use of recently developed notion of weak model categories [Hen19], we propose a refinement for the notion of essentially algebraic theories (EATs) [PV07] that leads to more sophisticated functorial semantics yielding more relaxed notion of homomorphism of algebras. Similar to essentlially algebraic theories, our proposal encompases categories, yet with functors and equivalences as homomorphisms and isomorphisms respectively. For theories `T` admitting unbiased descriptions (ones where for every posible composite term there is exactly one equation law, identifying the composite term with an atomic one) we derive a notion of generic enrichment structure `G(T)` — for categories being virtual double categories – and `V`-enriched `T`-algebras, `V` being a fixed `G(T)`-algebra.

Much like algebraic theories and generalized algebraic theories without equations on sorts [Car81], yet in contrast to EATs, our proposal keeps applicability of formation rules decidable regardless of word problem decidablity for the respective theory, thus we argue it to be not only an essentially, but a truly algebraic formalism. Thus we pursue the approach of [Is17] regarding type theories as algebraic presentations of structured categories and category-like structures.

# Introduction
The starting point for our endeavour was the analogy between bidirectional presentation of type theories and weak model categories.

Bidirectional presentation exibits three kinds of expressions:
- radicals of the form `(t : T)`;
- terms `t` which can reified into a radical `(t : T)` when typechecked against `T`;
- redexes `r` which can be evaluated into a radical.

This somehow corresponds to bifibrant, fibrant and cofibrant objects, the evaluation `Redex ↪̃ Rad` of a redex into a radical to the fibrant replacement, and the forgetful map `Rad ↠̃ Term` from radicals into terms to the cofibrant replacement. Fibrations are the projections, the maps that extract information. Cofibrations are {{TBC}}

# Weak model categories
A subcategory `D` of `C` is replete if for any object `x` in `D` and any isomorphism `f : x ≅ y` in `C`, both `y` and `f` are also in `D`.

A category `C` with projections is a category with a distinguished replete subcategory `C^↠` of “projections” (or “fibrations”, denoted by `X ↠ Y`) and “fibrant” objects with the following properties:
– `C^↠` has finite products. In particular, if it's non-empty, it has a terminal object `1` which is also the terminal object of `C`, and `C` has all finite products of fibrant objects. Fibrant objects can be equivalently characterized by the property that the unique map `X -> 1` is a projection.
- Given objects `X`, `Y` and `B` from `C^↠`, a projection `p : X -> B` and a map `f : Y -> B`, there is a fibered product `X ×₍p = f₎ Y`, and the canonical projections `fst : X ×₍p = f₎ Y ↠ X` and `snd : X ×₍p = f₎ Y ↠ Y` belong to `C^↠`. It means in particular, that `C^↠` has all finite limits. But it's more than that since it requires only `p` to be a projection for the fibered product to exist, while `f` may be any map.

Dually, a category `C` with inclusions is a category with  a distinguised replete subcategory `C^↪` of “inclusions” (or “cofibrations”, denoted by `A ↪ B`) and “cofibrant objects” having all finite disjoint sums and amalgamated sums, with one leg being an indlusion: given objects `X`, `Y` and `B` from `C^↪`, an inclusion `i : B ↪ X` and a map `f : B -> Y`, there is a pushout `X ⊔₍i ⨝ f₎ Y` and the canonical inclusions `inl: X ↪ X ⊔₍i ⨝ f₎ Y` and `inr: Y ↪ X ⊔₍i ⨝ f₎ Y` belong to `C^↪`.

Similarily, if `C^↪` is nonempty, `C` has a final object `0` which is also the final object of `C^↪`. Thus cofibrant objects can be equivalently characterized by the property that unique map `0 -> X` is an inclusion.

In a category with both inclusions and projections, an object will be called bifibrant if it is both fibrant
and cofibrant. The full subcategories spanned by fibrant, cofibrant and bifibrant objects will be denoted by `C^fib`, `C^cof` and `C^bif` respectively.

Given two maps `i : A -> B` and `p : X -> Y` in a category `C`, we write `i ⋔ p` if for any two given maps `f : A -> X` and `g : B -> Y` there is a map `w : B -> X` so that `iw = f` and `wp = g`. (We use the diagrammatic order for compositions `fg = g ∘ f `.) It is, any map `f : A -> X` factors through `i` (thus `i` is injective with respect to `X`), for any map `g : B -> Y` we can find such `w : B -> X` that `g = wp`, so `p` (thus `p` is surjective with respect to `B`), furthermore this can be performed simultaneously.

In a category with both inclusions and projections, a projection `p` is called trivial if `i ⋔ p` for all inclusions `i`. Dually, an inclusion is called trivial if `i ⋔ p` for all projections `p`. (TODO: Explain meaning.)

Weak model category is a category `C` with inclusions and projections, having a terminal object and satisfying the following conditions:
- Any map from a cofibrant object to a fibrant object can be factored both as an inclusion followed by a trivial projection and as a trivial inclusion followed by a projection.
- For any bifibrant object `A` and any factorization `Id_A : A ↪ B ↠̃ A` of the identity of `A` as an inclusion followed by a trivial projection, the inclusion is trivial as well.

Model “functor” between two weak model categories `C` and `D` consists of a pair of functors `f : C^fib -> D` sending projections to projections and `f' : D^cof -> C` sending inclusions to inclusions, adjoint on their common ground, i.e. 
`Hom(F(X), Y) ≃ Hom(X, G(Y))`
functorial in `X ∈ C^cof` and `Y ∈ D^fib`.

We adopt a slight modification of definition in [Hen19] allowing for weak model categories degenerate subcategories of inclusions or projections to recover a finite-product categories and product-preserving functors between them (Lawvere theories) as a trivial case of weak model categories and model functors between them, by equiping finite-product categories with trivial weak model structure: let the subcategory of inclusions be empty, and the subcategory of projections be the wide subcategory of `C` with maps composed out of isomorphisms and canonic projections of direct products (always nonempty since a finite-product category always has a terminal object). Now consider the model functor from such a category into a model category `D`. It consists of a functor `f` from `C` to `D` mapping projections into projections (thus product-preserving), and a functor `f' : D^cof -> C`. Since `f'` has to map inclusions to inclusions, and `C` has none, the category `D` also has to have no inclusions as well.

In order to interpret XATs in weak model categories we'll need an additional property, the Frobenius condition:
— Fibered products preserve trivial inclusions.


# Exposition of the Formalism

Extended algebraic theories will be given in form of rules interpretable in weak model categories. A set of rules of the theory will be used to define a specific small weak model category serving as the generic (or “free”) model of the theory. All other models will be given by model functors from the generic model, which can be recovered as the initial object of the category of models of the given theory.

First three kinds or rules are the same for plain algebraic theories: we may define a number of sorts, generative rules for expressions of givens sorts, and equational laws on these sorts, for example:
```
———————    ———————
 M alg      T alg
 
            a : M    t : T        t : T
———————    ————————————————    ———————————
 e : M          at : T           em = m
```

Here we define two algebraic sorts `M` and `T`, a constant `e` of the sort `M`, a binary operator (juxtaposition) forming an expression of the sort `T` from an expression of the sort `M` and expression of the sort `T`, and an equation law telling that the constant `e` is left identity for this operator. Algebraic types and operators between them are be interpreted by fibrant objects and maps.

We may declare some sorts to be syntactic rather than algebraic:
```
————————
 Ob syn
```
In this case it is forbidden to define equational laws on these sorts, and to introduce operators with arguments of algebraic types (because they might have custom equational laws in the theory we're defining or its extensions, which would than impose equational laws on syntactic sorts). While algebraic sorts are intended to modeled by sets (hsets in ∞-toposes) or similar entities with inherent notion of equality, syntactic sorts are meant to be have emergent notion of equivalence, instead of equality. The primary example is the sort `Ob` of objects in categories: internally to the theory, there is no such relation as equality on objects (and if there were, it would violate the principle of equivalence), externally the correct notion of equivalence on objects emerges from the definition of categories and turns out to be the set of isomorphisms between the objects (in particular, syntactic sorts are not always modelled by hsets in ∞-toposes; the XAT definition of categories yields univalent categories as models). Syntactic sorts are interpreted by bifibrant objects. In many cases it is possible to define a notion of large set-theoretic models for an XAT, where syntactic sorts are modeled by proper classes rather than sets (in case of categories, it yields locally small large categories).

Let's move on:
```
                 f : Map            f : Map
—————————    ———————————————    ———————————————
 Map alg      f.source : Ob      f.target : Ob
```

We may define one or more projections for any algebraic or syntactic sort. Such rule has precisely one argument and precisely one outcome. Whenever we provide a generative rule for an expression of a sort with projections, we have to specifiy the value of projections:

```
           o : Ob
—————————————————————————————————————
 id₍o₎ : Map[source = o, target = o]
```

In our applications, we'll encounter countless cases of sorts with precisely these two projections (`source` and `target`), so it makes sence to introduce a shorthand notation (which is already very common among type theorists):
– Let `src ⊢₍ArrowSort₎ f : tgt` always denote `f : ArrowSort[source = src, target = tgt]`. In many cases we'll have multiple types of “arrow sorts” such as functors and proarrows or 1-cells and 2-cells. We reserve turnstile without subscript `⊢` for the sort named "Map" if it exists in the given theory.

Now we can write the above rule as follows:
```
    O : Ob
————————————————
 O ⊢ id₍O₎ : O
```

A bit more of syntactic sugar: when we have multiple arguments of the same sort we may write `a b .. c : Ob` instead of `a : Ob   b : Ob   ...   c : Ob`

Since (weak) model categories support fibered products along fibrations, the premises of generative rules may also contain equations, where one side is given by a projection and the other by any expression:

```
   f : Map    g : Map    f.target = g.source
————————————————————————————————————————————————
 fg : Map[source = f.source, target = g.target]
```

By using our shorthand notation equivalently:
```
 f g : Map   f.target = g.source
—————————————————————————————————
   f.source ⊢ fg : g.target
```

Or alternatively:
```
 X Y Z : Ob    X ⊢ f : Y    Y ⊢ g : Z 
——————————————————————————————————————
           X ⊢ fg : Z 
```

When defining equational laws for sorts with projections, one has to check that the LHS and RHS agree on all projections:
```
 f g h : Map   f.target = g.source   g.target = h.source
—————————————————————————————————————————————————————————
                    (fg)h = f(gh)
                    
 X Y : Ob    X ⊢ f : Y
———————————————————————
 id₍O₎ f = f = f id₍O₎
```

Congratulations, that was a XAT definition of a category. But we have not yet learned all kinds of rules we need. The rules already listed are insufficient to give provide finitery definitions for even simplest cases of structured categories (e.g. category with finite products) nor for the simplest cases of category-like objects (e.g. multicategory or even operad).

* * *


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
1) One requires existance of all fibered products while only few are required. Solution: consider categories with distinguished class of objects (“classifying sorts”) and maps (“projections“) and require only fibered products of the form `(x : X) ✕_₍x. =₍Z₎ f(y)₎ (y : Y)` where `proj` is a projection and `Z` is a classifying sort.
2) The identification of models and limit-preserving functors is not accurate: one actually only needs the functors to be defined on the full subcategory spanned by “esssential sorts” (the sort of maps in case of categories), while all other sorts (the sort of objects in case of categories) are there only to carry elusive compatibility structure of “essential” objects and should be taken into account only to the extent they are indispensible. The solution is provided by the doctrine of weak model categories and Quillen pairs between them.

Extended algebraic theories will be identified to (a restricted form of) weak model categories as defined in [Hen19]. Weak model categories come with two distinguised classes of maps called fibrations `X ↠ Y` and cofibrations `A ↪ B` closed under compositions and subject to a number of further axioms. They are required to have initial and terminal objects with unique map between them being both fibration and cofibration. The objects for which the unique map `X ↠ 1` is a fibration are called fibrant, respectively the objects for which the unique map `0 ↪ X` is a cofibration are called cofibrant. In the framework of extended algebraic theories, the class of cofibrant objects is intended to be spanned by “essential sorts”, the class of fibrant objects by “classifying sorts”, fibrations by projections, cofibrations by conversions (see below). Besides projections and constructions there are still the usual formation rules inherited from plain old algebraic theories. 

Now we can proceed to an example of a syntactical description for an EAT:
```
# Presenting sorts, as well as projections and conversions between them:

                               f : Map             f : Map
––––––––     ––––––––—     –––––––––––––––     ———————————————
 Ob cls       Map ess        f.source : Ob       f.target : Ob

# Define identity maps:

                     O : Ob
–––––––––––––————————————————————————————————————————
 id₍O₎ : Map    id₍O₎.source = O    id₍O₎.target = O

# Define composition of maps:

 f g : Map     X Y Z : Ob     f.source = X    f.target = Y    g.source = Y    g.target = Z
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––—————
                    fg : Map     (fg).source = X     (fg).target = Z

# Equational laws:

 (premises for `fgh` to exist)        (...)             (...)
–––––––––––––––––––––––––––––––     —————————————     —————————————  
        f(gh) = (fg)h                f id₍O₎ = f       id₍O₎ f = f
```
(Example 1: Categories)

Let's go through this example step by step:

1) a finite set of sorts marked as classifying, essential or both

2) a finite number of named projections and conversions (conversions are not required for the definition of plain categories)

3) a finite (or recursively generated) set generative rules for function symbols and universal equational laws. Premises consist of zero or more typed variables `x, y,...,z` and zero or more equational constraints of a special form: left hand side must be formed by a projection-free expression followed by a chain of projection applications ultimately landing in classifying sort, while right hand side is any expression possibly containing variables `x, y,...,z`. Each generative rule has to be accompanied by equational rules of the form `newly-defined-term.proj = term` for each applicable projection `proj`. Furthermore for every conversion `conv` into a type one must provide a term implementing the generative rule. These accompanying rules are called β-reductions and η-expansions respectively and should generate a confluent rewrite system eventually rewriting any expression of a classifying sort a projection-free form. To rule out circularity (to prove normalization we need the applicability of rules to be checkable, which relies on normalization), we need to provide a well-ordering on generative rules and their accomanying rules.

Equational laws required to respect projections, i.e. they are allowed only between terms, projections on which agree for all projections.

There are two additional restrictions:
– Equational laws are allowed to affect only non-classifying sorts.
– Rules producing a term belonging to a classifying sort are allowed to contain only variables belonging to classifying sorts.

These are to ensure decidability of equality on classifying sorts in the syntactic model, which is necessary for applicability of generational rules (and equational laws) to be decidable. 

Let's move on to an example making substantial use of the whole machinery: multicategories (aka virtual monoidal categories). These are much like categories, but source of a map is now not a single object, but a list of objects (called "Context). Composition `fg` is therefore defined not for two maps `f : X -> Y` and `g : Y -> Z`, but for a map `g : CY -> Z` from a context `CY` and a list of maps `f` one map for each element of `CY`. Besides the type of contexts we'll require a type of multimaps.

```
# Presenting sorts, as well as projections and conversions between them:

                                          
––––––––     —————————     ––––––––—     ——————————     
 Ob cls       Ctx fix       Map ess       MMap fix

    f : Map              f : Map             m : MMap            m : MMap
—–––––––––––––––     ———————————————     ————————————————    ————————————————
 f.source : Ctx       f.target : Ob       m.source : Ctx      m.target : Ctx
        
# Define contexts:

                 tail : Ctx    head : Ob    
–––––––––––     ––———————————————————————
 nil : Ctx          (tail; head) : Ctx

# Define composition

 f : MMap     g : Map     X Y : Ctx    Z : Ob     f.source = X    f.target = Y    g.source = Y    g.target = Z
–––––––––––––––––––––––––––––––––––––––––––––————————————————————–––––––––––––––––––––––––––––––––––––––––—————
                    fg : Map     (fg).source = X     (fg).target = Z

# Define multimaps

———————————————————————————————————————————————————————
 mnil : MMap    mnil.source = nil    mnil.target = nil

              tail : MMap    head : Map
————————————————————————————————————————————————————————————————————————————————————————————————————————————————
   (tail ;ₘ head) : MMap    (tail ;ₘ head).target = (tail.target ; head.target)     (tail ;ₘ head).source = ???

```

To fill the gap we need to join two contexts: `tail.source` and `head.source`. How can we do it? Well, the thing is that can encode computations by β-reductions in our rules.

------

```
                 j : Join        j : Join
——————————    —————————————    —————————————
 Join fix      j.fst : Ctx      j.snd : Ctx

    j : Join
———————————————
 j^step : Join
 
      a b : Ctx
 ——————————————————————————————
  join(a, b) : Join    fst = a
 
 
   j : Join   j.fst = nil
—————————————————————————————
   j = join(nil, j.snd)^step


 j : Join   head : Ob    tail : Ctx     j.fst = (tail ; head)
——————————————————————————————————————————————————————————————
      j = join(nil, join(tail, j.snd)!step.snd ; head)^step

Usage: Join(a, b)^step.snd gives a context, which is 
```

## More examples of category-like objects

Common feature of category-like objects are types with projections `.source` and `.target` (not necessarily into the same sort). For such sorts we'll define a shorthand syntax: `Г ⊢₍Map₎ f : T` for `f : Map    f.source = Г    f.target = T`.

Two examples: Virtual double category and sketch of a definition for weak ω-Categories (as defined by Finster-Mimram (2017)).

## Base of all Martin-Löf Dependent Type Theories: finitely-complete categories.

Let's move on to an example making substantial use of the whole machinery: the theory of finitely complete categories. First we'll extend the definition of category to include finite products and then we'll modify the definition to contain products in all slices (that is fibered products), than we'll add the initial object finitely complete categories. (Reformulate: we'll recover the notion of categories with families.)

```
———————————      ————————
 Unit type        1 : Ob

 f : Mor     f.target = 1
——————————————————————————
        conv : Unit
```



```
  X Y : Ob  
————————————
 X × Y : Ob        

                  X Y : Ob
——————————————————————————————————————————————————
 ᴨ₁ : Mor    ᴨ₁.source = (X × Y)    ᴨ₁.target = X

                  X Y : Ob
——————————————————————————————————————————————————
 ᴨ₂ : Mor    ᴨ₂.source = (X × Y)    ᴨ₂.target = Y

                  p : Pair         p : Pair
———————————     —————————————    —————————————
 Pair type       p.fst : Mor      p.snd : Mor


   p : Pair
——————————————
 p^conv : Mor

 Г : Ob    f : Mor    g : Mor    f.source = Г    g.source = Г
——————————————————————————————————————————————————————————————
     <f, g> : Pair    <f,g>.fst = f    <f,g>.snd = g
 
 
 X Y : Ob      f : Mor     f.target = X × Y
––––––––––––————————————————————————————————
         f = <ᴨ₁ f, ᴨ₂ f>^conv
         
```



```
                   f : Fam         f : Fam
——————————      —————————————     —————————
 Fam type        f.base : Ob       

```

Key problem: Direct map from Maps to Objects (constructor of fibered product depends on the respective two maps) is prohibited as functions into classifying sorts must be from classifying sorts only.



## Bidirectionally Typed Martin-Löf Type Theories

ML71 example!!!

```
       f : Map
––––––––––––––––––––––––––
 lam(f) : Lam    apply(e)
```

[Hen19] Simon Henry, “Weak model categories in classical and constructive mathematics”, https://arxiv.org/abs/1807.02650
[PV07] Erik Palmgren, Steve Vickers, “Partial Horn logic and cartesian categories.” Annals of Pure and Applied Logic, 145(2007), 314-355. http://www2.math.uu.se/~palmgren/partialalgebras_pre.pdf
[Law3] F. William Lawvere, “Functorial Semantics of Algebraic Theories”, Proceedings of the National Academy of Sciences 50, No. 5 (November 1963), 869-872
[Is17] Isaev, V., 2017 “Algebraic Presentations of Dependent Type Theories”, https://arxiv.org/abs/1602.08504
