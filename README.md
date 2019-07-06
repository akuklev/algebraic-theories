# Extended Algebraic Theories

Making use of recently developed notion of weak model categories [Hen19], we propose a refinement for the notion of essentially algebraic theories (EATs) [PV07] that leads to more sophisticated functorial semantics yielding more relaxed notion of homomorphism of algebras. Similar to essentlially algebraic theories, our proposal encompases categories, yet with functors and equivalences as homomorphisms and isomorphisms respectively. For theories `T` admitting unbiased descriptions (ones where for every posible composite term there is exactly one equation law, identifying the composite term with an atomic one) we derive a notion of generic enrichment structure `G(T)` — for categories being virtual double categories – and `V`-enriched `T`-algebras, `V` being a fixed `G(T)`-algebra.

Much like algebraic theories and generalized algebraic theories without equations on sorts [Car81], yet in contrast to EATs, our proposal keeps applicability of formation rules decidable regardless of word problem decidablity for the respective theory, thus we argue it to be not only an essentially, but a truly algebraic formalism. Thus we pursue the approach of [Is17] regarding type theories as algebraic presentations of structured categories and category-like structures.

## Exposition of the Formalism
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
