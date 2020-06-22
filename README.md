A Framework for Complex Symbolic Languages and Structured Categories
====================================================================

ABSTRACT: We develop two extensions to the formalism of algebraic theories of successively increasing strength to provide a formalism for symbolic languages including proposition and proof languages for standard logical systems and internal languages for plethora of structured categories. 
The first one, IIR-EAT, can be understood as stratified version of essentially algebraic theories with slightly refined semantics following the natural model approach of [Awo16]: it allows for more models, yields a more flexible notion of isomorphism and makes IIR-EATs into a superset of Cartmell's Generalised Algebraic Theories without equations on sorts[Car81]. This formalism is sufficient for symbolic languages of first order logical systems, categories with simple algebraic structure (e.g. monoidal categories) and most notably also weak ⍵-categories[Fin17]. We present explicit IIR-EATs of symbolic languages for the single-sorted equational logic and first order logic with dependent sorts[Makkai]. Axiomatic theories are then free algebras for logic systems they are defined upon.
The second one, XAT (extended algebraic theories), goes even further and incorporate a staging mechanism known as bidirectional typing that allows well-controlled circular type dependencies. XATs can represent symbolic languages of higher order logics and internal languages of (quasi)categories with arbitrary properties that can be expressed as essentially unique algebraic structures (existence of products, limits, internal homs, subobject and object classifiers). XATs have natural functorial semantics in the doctrine of recently developed fibrant weak model categories [Hen20], and the category of models for each theory carries a structure of fibrant weak model category itself. XATs facilitate exact formulations of syntax-semantics duality and Baez-Dolan microcosm principle.


§ Introduction: Symbolic Languages
==================================

The idea of symbolic languages traces back to Leibniz. He conceived symbolic languages for knowledge representation, logical arguments, specification of devices and systems, and even legislation. Symbolic languages were to be strictly unambiguous, have a precise well-defined grammar, a carry an intrinsic notion of sentence identity, i.e. it should be clear what details of how a sentence is being written down (or spoken out, or represented in any other way) are insignificant).

{Sidenote: There is a related notion of formal languages in computer science. There, sentences are assumed to be represented as finite sequences of characters of predefined alphabet. This notion differs from the notion of symbolic language by prescribing the representation and lacking unambiguity. In applications, formal languages are usually to be parsed: processed into an unambiguous abstract syntax tree, or rather abstract syntax representation, because plain trees are in general not enough to represent languages with binders like the first order logic (the quantifiers are operators with binders). Symbolic languages are formal languages modulo parsing: they're about abstract syntax representations.}

Statements, proofs and constructions in mathematics are mostly written using natural languages (e.g. English) as a matter of fact. But at least since Frege(cf. https://en.wikipedia.org/wiki/Begriffsschrift, 1879) it is universally assumed that it's possible to use well-defined symbolic language instead. Mathematicians keep writing up their results using natural languages because they are way more human-readable and much better at expressing subtleties and the thought process which lead to the result: ultimately a goal of a paper is not just establishing a mathematical fact but also instructing the reader how to carry out such or a similar proof themselves. Yet mathematicians strive to keep relevant parts trivially translatable into the respective symbolic language.

While mentally using a symbolic language or two (the first order logic and its proof language, known as natural deduction) for these purposes, generic pure mathematicians have had little interest in symbolic languages as subject of study. The area was predominantly studied by computer scientists driven by applications: symbolic languages are used computer-aided knowledge representation, software development (declarative programming languages are precisely the symbolic languages for specification of algorithms, interactive systems and distributed systems) and computer-verifiable proofs. Being application-driven, the area relied on a patchwork of ad-hoc formalisms of varying mathematical elegance and no strong connections to other areas of mathematics.

In recent decades, a solid theory of symbolic languages has begun to emerge, uncovering a multitude of connections to category theory, abstract homotopy theory and algebraic geometry. 

§ Exposition: Symbolic Languages and Algebraic Theories
=======================================================

Mathematical facts (theorems) are stated and proven inside of a respective axiomatic theory, e.g. Euclidean Geometry. For sake of reusability and composability of mathematical results, generic mathematicians<sup>[^1]</sup> usually work inside of a common environment: an axiomatic theory of vast generality known as Zermelo–Fraenkel set theory, into which more specialised axiomatic theories (like theory of groups) are submerged. However, it makes a lot of sense to study specialised axiomatic theories in their own right.

An axiomatic theory is defined upon a chosen underlying logic (usually, classical first order logic unless stated otherwise) and is given by
– a language in which propositions of the theory are stated (the language of the underlying logic extended by theory-specific syntax), and
– a finite or recursively generated set of axioms in this language, i.e. propositions assumed to be true a priori in this particular theory.

A logic consists of an extendible common language base for axiomatic theories stated upon this logic, and a language for proofs specific to this logic. These symbolic languages can be described in terms of formation rules (also called “inference rules” in proof languages) generating a set of well-formed (by construction) propositions and a set of correct (by construction) proofs respectively.

<figure><b>Fig. 1: Examples of formation and inference rules.</b>
<pre>```
 A : Prop   B : Prop       A : Prop   B : Prop   x : Pf[A]    y : Pf[A => B]
—————————————————————     ———————————————————————————————————————————————————Modus Ponens
    A => B : Prop                           MP(x,y) : Pf[B]

```</pre></figure>
<lj-cut>Equational logic can be seen as a weak fragment of classical first order logic where the only axioms allowed are universally-qualified equational laws. Thus theories based upon equational logic cannot express any properties of non-functional relations, in particular incidence relations, order relations and partially defined operations (like division in fields). For this reason for theories defined upon equational logic, theory specific syntax is limited to a fixed number of functional symbols of fixed arities (symbols of arity zero being called constants). Theory-specific syntax is usually described precisely in the form we used in Fig. 1 above, as formation rules for terms of the theory.

Lots of interesting axiomatic theories including theory of groups, theory of rings and theory of modules over a ring can be stated and studied upon equational logic. Proofs in equational logic are limited to algebraic manipulations (transforming symbolic expressions using equalities to prove other equalities). For this reason, such theories are known as <a href="https://ncatlab.org/nlab/show/algebraic+theory">algebraic theories</a>. Algebraic theories have <a href="https://ncatlab.org/nlab/show/Functorial+Semantics+of+Algebraic+Theories">exceptionally elegant and well-understood model theory</a>, and <a href="https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff&#39;s_theorem">most well-behaved correspondence between syntax and semantics</a>.

<figure><b>Fig. 2: Example of a single-sorted algebraic theory.</b>
<pre>```
 x   y                     x             x
————————    —————     ———————————   ———————————
 [x,y]        e        [e,x] = x     [x,e] = x

```</pre></figure>
All irreducible provable propositions in equational logic are universally qualified and of the form “term₁ = term₂” or “(a = b) ⋀ ··· ⋀ (c = d) ⇒ (x = y)”. Thus, equational logic can be also seen as a logic in its own right with a very tractable proposition and proof languages. Whereas in full first order logic, propositions are arbitrary combinations of nested quantifiers and connectives, in equational logic propositions have a very rigid form, so that quantifiers and connectives can be leaved implicit and not part of the language, a proposition can be described by a nonempty list of equations of finite length, where terms (sides of equalities) are generated by formation rules of the theory and possibly a number of variables. Proof language of equational logic is also vastly simpler: equations can be generated by reflexivity, transformed by symmetry, composed by transitivity and used for algebraic transformations, a proof is just a tree of such steps.

An algebraic theory is a grammar + equational laws between terms generated by the grammar. Grammar of an algebraic theory is allowed to be multisorted (e.g. there two distinct types of variables and terms: “scalars” and “vectors”). Such grammars are however not general enough to describe proposition and proof languages for a logic. A grammar for a proof language (see Fig. 1) is necessarily not just multisorted, but dependently typed: there are types with indexes like `Pf[p]` standing for “Proof of proposition `p`”. Moreover, a if language of propositions has (at least implicit) quantifiers (which is the case for every logic beyond zeroth-order) and also has a dependently typed grammar: besides type `Prop` of closed propositions there have to be types `Pred[ctx]` of predicates of several of variables (where the “context” ctx specifies the number and types of variables).

To make sense of a dependently typed grammar, one has to rely a certain notion of equality[^2] on indexes of the types. Moreover, when two occurrences of typal dependency (`Proof[prop]` and `Prop[ctx]`) come into interaction, equality cannot by swept under the rug: in order to define proposition and proof languages for logics, we have to provide their grammars together with some additional equational laws; the framework to describe sufficiently elaborate grammars is necessarily a generalisation of algebraic theories' framework.

Ultimately, it is desired to obtain a framework of extended algebraic theories (XATs), so that each standard logical system can be expressed as an extended algebraic theory and an axiomatic theory upon this system as its free algebra generated by sort definitions, term formation rules and axioms of the theory. The framework should support at least classical and intuitionistic first order logic (including FOLDS = first order logic with dependent sorts), equational logic (optimally, it should “eat itself”) and encompass an algebraic definition of an elementary ∞-topos, which is a modern foundational alternative to Zermelo–Fraenkel set theory.

Establishing such an all-encompassing framework of this kind with a nice semantics is however still work-in-progress. Present work is an attempt to progress in this direction.

[^1]: <i>A generic mathematician, or more precisely a generic pure mathematician, is a mathematician working in the areas of algebra, analysis, geometry, topology or number theory, using classical logic and the axiom of choice.</i> — David M Roberts, hott.zulipchat.com

[^2]: Actually, instead of equality a more general notion of canonical convertibility can be developed for this case.

§§ The Equality Problem
-----------------------

In the framework of algebraic theories (both <a href="https://ncatlab.org/nlab/show/Lawvere+theory">single-sorted</a> or <a href="https://ncatlab.org/toddtrimble/published/multisorted+Lawvere+theories">multisorted</a> with a fixed finite collection of sorts), equations are imposed upon grammar and not intertwined with it. In order to construct an initial model, one just generates the set of terms from the grammar and factors it by equations. In this framework there is also no notion of equality on sorts except for the purely syntactic notion of nominal equality (equally named sorts are equal).

It gets more tricky if one extends the framework to accommodate dependently-typed formation rules. In such theories sorts are generalised to types which are in general dependent on values of other types, say `Mat[n, m]` of `(n × m)`-matrices, which can be multiplied only if dimensions match. In such cases one speaks of sort `Mat` with two indexes of type `Nat`. The concrete type is given by sort and fixed values for all of its parameters, e.g. `Mat[3, 3]`. With dependent types we run into a problem: in order to see if a term of type `T[x]` fits into a receptacle of type `T[x']` we need to be able to check if `x = x'`, and it might even happen that `x : G[y]` and `x' : G[y']` so that we need to check if `y = y'` even to start checking if `x = x'`.

Unless we restrict allowed dependency structure, we might run into situation where a circular dependency makes the question if a term fits into a receptacle (i.e. if a given word is a syntactically valid term) not only undecidable but not even semidecidable, and the very existence of the initial model can be shown only with help of the highly non-constructive well-ordering principle (= axiom of choice). A theory without a tractable syntactical model can hardly be named algebraic. For a theory describing a proof language such situation is unacceptable: a proof language where it is in general inherently impossible to find out if a proof is valid is worthless.

A workable solution is to distinguish indexing sorts, which are either free sorts (sorts with no equations whatsoever) or sorts with canonical forms (with arguments of indexing sorts only), and to restrict conditions in premises of formation rules to equalities over indexing sorts.

In the following we'll start with a broad generalisation of algebraic theories and restrict it step-by-step while refining its semantics at the same time.


§§ Algebraic Theories
---------------------

{TODO: Exposition}
{Categorical semantics:
1. Signature (incl. equations) = Finite presentation of an FPCat
2. Syntactic model = This FPCat
3. Models = Product-preserving Functors from this FPCat
4. Homomorphisms = Natural transformations between that functors
5. We have a category of models and homomorphisms, the syntactic model is it's canonical initial object.
6. Say a word that this category comes with a tensor product and proarrows}

{HoTT semantics:
1. Initial model given by a closed inductive type family.
2. Models are (non-dependent set-level) elimination motives: a coinductive type family.
3. Isomorphisms given by equality.
4. Say a word about how to define homomorphisms, tensor product and proarrows.
}

§§ Essentially Algebraic Theories
---------------------------------
{TODO: Exposition}
{Categorical semantics: Same as algebraic, but categories with finite limits and lex functors.}


§ The First Novel Formalism
===========================

§§ Index Sorts
--------------

Algebraic theories with index sorts are a special case of EATs, where some sorts are marked as index sorts and there is an additional kind of formation rules: formation rules of “canonical forms” written with `term ↪ T` instead of `term : T` below the rule. Canonical forms have to map from and into index sorts only.

The only conditions allowed in algebraic theories with index sorts are of the form `t = c` where `t` is a (non-canonical) term of index type and `c` is a canonical form of the same type. All equational rules in index sorts also must be of this form. Every (noncanonical) formation rule into an index sort must come with a number of equational rules allowing to unambiguously find an equal a canonical form for a term whenever arguments of canonical form are substituted. These rules are called computation rules. No other equational rules in index sorts are allowed. In particular, index sorts with no canonical forms have to be free (no equations allowed), we'll call such sorts abstract.

<figure><b>Fig. 3: Index sort of natural numbers with addition.</b>
<pre>```
                            n : Nat
—————————    ——————————    —————————
 Nat idx      0 ↪ Nat      n' : Nat

 n : Nat    m : Nat
————————————————————
     n + m : Nat

  n : Nat    m : Nat   n = 0
—————————————————————————————
    n + m = m             

 n : Nat    m : Nat    k : Nat    n = k'
—————————————————————————————————————————
        n + m = (k + m)'
```</pre></figure>
Index sorts are helpful when one wants to define dependent sorts like `Mat[n, m]` of `(n × m)`-matrices or `Pred[n]` of predicates with `n` untyped variables or `Pred[ctx]` of predicates in context `ctx`, where context is a finite list of types of variables.

Non-abstract index sorts are intended to be “closed”, i.e. not to be extended in models. Abstract sorts are open: they are explicitly allowed to be extended (but only freely).

Example:
<figure><b>Fig. 4: Index sort of lists over an abstract sort.</b>
<pre>```
————————    —————————
 Ob abs      Ctx idx

                   tail : Ctx    head : Ob
——————————————    —————————————————————————
 empty ↪ Ctx         (tail; head) ↪ Ctx

 a : Ctx    b : Ctx
————————————————————
 append(a, b) : Ctx


 a : Ctx    b : Ctx    b = empty
—————————————————————————————————
 append(a, b) = b

 a : Ctx    b : Ctx    tail : Ctx     head : Ob    b = (tail; head)
————————————————————————————————————————————————————————————————————
 append(a, b) = (append(a, tail); head)

```</pre></figure>
We'll introduce a refined semantics for Algebraic Theories with Index Sorts: namely, we do not want to distinguish between models which differ by inaccessible or indistinguishable elements of index types. This will ultimately lead to notion of equivalence of categories for algebraic theory of categories.

Index sorts: Categorical Initial Model
--------------------------------------

As it was already mentioned, Algebraic Theories with Index Sorts can be interpreted as a subclass of essentially algebraic theories, so initial model for each such theory (a finitely-presentable category with finite limits) is known to exist[Palmgren-Vickers][^ It is even known to be constructible in every topos with a natural number object]. But the signature of an algebraic theory with index sorts actually provides more structure:
– A subclass of objects known as index sort objects (also includes finite products of sort objects and the terminal object 1);
– A subclass of maps known as canonical inclusions (maps generated by formation rules for canonical forms), all of which have index sort object as their source and target;
— A subclass of maps known as free inclusions: all maps from the terminal object 1 into abstract objects (index objects such that no canonical inclusions map into them) and isomorphisms between index sort objects.
– Any map `f : 1 -> T` from the initial object into an index sort object factors into a free inclusion followed by a canonical inclusion. This guarantees that equality on elements of index sort always remains decidable.

(Note: Index sort objects with inclusions form a subcategory.)

§§ IIR-EATs: Algebraic Theories with Index and Indexed Sorts
------------------------------------------------------------

In this extension, each sort may additionally have a fixed number of named indexes, e.g. `Mat[width : Nat, height : Nat]`. Types of indexes are not limited to index types, but only indexes of index types can be used in conditions of formative rules. Equational laws are allowed only if indices of left hand side and right hand side are equal (either nominally, or by application of computation rules).

Every formative rule must be supplied by equations expressing indices of outcome in terms of indices of its constituents. These can be included into the formative rule as in the following example:
<figure><b>Fig. 5: Language of first order propositions for a single-sorted theory</b>
<pre>```
                            n : Nat
—————————    ——————————    —————————
 Nat idx      0 ↪ Nat      n' : Nat

————————————————————————————————
 Mat[height : Nat, width : Nat]

 a : Mat   b : Mat   a.height = b.width
————————————————————————————————————————
   ab : Mat[a.height, b.width]
```</pre></figure>
Algebraic Theories with Index and Indexed Sorts where the only index types are free types are syntactically precisely the <a href="https://ncatlab.org/nlab/show/generalized+algebraic+theory">Generalised Algebraic Theories</a> without sort equation. For readers with CS background, initial algebras of such theories can be expressed the closed Quotient-Inductive-Inductive Types[https://arxiv.org/abs/1612.02346] and set-valued models as their (non-dependent, set-level) elimination motives.

<figure><b>Fig. 6: Definition of Semicategories</b>
<pre>```
————————    ———————————————————————————————
 Ob abs      Map[source : Ob, target : Ob]

 f : Map    g : Map    f.target = g.source
———————————————————————————————————————————
     fg : Map[f.source, g.target]

 f : Map    g : Map    h : Map    f.target = g.source    g.target = h.source
—————————————————————————————————————————————————————————————————————————————
               f(gh) = (fg)h
```</pre></figure>
Initial algebras for generic Algebraic Theories with Index- and Index-Dependent Sorts are the closed Quotient-Inductive-Inductive-Recursive Types, the non-canonical formation rules for index types with their respective computation rules taking them to the canonical ones are turned into internal recursive functions.

§§ Categorical Initial Model
----------------------------

Algebraic Theories with Index and Indexed Sorts can also be seen as a special case of essentially algebraic theories, so their EAT-initial model (a finitely-presentable category with finite limits) can be constructed. But the signature provides information for more structure:
– A wide subcategory of index maps (including unique maps into the terminal object 1 from any object).
— A subcategory of index sort objects and inclusions (now closed not only under products but also under pullbacks along index maps into index sorts), and it is still guaranteed that every map `f : 1 -> T` into an index sort object factorises into a free inclusion followed by a canonical inclusion. 

This category contains lots of unnecessary limits. In order to represent only syntactically relevant data, all limits except pullbacks of sorts along index maps (only one leg being an index map is sufficient) into index sorts. Note that first projections of such pullbacks and thus both projections of products should count as index maps.

Please note that free inclusions can be characterises via LLP with respect to index maps. Later we'll make use of this characterisation for the definition of the doctrine of structured categories suitable to model our flavour of extended algebraic theories and structure-preserving functors between them.

§§ A Theory for Single-Sorted Equational Logic
----------------------------------------------
(Dealing with hereditary substitution)

```
———————————————————————————    ———————————————————————
 Operator[arity : Nat] abs      Term[arity : Nat] idx

———————————————————————————————————————————————————
 EquationalLaw[arity : Nat, lhs rhs : Term[arity]]



                    n m : Nat    o : Operator[n]    l : TermList[n, m]
———————————————    ———————————————————————————————————————————————————
 var ↪ Term[1]                    apply(o, l) ↪ Term[m]

 n m : Nat    t : Term[n]    l : TermList[n, m]   
————————————————————————————————————————————————
     compose(t, l) : Term[m]


{deal with hereditary substitution via “Everybody’s Got To Be Somewhere” by Conor McBride, https://arxiv.org/pdf/1807.04085.pdf}

```
          
—

<h3>§§ Case study: Proposition Languages, Type-Theoretical Notation</h3>
Algebraic Theories with Index and Indexed Sorts can be used to define language of propositions for logics. Let's start with the case of single-sorted underlying theory. 


<figure><b>Fig. 7: Language of first order propositions for a single-sorted theory</b>
<pre>```
The extendable sorts for theory-specific part of the language:

———————————————————————————    ———————————————————————————
 Operator[arity : Nat] abs      Relation[arity : Nat] abs


——————————————— Type of terms with `n` variables
 Term[n : Nat]

 n m : Nat    o : Operator[m]   args : TermList[n, m]
——————————————————————————————————————————————————————
   apply(o, args) : Term[n]


 t : Term[n]
———————————————— Terms with `n` variables are included into terms with `n + 1` variables
 t' : Term[n']

 n : Nat
——————————————————— Reference to `n`'th variable is valid term with `n` variables
 var(n) : Term[n']

{TODO: Switch to co-de Bruijn representation}

Now the atomic predicates are defined:

 n : Nat    t1 : Term[n]    t2 : Term[n]
—————————————————————————————————————————
      equals(t1, t2) : Pred[n]

{Add relations.}

Logical connectives:

 n : Nat   a : Pred[n]    b : Pred[n]
——————————————————————————————————————
        a => b : Pred[n]

 n : Nat   a : Pred[n]    b : Pred[n]
——————————————————————————————————————
        a ⋀ b : Pred[n]

 n : Nat   a : Pred[n]    b : Pred[n]
——————————————————————————————————————
        a ∨ b : Pred[n]

    n : Nat
——————————————
 ⊥ₙ : Pred[n]

Quantifiers:

 n: Nat   p : Pred[n']
———————————————————————
    ∀p : Pred[n]

 n: Nat   p : Pred[n']
———————————————————————
    ∃p : Pred[n]
```</pre></figure>

Now let's move to the version for many-sorted theories. First, in addition to the type `Nat` of natural numbers (we'll need that for `var(n) : Term[n']`) we'll define the type `Ctx[n : Nat]` of contexts of length `n`, i.e. lists of types of variables. It will be defined upon abstract type `Ob` of theory-specific sorts. `Ctx[n : Nat]` makes substantial use of the feature that index types can be indexed themselves.

<figure><b>Fig. 8: Defining the index sort of contexts for multi-sorted theories</b>
<pre>```
                            n : Nat
—————————    ——————————    —————————
 Nat idx      0 ↪ Nat      n' : Nat

 n : Nat    m : Nat
————————————————————
     n + m : Nat

  n : Nat    m : Nat   n = 0
—————————————————————————————
    n + m = m             

 n : Nat    m : Nat    k : Nat    n = k'
—————————————————————————————————————————
        n + m = (k + m)'


————————    ———————————————————————
 Ob abs      Ctx[length : Nat] idx

                         tail : Ctx    head : Ob
—————————————————    ——————————————————————————————————
 empty ↪ Ctx[0]      (tail; head) ↪ Ctx[tail.length']

 a : Ctx    b : Ctx
—————————————————————————————————————————
 append(a, b) : Ctx[a.length + b.length]


 a : Ctx    b : Ctx    b = empty
—————————————————————————————————
 append(a, b) = b

 a : Ctx    b : Ctx    tail : Ctx     head : Ob    b = (tail; head)
————————————————————————————————————————————————————————————————————
 append(a, b) = (append(a, tail); head)

```</pre></figure>

In our applications, we'll encounter countless cases of sorts with precisely these two projections (`source` and `target` or `context` and `type`), so it makes sense to introduce a shorthand notation (which is already very common among type theorists):
- Let `src ⊢₍ArrowSort₎ f : tgt` always denote `f : ArrowSort[source = src, target = tgt]`. In many cases we'll have multiple types of “arrow sorts” such as functors and proarrows or 1-cells and 2-cells. We use turnstile without subscript `⊢` if only one such sort exists in the given theory, or reserve it for the sort named “Map” otherwise.
— Analogously, we'll use `ctx ⊢ p Prop` for `p : Prop[ctx]`
– Let's write `a b .. c : T` instead of `a : T   b : T   ...   c : T` when we have multiple arguments of the same sort.

<figure><b>Fig. 8: Language of first order propositions for a multi-sorted theory</b>
<pre>```

——————————————————————— Type of terms in a context
 Term[Г : Ctx, T : Ob]

Г : Ctx    R : Ob    Г ⊢ t : T
———————————————————————————————
    Г; R ⊢ tᴿ : T

    Г : Ctx    T : Ob
———————————————————————————
 Г; T ⊢ var(Г.length) : T

{Here the theory-specific formation rules for terms come.}

Now the atomic predicates are defined:

 Г : Ctx     Г ⊢ t1 t2 : T
————————————————————————————
 Ctx ⊢ equals(t1, t2) Pred

{If the theory has additional relations besides equality, add an analogous theory-specific rule for each of them.}

Logical connectives:

 Г : Ctx    Г ⊢ a b Pred
———————————————————————————
    Г ⊢ a => b Pred

{...}

Quantifiers:

 Г : Ctx    R : Ob    Г; R ⊢ p Pred
————————————————————————————————————
          Г ⊢ ∀ᴿp Pred

 Г : Ctx    R : Ob    Г; R ⊢ p Pred
————————————————————————————————————
          Г ⊢ ∃ᴿp Pred

```</pre></figure>

The shorthand notation is also very handy for definition of categories:
<figure><b>Fig. 9: Type-Theoretical Style Definition of Categories</b>
<pre>```
 X Y Z : Ob    X ⊢ f : Y    Y ⊢ g : Z 
——————————————————————————————————————
           X ⊢ fg : Z 

    O : Ob           X Y : Ob    X ⊢ f : Y
————————————————    ———————————————————————
 O ⊢ id₍O₎ : O       id₍X₎ f = f = f id₍Y₎

 A B C D : Ob    A ⊢ f : B    B ⊢ g : C    C ⊢ h : D 
——————————————————————————————————————————————————————
                   f(gh) = (fg)h 
```</pre></figure>

Note that the framework as presented can readily be used for the Type-Theoretical Definition of Weak ω-Categories (by E. Finster, S. Mimram, https://arxiv.org/abs/1706.02866). Note that this theory only contains index and abstract types, no ordinary (algebraic) types whatsoever.

<h2>§§§ Proposition Language for FOLDS</h2>

FOLDS is a generalisation of first order logic for multisorted theories. In FOLDS, sorts are declared to be dependent on zero or more previously dependent sorts and come in two flavours: those with equality predicate and those without (in particular categories are defined as theories where `Map`s do have equality predicate while `Ob`jects don't). Relations are introduced as dependent sorts on which no other sorts are dependent. In particular, no sorts can be dependent on relations including equality relations. Signatures of FOLDS-theories are not allowed to contain any theory-specific term formation rules, because one can readily encode constants and functions via relations. For instance, instead of defining a neutral element of a monoid as constant `e : M` we define an unary relation `is-neutral[e : M]`, and instead of composition a ternary relation `is-composition[x y z : M]` with additional axioms involving equality relation ensuring this relation is functional with respect to target `z`. FOLDS-theories have an excellent HoTT  semantics[https://arxiv.org/pdf/2004.06572.pdf]: In models, the type of identifications between elements `e1 e2 : T` of a given sort `T` without equality predicate is taken to be discernability between `e1` and `e2` with help of sorts dependent on `T`. This means in particular, that since no further sorts are allowed to depend on `is-neutral`, any `e1 e2` such that `is-neutral[e1]` and `is-neutral[e2]` satisfy `e1 = e2`, identifiability of objects in a category coincides with isomorphism.

(Remark: There is a notion of FOLDS⁺, where term formation rules are allowed. FOLDS⁺-theories have natural topological interpretations, where algebraically defined constants and functions have to exist globaly, whereas relationaly defined ones are only required to exist locally in a coherent fashion. This language facilitates natural handling of approximate identities in Banach algebras and alike. Later we'll encounter the same phenomenon regarding object classifiers (type theoretical universes): for any compact part of the model there will always exist a universe large enough, but a global one cannot exist.)

<figure><b>Fig. 10: Defining the index sort of contexts for FOLDS theories</b>
<pre>```

——————————————————————    ——————————————————————————
 Ob[deps: ObList] abs      ObList[length : Nat] idx

                           tail : ObList    head : Ob
—————————————————————    ——————————————————————————————————————
 emptyᴰ ↪ ObList[0]      (tail;ᴰ head) ↪ ObList[tail.length']



———————————————————    ———————————————————————————
 Ctx[length : Nat]      Type[Г : Ctx, O : Ob] idx

                       tail : Ctx    tail ⊢ head Type
—————————————————    ——————————————————————————————————
 empty ↪ Ctx[0]      (tail; head) ↪ Ctx[tail.length']


(definition of elements of Type has to be postponed)

Absence of formation rules means all the terms are simply variables so the type of terms can be made a closed index type (it had to be open algebraic type previously), which allows us to use it in the definition of Type.


————————————————————————————— Type of terms in a context
 Term[Г : Ctx, Г ⊢ T Type] idx

    Г : Ctx    Г ⊢ R Type
———————————————————————————
 Г; R ⊢ var(Г.length) ↪ T

 Г : Ctx    Г ⊢ T R Type    Г ⊢ t : T
——————————————————————————————————————
       Г; R ⊢ tᴿ ↪ Tᴿ


Now let's define Type:

 Г : Ctx    deps : ObList    o : Ob[deps]    Г ⊢ params : PramList[deps]
—————————————————————————————————————————————————————————————————————————
   Г ⊢ type(o, params) ↪Type[o]


———————————————————————————————————
 PramList[Г : Ctx, l : ObList] idx

       Г : Ctx
——————————————————————————————————
 Г ⊢ emptyᴾ(Г) ↪Pramlist[emptyᴰ]

 ob-tail : ObList    o : Ob    Г : Ctx    Г ⊢ tail : PramList[ob-tail]    Г ⊢ p Term   p.type.o = o 
————————————————————————————————————————
 Г ⊢ tail ;ᴾ p ↪Pramlist[ob-tail ;ᴰ o]


Since no custom relations are added as formers for atomic propositions, the type of propositions can be made into a closed index type: this will enable us later to define a type of proofs `Pf[prop]` without workarounds.

—————————————————————
 Pred[ctx : Ctx] idx


Now the atomic predicates are defined:
 Г : Ctx     Г ⊢ P Type
————————————————————————————
 Г ⊢ P ↪Pred


We'll need a marker for sorts that have inbuilt equality predicate:

—————————————————————————
 HasEquality[O : Ob] abs

 Г : Ctx     Г ⊢ T Type    Г ⊢ t1 t2 : T   ev : HasEquality[T]
———————————————————————————————————————————————————————————————
 Г ⊢ equals(T, t1, t2) ↪Pred


Logical connectives:

 Г : Ctx    Г ⊢ a b Pred
———————————————————————————
    Г ⊢ a => b ↪Pred

{...}

Quantifiers:

 Г : Ctx    Г ⊢ R Type    Г; R ⊢ p Pred
————————————————————————————————————————
          Г ⊢ ∀ᴿp ↪Pred

 Г : Ctx    Г ⊢ R Type    Г; R ⊢ p Pred
————————————————————————————————————————
          Г ⊢ ∃ᴿp ↪Pred

```</pre></figure>

{TODO: Define proof language, }

<h2>§§ Staged equality/abstract covering sorts</h2>

{Motivation: Finitely Complete Categories}

<h2>§§ Categorical semantics</h2>

Categories suitable to model XATs are essentially fibrant parts (a la Henry) weak model categories:
categories: categories with a wide subcategory of fibrations and a full category of bifibrant objects and cofibrations, so that all pullbacks along fibrations <b>into bifibrant objects</b> (this restriction is not present in the original definition) exist and
– Any map from an bifibrant object can be factored both as an cofibration followed by a trivial fibration and as a trivial cofibration followed by a projection.
— For any bifibrant object A and any factorization Id_A : A ↪ B ↠̃ A of the identity of A as an cofibration followed by a trivial fibration, the inclusion is trivial as well.

{Show that category of models for a given theory naturally carries such structure itself, following “The language of a model category” by Simon Henry, https://www.uwo.ca/math/faculty/kapulkin/seminars/hottestfiles/Henry-2020-01-23-HoTTEST.pdf}

<h2>§§ Signature Language for Extended Algebraic Theories</h2>
```

———————————————————————————————————————————————
 Sort[k : Kind, s : Subkind[k], deps : Ob] abs

Sorts can be of either index or algebraic Kind, index sorts additionally have a subkind: open (abstract) or closed (default).

——————————    —————————————    —————————————
 Kind idx      idx ↪ Kind      alg ↪ Kind

                       
———————————————————————    ————————————————————
 Subkind[k : Kind] idx      abs ↪ Subkind[idx]

————————————————————————————    ————————————————————————————
 idx-default ↪ Subkind[idx]     alg-default ↪ Subkind[alg]


    k1 k2 : Kind         k1 k2 : Kind    k1 = alg      k1 k2 : Kind    k1 = alg
————————————————————    ——————————————————————————    ——————————————————————————
 min(k1, k2) : Kind         min(k1, k2) = alg              min(k1, k2) = k2



                           S : Sort
—————————————————————    ——————————————————
 Ob[kind : Kind] idx      just(S) : Ob[s.k]

          A B : Ob
—————————————————————————————————————————
 product(a, b) : Ob[min(a.kind, b.kind)]

 A B : Ob    Z : Ob[idx]   A ⊢₍Proj₎ p : Z    B ⊢₍Term₎ t : Z
———————————————————————————————————————————————————————————————
      pullback(A, B, Z, p, t) : Ob[min(k1, k2)]


—————————————————————————————————————————————————————————————————————————
 CanonicalConstructor[source : Ob[idx], target : Sort[idx, idx-default],
  source ⊢₍Term₎ t : target.deps] abs

 
———————————————————————————————————————————————————
 AlgFormationRule[source : Ob, target : Sort[alg],
  source ⊢₍Term₎ t : target.deps] abs


—————————————————————————————————————————————————
 EquationalRule[source : Ob, target : Sort[alg],
  source ⊢₍Term₎ lhs rhs : target]

(subject to typechecking that all lhs and rhs agree on all projections)


————————————————————————————————————————————————————————
 IdxFormationRule[source : Ob[idx], target : Sort[idx],
  source ⊢₍Term₎ t : target.deps] abs

——————————————————————————————————————————————————————————————————
 ComputationRule[R : IdxFormationRule, cond : ···, rewrite : ···]

(computation rules must be checked for being exhaustive, nonoverlapping and terminating)
```


<h2>§§ Internalising types: The Bi-directional Doctrine</h2>

Let's define a category with binary products
```
@import Cat

  A B : Ob
—————————————
 A × B ↪ Ob


 X A B : Ob    X ⊢ f : A × B
—————————————————————————————
     X ⊢ f.fst : A


 X A B : Ob    X ⊢ f : A × B
—————————————————————————————
     X ⊢ f.snd : B

                            p : Pair[O X Y]
———————————————————————    =================
 Pair[O X Y : Ob] idx        O ⊢ p : X × Y




```

<h2>§§ A Recipe for Baez-Dolan Microcosm Principe</h2>
{TODO: 
1. Take an unbiased extended algebraic theory, i.e. one where every composite operation has a canonical name.
2. Add a type of vertical maps for all indexes.
3. Add independent types for inputs of all operations.
5. Convert each operation into a dependent type parametrised by vertical maps along indexes.}

<h2>§§ Discussion</h2>
1. {Proving existence of initial models for closed finitary XATs in HoTT-I}

2. {Is HoTT-I an extended algebraic theory?}

3. {Eating itself}

4. (2+3) — The problem of Type-valued functors from a concrete category.

5. {Possible generalisations of algebraic theories: 
– support for directed sorts (examples: skew monoids, skew semirings), ultimately opetopic theories (see “Towards Higher Universal Algebra in Type Theory” by Eric Finster)
— substructural logics and modalities (not only fibrant and bifibrant, but also cofibrant types on the semantic side): quantitative type theories & linear logic
— doctrine for monoidal theories over a generalised field, which turn into algebraic theories if the field is taken to be 𝔽₁ (example: Hopf algebra, models over 𝔽₁ has to be groups).
}
