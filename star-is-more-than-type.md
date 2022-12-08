The `*` is more than type, `(→)` is more than function.
=====================================================

We present a sketch of an extension of the Higher Homotopy Type Theory (HOTT) by first-class notions of Reedy categories explicit polymorphism, so as to allow to handle simplicial and similar types, and handle higher categorical objects and large categories neatly. and provides a part

§ Introduction
--------------

In his Topos Institute Lecture “Cats and Types: Best Friends?“ C. McBride presented a yet unpublished idea of inductive types that are simultaneously inductively defined categories, associative and directed by construction.

Extending this idea of we propose to extend the by a new notion parallel to types: indices. Mathematically indices correspond to Reedy Categories and indexed inductive types on them are precisely Type-valued presheaves on these categories.

In the original HOTT, only the type formers manifestly differentiate between indexes and parameters. In our extension functions and constructors will be manifestly differentiate beween arguments `(\arg : type)` and parameters `[\p : signature]`. Indices cannot play the role of a type, but are used in signatures.

We be able to define various very useful indices:
- The index CatCarrier so that `[C : CatCarrier → *] ≡ [C.Ob : *, C.Mor : Ob → Ob → *]`;
- For various definitions of n-Categories (globular, simplicial, etc) the index `nCatCarrier[n]` so that
```
  [C : CatCarrier → *] ≡ [C.Cell(0) : *, C.Cell(1) : Ob → Ob → *, C.Cell(2) : ···,...C.Cell(n) : ··· ]
```   
  therefore n-Categories and n-Functors between them could be defined generically for all n. 
- The indices Δ⁺ and Δ such that parameters `[SST : Δ⁺ → *]` and `[ST : Δ → *]` will correspond precisely to semi-simplicial and simplicial types respectively. This way it will be possible to define ω-categories and various other interesting objects.

We will also introduce a notion of generalized inductive types (indexed by an index defined mutually with the type itself, which is itself a generalization of inductive-inductive types). We will show that bidirectionally presentable type theories such as the domain-specific type theories CaTT (cf. Globular weak ω-categories as models of a type theory, by E. Finster, S. Mimram) and virtual equipment type theory (VETT) that provides a semantic model for formal category theory can be implemented as generalized inductive types.


§ Signatures
------------

Signatures play the role of types for polymorphy parameters of functions and typeformers, as well es for indices of type formers.

A valid signature is given by 
- `*` that roughly corresponds to  “any type”;
- an index;
- a `[type]`; or
- `signature → typeformer-signature`,

A valid typeformer signature is given by 
- `*`
- `signature → typeformer-signature`

In both cases, arrows allow dependencies.

Some examples of valid signatures:
```
  *
  Δ
  [Nat] → *
  * → *
  * → (Δ⁺ → *)
  (T : *) → Monoid[T] → *
  
```
  
Here are some invalid ones:
```
  * → [Nat]
  Δ⁺ → Δ
```

The point of * is more than Type lies in the property that any structure on the carrier of the signature `[C : I → *]` can be automatically lifted to the carrier of the signature `[C :  I → ((J → *) → *)]` where `J` is an arbitrary index. That corresponds to the property of elementory higher topos structure to be preserved under building presheaves.

§ Indexes
---------

Indices are built as inductive types augmented by arrows between inhabitants. There are two kinds of arrows: left arrows (called embeddings) are allowed to connect a structurally smaller inhabitant to the larger one, the right ones (called projections) exactly the opposite: 
```
#Index NatBound : *
  0 : NatBound
  (_') : NatBound → NatBound
  [\n : NatBound] |Extend(\m : Nat)〉 [n.rec n (_') ]
  |Extend(\m : Nat)〉 |Extend(\p : Nat)〉 ↦ |Extend(n + m)〉 
```
Indexes correspond the mathematical notion of Reedy Categories.

§§ Degeneracies: Example of `FiniteNatVector`
---------------------------------

В одном из предыдущих постов мы встречались разложением положительных целых чисел на простые:
factorize : PosInt → List[Nat]
Функция factorize выдаёт нам список степеней последовательных простых чисел в разложении аргумента. Первый элемент — степень двойки в аргументе, потом степень тройки, степень пятёрки, степень семёрки и т.д.
(factorize 60) = List\(2, 1, 1)
Однако тип результата не совсем аккуратен. Дело в том, что результаты List\(a, b,.., c) и List\(a, b,.., c, 0,.., 0) эквивалентны, произвольное количество нулей в конце можно опускать.
Обозначим такой тип
```
#Synthetic DList[\T : *](zero : T):
   EmptyDList[\T] : DList[T]
   NonEmptyDList(\head : \T, tail : DList[T]) : DList[T]
   Expand[\T]
   : EmptyDList[T] = NonEmptyDList[T](zero, EmptyDList[T])
```
Теперь можно выписать правильную сигнатуру факторизации —
```
  factorize : PosInt → DList[Nat](0)
```  
Для такого типа функцию length вообще говоря определить невозможно. Она же должна выдавать один и тот же результат независимо от количества нулей в конце, в то же время проверять элементы на “нулёвость” вообще говоря невозможно, тип T можеть не иметь разрешимого равенства (таков, например, тип вещественных чисел, там равенство лишь опровергаемо, но не проверяемо).
Но нам бы хотелось выражать в типе тот факт, что один такой список не длиннее другого. Нам понадобится синтетический индекс — “обобщённый тип”, где вместо образующих равенства задаются образующие конверсий (да, это будет категория, но не всё сразу).
```
#Index NatBound:
   #import Nat
   [n] |Expand> : PosInt[n]
```
Теперь мы можем выписать определение списка, ограниченного длинной bound:
```
#Synthetic BList[\T : *, bound : NatBound](default : T):
   EmptyBList[\T] : BList[T, Zero]
   NonEmptyBList(\head : \T, tail : BList[T, bound])
   : BList[T, Succ(bound)]
   EmptyBList[\T] |Expand>
   ↦ NonEmptyBList[T](default, EmptyBList[T])
   NonEmptyBList(\head : \T, tail : BList[T, \bound]) |Expand>
   ↦ NonEmptyBList[T](head, tail |Expand>)
```
   
Последние четыре строчки имплементируют конверсию NatBound.|Expand>. Теперь если `n < m`, то
```
  BList[T, n] <: BList[T, m]
```  
причём при переводе из первого во второе, список автоматически добивается в конце нужным количеством нулей.
В нашем примере конверсии внутри индекса порождаются одной образующей. Однако вообще говоря, может быть много образующих, они могут быть с параметрами (таким образом их может быть даже более чем счётное количество), и они могут быть несвободные — мы можем определить на них операцию композиции. Важно однако, что target всегда ≥ source, то есть исключены циклы, исключая эндоморфизмы. Эндоморфизмы в индексированных типах должны обращаться в автоморфизмы.

§§ Dependencies
---------------

Прежде я рассказал про индексы с правыми стрелками (degeneracies), которые позволяют организовать ковариантный сабтайпинг вдоль индексов. Сейчас я расскажу, что индексы могут иметь ещё и левые стрелки (dependencies).

Я обещал рассказать, как зависимые пары выражать как отображения. Именно для этого нам понадобится ввести индексы с левыми стрелками. Вот простейший пример:
```
#Index 𝟚ⱽ:
   Fst
   Snd
   [Snd] 〈Pre| [Fst]
```
На индексах нельзя задовать функции (в фиксиованный тип T), но задавать индексированные им типы T : 𝟚ⱽ -> * или модельные функторы (в иные индексы или вселенные).
Чтобы задать функтор на индексе, нужно задать действие на на всех конструкторах, причём, если в какой-то конструктор (например Snd) ведут левые стрелки, (например, `〈Pre|`) задаём действие на них в терминах экстракторов:
```
T : 𝟚ⱽ → *
T(Fst) ↦ Nat
T(Snd) ↦ Σ(\n : Nat) Fin[n]
T(〈Pre|) ↦ fst
```
Таким образом сигнатура `(X : *, Y : X -> *)` теперь эквивалентна `(𝟚ⱽ → *)`.



Сигнатура кванторов Σ, ∃ и ∀ 
```
  (X : *, Y : X → *) → *
```
теперь выражается
```
  (𝟚ⱽ → *) → *
```

§ Categories as master examples
-------------------------------

Рассмотрим категорию как структуру на носителе
```
#Structure Cat[Ob : *, Mor : Ob → Ob → *]:
  id[T : Ob] : Mor[T, T]
  compose[X Y Z : Ob] : Mor[X, Y] → Mor[Y, Z] → Mor[X, Y]
  ... axioms
```
  
Определим
```
#Index CatCarrier:
  Ob
  Mor
  [Hom] 〈src| [Ob]
  [Hom] 〈tgt| [Ob]
```
Теперь носитель категории можно записать просто как `CatCarrier → *`:
```
#Structure Cat[C : CatCarrier → *]:
  id[T : C.Ob] : C.Mor[T, T]
  compose[X Y Z : C.Ob] : C.Mor[X, Y] → C.Mor[Y, Z] → C.Mor[X, Y]
  # axioms
```
  
Это даёт нам целых две новых возможности!

Во-первых, без этой штуки мы вообще не могли выразить носитель высхых категорий! У вего веть есть не только `C.Ob = C.Cell(0) и C.Mor = C.Cell(1)`, но и ячейки высших порядков до бесконечности.

А во-вторых, это позволяет нам работать с осмысленной разновидностью large категорий: категорий множеств, оснащённых структурой. Скажем, категории всех групп.

Структура группы `Group[T : *]` может рассматриваться как функтор `Group : * -> *`. Сигнатура больших категорий монструозна:
```
#Structure CatOfStructuredSets[Ob : * -> *,
 Mor : (SrcCarrier : *) → (TgtCarrier : *)
 → (SrcStructure : S[SrcCarrier])
 → (TgtStructure : S[TgrCarrier])
 → *]
```
Скажем категория всех групп это структура типа `CatOfStructuredObjects[Ob: Group, Mor: GroupHomomorphism]`
С использованием индекстного типа `CatCarrier` возникает возможность записать всё это куда проще:
```
#Structure CatOfStructuredSets[\С : CatCarrier  → (* → *)].
```
Вообще-то мы всегда можем заменить у полиморфной структуры носитель c `[I → *]` на `[I → (* → *)]` и даже на `[I → ((J → *) → *)]` — это следует из того, что вся структура высшего топоса переносится на предпучки и пучки на этом топосе (и, как обычно, леммы Йонеды). Машинерия по формулированию всех сигнатур методов и всех аксиом структуры может быть полностью механизирована, в результате нам не нужно отдельной структуры `CatOfStructuredSets`, мы можем просто сказать что * is more than Type, и определив лишь структуру `Cat[С : CatCarrier  →]` за бесплатно декларировать её инстансы
```
#Define Grp : Cat[C.Ob: Group, C.Mor: GroupHomomorphism]
  ... realization
  
#Define Rng : Cat[C.Ob: Ring, C.Mor: RingHomomorphism]
 ... realization
```

Больше того, если мы определим также n-категории
```
#Structure nCat[\n : Nat][\С : CatCarrier[n]  → *] 
  ... realization
```
такие что `Cat ≅ nCat[1]`, и nFunctor'ы между ними
```
#Structure nFunctor[\n : Nat][\С : CatCarrier[n']]
  ... realization
```

такие что
```
  Cat ≅ nFunctor[1][Cell(0)]
  Functor ≅ nFunctor[1][Cell(1)]
  NatTrans ≅ nFunctor[1][Cell(2)]
```
Функторы n-ного уровня образуют категорию n'-го уровня

```
#Define nCAT(\n) : nCat[n'][nFunctor[n]]
  ... realization
```

В частности обычные категории, функторы между ними и естественные образования между ними образуют 2-категорию nCAT(1).


§ Generalized Inductive Types and Extended Algebraic Theories
-------------------------------------------------------------

...