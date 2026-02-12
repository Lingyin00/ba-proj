#import "../template.typ": *

= Background (5 Pages)

This section presents the mathematical and technical background necessary for the subsequent formalization, including essential notions from group theory, key mechanisms of Lean, and an overview of the mathlib environment.

== Group Theory (1.5 Pages)
We recall some basic definitions from group theory.

A _group_ is a set $G$ together with a binary operation
$dot.op : G times G arrow.r G$ satisfying the following axioms: associativity $(g_1 dot g_2) dot g_3 = g_1 dot (g_2 dot g_3)$, the existence of a neutral element $e_G$ and the existence of an inverse elememt $g^(-1)$ for all $g in G$. If all elements of a group also satisfy commutativity, then it is called _Abelian group_ or _commutative group_. The _cardlinality_ of a group $G$, denoted as $|G|$, is defined as the cardinality of the underlying set. A group is finite if $|G| < infinity$, and infinite otherwise.

A _group homomorphism_ is a function between groups that preserves the group operation, which means $f : G arrow.r H$  satisfying $f(x dot y) = f(x) dot_H f(y)$ for all $x,y in G$. A homomorphism $g$ is called a left inverse of $f$ if
$g compose f = id_G$, and a right inverse if
$f compose g = id_H$, where $id_G$ and $id_H$ denote the identity maps
on $G$ and $H$, respectively. The _kernel_ of a homomorphism, is defined as $ker(f) = {g in G| f(g) = e_H}$. An _isomorphism_ is a homomorphism with a left and a right inverse. When two groups are _isomorphic_, denoted as $G_1 tilde.equiv G_2,$ they have the same group theoretic structure. 

There are two ways to obtain "smaller groups" from a given group: by passing to a _subgroup_, or by forming a _quotient group_. 

A _subgroup_ is a subset $H$ of $G$ whose elements also satisfies the three axioms above. An important class of subgroups is given by _cyclic subgroup_, if it is generated only by a single element. Among all subgroups of a group $G$, there is always a smallest one, namely the trivial subgroup ${e}$, and a largest one, namely $G$ itself. These form the bottom and top elements of the lattice of subgroups of $G$. A group is called _simple_ if it has no non-trivial normal subgroups.

We define the _quotient group_ via an equivalence relation. Let $G$ be a group and let $H$ be a subgroup of $G$, we define an equivalence relation on $G$ by $g ~ h <==> g^(-1) dot h in H.$ The equivalence class of an element $g in G$ is given by $[g] = g dot H$, which is called the _left coset_ of $H$ in $G$. The _index_ of $H$ in $G$, denoted as $[G:H]$, is defined as the cardinality of left cosets of $H$ in $G$. The set of equivalence classes $G \/ H$ is called the _quotient_ of $G$ by $H$. However not every subgroup admits a quotient group construction. This leads to the notion of a _normal subgroup_. $H$ is a normal subgroup of $G$ if and only if $g dot H dot g^(-1) = H$ for all $g in G$. In this case, $G \/ H$ is called a quotient group of $G$ by $H$. Equivalently, $[G:H] = |G \/H|$.

The following definitions and theorems provide the main algebraic tools for the proofs in this project.
#definition[Abelian simple Group][If a group is abelian and simple, i.e, it is a commutative group and has no trival subgroup, then it is an Abelian simple group.]
#definition[Hall Subgroup][A subgroup $H$ is called a Hall Subgroup of a finite group $G$, if its index is coprime to its cardinality.]

The Lagrange's theorem relates the size of a subgroup to the size of the ambient group via the notion of index, and provides a basic constraint on possible subgroup structures in finite groups.
#theorem[Lagrange's theorem][Let $G$ be a finite group and $H$ is a subgroup of $G$. Then $|G : H| = |G| \/ |H|.$]
While Lagrange’s theorem constrains subgroup sizes, the following two isomorphism theorems describe how isomorphism factor through quotient groups. The first isomorphism theorem formalizes the idea that the essential structure captured by a homomorphism is obtained by factoring out its kernel. The second isomorphism theorem describes how isomorphism arises from inclusion and intersection relations between subgroups.
#theorem[The first isomorphism theorem][If $phi:$ $G arrow H$ is a group homomorphism, then $ker(phi)$ is a normal subgroup of $G$, and $G \/ker(phi) tilde.equiv phi(G).$]
#theorem[The second isomorphism theorem][Let $G$ be a Group and let $A, B$ be subgroups of $G$ such that $a dot B dot a^(-1) = B $ for all $a in A$. Under this assumption, we have:
  - $A union.sq B$ is a subgroup of $G$
  - $B$ is a normal subgroup of $A union.sq B$
  - $A union.sq B \/B tilde.equiv A \/ (A inter.sq B)$]


== Lean (1 Page)
TODO: 
- add basic knowledge of Lean's type system like Type and Prop
- To write a theorem is to create an inhabitant in Prop

Lean is an interactive proof assistant based on _dependent type theory_, in which propositions are represented as types, and proofs correspondent to terms inhabiting these types. This view allows treating mathematical statements and proofs as structured objects that can be manipulated and checked by the system. (*citation*)

In Lean, a mathematical theorem is introduced by keywords such as `theorem` or `lemma`, followed by a name, a list of parameters, and type annotations of this theorem. A proof is then provided by constructing a term of this type. 

As an illustration, we can formulate Lagrange's theorem in Lean as follows:
```lean
theorem lagrange {G : Type*} [Group G] (H : Subgroup G) :
    Fintype.card G /  Fintype.card H = Fintype.card 
    (a • (H : Set G) : Set G) := by 
  sorry
```
In the example above, `lagrange` is the theorem's name. The expression between the name and colon specify the parameters and assumptions of the theorem. The expression following the colon and colon equals is the type of the theorem. The symbol `:=` introduces the proof, and the code following it constitutes the corresponding proof term. When the keyword `by` is used, the proof is written in tactic mode. Tactics are tools that facilitate the construction of proof terms(*citation Lean language manual*). When a tactic is applied, we could observe in `Info-View` from our editor that the proof state is been modified.

In Lean, parameters enclosed in parentheses denote explicit arguments, such as `(H : Subgroup G)`, which must be provided by the user when invoking a definition or theorem. In contrast, parameters enclosed in curly braces, such as `{G : Type*}`, denote implicit arguments, meaning that Lean attempts to infer them from the context. Square brackets indicate type class parameters, for instance `[Group G]`, which trigger Lean’s instance inference mechanism.

_Type classes_ serve multiple purposes. In this thesis, they are primarily used to represent algebraic structures together with the axioms they satisfy(*cite Lean Language manual type class*). When a type class parameter is required, Lean automatically searches for a suitable instance registered in the environment. This process can also be invoked explicitly using the command `inferInstance`, which instructs Lean to construct the appropriate instance if one is available.

Note that a mechanism named _coercion_ appears in `(a • (H : Set G) : Set G)` from the theorem statement above. Here, the subgroup `H : Subgroup G` is explicitly coerced to its underlying set `H : Set G`.  Although the coercion is written explicitly in this example, Lean often inserts such coercions automatically during elaboration when a term is used in a context expecting a compatible type.
For instance, coercions are frequently used to pass from `Nat` to `Int`, or from algebraic structures to their underlying carrier types.

== Mathlib (2.5 Pages)
Rather than being merely a large collection of formalized theorems, mathlib is shaped by a design philosophy centered on abstraction, generalization and systematic reuse through typeclass inference. The library favors small composable lemmas that act as bridges, enabling the construction of more complex results in a modular way(*citation the mathlib paper from Anne*). The design philosophy becomes particularly visible in its algebraic hierarchy, where algebraic structures are not defined independently, but through several layers by using type classes. A representative example is the definition of a group in mathlib:
```lean
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
```
Here the keyword `class` defines `Group` as a type class, whose instances can be automatically inferred by Lean. Morover, the keyword `extends` indicates that `Group` inherits all operations and lemmas associated with a more primitiv structure `DivInvMonid`: 
```lean
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G : Type u
```
It is again a type class inheriting from `Monoid`, while `Inv G` and `Div G` introduce inverse operation and the division without redifining a new `G`. The classes `Inv G` and `Div G` originate from the `Init/Prelude`, the first file in the Lean import hierarchy. This reflects the fact that algebraic hierarchy in mathlib is constructed incrementally from foundational operational structures provided by the core language.

The development of mathlib is a collaborative, commuity-driven process involving contributors from around the world. Contributions are submitted via pull request and undergo rigorous code view by maintainers and viewers. To ensure the quality of code, a pull request often goes through several rounds of refinements, generalizations and modifications before being merged. Consequently, formalization in mathlib is not only a mathematical formalization activity, but also an interaction with an envolving infrastructural system.

Due to the scale and complexity of the library, efficient navigation becomes an efficient skill in this project. Locating exisiting lemmas is crucial tp avoid duplication and to reuse established results. The mathlib documentaion(*citation the mathlib documentation*) usually serves as the primary entry point. It is organized into thematic cateogries such as `GroupTheory`, `FieldTheory`, each containing several more specialied subtopics. For instance, `Coset`, `Subgroup`, `QuotientGroup` are subtopics under `GroupTheory`. Furthermore, under each subtopic, definitions are collected into section `Defs`, basic theories are placed into `Basic`, and the core results are into other labels. Using the mathlib documentaion to locate a lemma usually need us to know the name of the lemma. While during the formalization process, the name of a lemma might not always be obvious. Tools such as _LeanSearch_ allows us to qury lemmas semantically, while ineratcive tactic like `apply?` could also give us hints. In practice, most commonly needed results already exist within the library; thus, working within mathlib often involves identifying and adapting existing components rather than constructing proofs entirely from scratch.

TODO: the most important infrastructures in this thesis: Subgroup.normal as Prop-class, quotient group instance, coercion between subgroup and group, distinction between AddGroup and MulGroup


