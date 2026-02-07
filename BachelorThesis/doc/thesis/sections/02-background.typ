#import "../template.typ": *

= Background (5 Pages)

In this section, we provide preliminaries about this thesis, which include necessary math background, knowledges about how to read lean code relating to this project and group theory library of mathlib.

== Group Theory (1.5 Pages)
We recall some basic definitions from group theory.

A _group_ is a set $G$ together with a binary operation
$dot.op : G times G arrow.r G$ satisfying the following axioms: associativity $(g_1 dot g_2) dot g_3 = g_1 dot (g_2 dot g_3)$, the existence of a neutral element $e_G$ and the existence of an inverse elememt $g^(-1)$ for all $g in G$. If all elements of a group also satisfy commutativity, then it is called _Abelian group_ or _commutative group_. The _cardlinality_ of a group $G$, denoted as $|G|$, is defined as the cardinality of the underlying set. A group is finite if $|G| < infinity$, and infinite otherwise.

Homomorphism and isomorphism: A _group homomorphism_ is a function between groups that preserves the group operation, which means $f : G arrow.r H$  satisfying $f(x dot y) = f(x) dot_H f(y)$ for all $x,y in G$. A homomorphism $g$ is called a left inverse of $f$ if
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
Lean is an interactive proof assistant based on principle that propositions are represented as types, and proofs correspondent to terms inhabiting these types. This view allows treating mathematical statements and proofs as structured objects that can be manipulated and checked by the system. (*citation*)

In Lean, a mathematical theorem is introduced by keywords such as `theorem` or `lemma`, followed by a name, a list of parameters, and type annotations of this theorem. A proof is then provided by constructing a term of this type. 
```lean
theorem lagrange {G : Type*} [Group G] (H : Subgroup G) :
    Fintype.card G /  Fintype.card H = Fintype.card 
    (a • (H : Set G) : Set G) := by 
  sorry
```
In the example above, `lagrange` is the theorem's name. The expression between the name and colon specify the parameters and assumptions of the theorem. The expression following the colon and colon equals is the type of the theorem. The symbol `:=` introduces the proof, and the code following it constitutes the corresponding proof term. When the keyword `by` is used, the proof is written in tactic mode. Tactics are tools that facilitate the construction of proof terms.(*citation Lean language manual*)When a tactic is applied, we could observe in `Info-View` from our editor that the proof state is been modified.

== Mathlib (2.5 Pages)
In this section, we introduce the necessary preliminaries of mathlib that are used in the main part of this thesis. Mathlib is currently the biggest and the most widely used library for formalized mathematics(*citation*) and is under active development. Contributions to mathlib are subject to a strict code view process and are required to follow its design principles. One of the central design principles of mathlib is the use of _type class_ to encode mathematical structures (*citation*). This mechanism plays a fundamental role in the formalization of group theory and underlies the constructions and tools used throughout this section.
=== The absrtaction hierarchy of group theory API (1 page)
This section outlines the layers of abstraction in group theory library, focusing on how algebraic structures are organized and related through type class.
TODO



=== Tools that I have used (1 page)
We summarize the main components of mathlib that are used...
TODO
参考下面列出来的一大片tools。

=== Looking up lemma (0.5 page)
We briefly talk about how to find the potentially useful lemma in the big and complex API...
TODO


explain the following stuffs: 
=== The definition hierachy of group in mathlib
- *explain* Group definition hierachy in mathlib:
In mathlib the most basic definition of a group are:
```lean
class Group (G : Type u) extends DivInvMonoid G : Type u
class AddGroup (A : Type u) extends SubNegMonoid A : Type u
```

In this thesis we are mostly handling on the following extensions of basic groups, one is commutative group, the other is quotient group.

=== Distinction between group and additive group in mathlib
- *explain* the distinction and the to_additive notation in mathlib group section, and when it matter during the formalization.

=== Commutative group
- explain its usage shortly
```lean
-- An additive commutative group is an additive group with commutative (+)
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G : Type u

-- A commutative group is a group with commutative (*).
class CommGroup (G : Type u) extends Group G, CommMonoid G : Type u
```

=== Normal Subgroup
- explain its usage shortly
- using N.normal as typeclass parameter
```Lean
class Subgroup.Normal {G : Type u_1} [Group G] (H : Subgroup G) : Prop
```
=== Quotient group
- explain why it is an instance
- prepare the context of its usage in latter formalization
```lean
instance QuotientGroup.Quotient.group {G : Type u_1} [Group G] (N : Subgroup G) [nN : N.Normal] : Group (G ⧸ N)
```