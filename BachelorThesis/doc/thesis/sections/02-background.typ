= Background (4 Pages)
== Group Theory
explain very basic stuffs of group theory
== Lean 
explain how to read Lean code(the necessary technical stuffs, which only related to Lean)
== Mathlib
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