#import "../template.typ": *
= Formalization of Two Theorems on Hall Subgroups
In this section, I formalize two theorems describing the behavior of Hall subgroups with respect to normal subgroups - namely under intersection and under forming products with a normal subgroup, as well as under passage to the corresponding quotient group.. Recall the definition 2.1.1, a subgroup $H <= G$ is a Hall subgroup if its index in $G$ and its cardinality is coprime.

While the theorems formalized in this chapter only rely on elementary tools such as index computations and the isomorphism theorems, the broader theory of Hall subgroups is closely connected to the structural analysis of finite groups. In particular, Sylow's theorems guarantee the existence of Hall subgroups in this special case.
However, for a general set of primes π, π-Hall subgroups do not necessary need to exist in arbitrary finite groups. The alternating group $A_5$, which is simple, provides a classical example where certain $pi$-Hall subgroups fail to exist. As these deeper structural aspects lie beyond the scope of the present thesis, I do not pursue them further here. Interested readers may consult a standard textbook in abstract algebra@Dummit for additional information.

== Mathematical Statement<4.1>
The following three definitions are used in the subsequent theorems and their proofs.

#definition[$H inter.sq N$][Let $G$ be a group and let $H,N ≤ G$. The intersection of $H$ and $N$ is defined as $H inter.sq N := {g in G| g in H and g in N}$. It is again a subgroup of $G$.] 

#definition[$H N$][Let $G$ be a group and let $H,N ≤ G$. The product of $H$ and $N$ is defined as $H N := {h n| h in H, n in N}$. In general, $H N$ is only a subset of $G$. If $H$ or $N$ is normal in $G$, then $H N$ is a subgroup of $G$.]

#definition[Subgroup chains][If $H$ and $N$ are both subgroups of $G$, and $N$ is also a normal subgroup of $G$, then we have  subgroup chains where $H inter.sq N$ $≤ H ≤ H N ≤ G$ and $H inter.sq N$ $≤ N ≤ H N ≤ G$.]

#theorem[Hall subgroups][If $H$ is a Hall subgroup of $G$ and $N$ is a normal subgroup of $G$, then $H ⊓ N$ is a Hall subgroup of $N$.]

A typical textbook proof proceeds as follows:
 since $H inter.sq N$ is a subgroup of $H$, we have $|H inter.sq N| ∣ |H|$ due to Lagrange's theorem. 

Since $N$ is a normal subgroup of $G$, the product of $H N$ forms a subgroup of $G$. A standard counting argument (see Proposition 13 in Sec.3.2 @Dummit) yields: $ |H N| = |H| dot |N| \/|H inter.sq N|. $ Rearranging the equation we get: 
  $ |N : H inter.sq N| = |H N| \/ |H| $ By Lagrange’s theorem, these quotients may be interpreted as indices, thus: $ |N : H inter.sq N| = |H N : H| $
Next, decomposing the index of $H$ in $G$ gives $ |G : H| = |G : H N| dot|H N : H| $ In particular $ |H N : H| ∣ |G : H| $. 

Now together with $|H inter.sq N| ∣ |H|$, we have:
  $|N : H inter.sq N| ∣ |G : H|$.
Since $|H|$ and $[G : H]$ are coprime (recall that $H$ is  Hall subgroup), then $|H inter.sq N|, |N : H inter.sq N|$ are also coprime.
 
#theorem[Hall subgroups][If $H$ is a Hall subgroup of $G$ and $N$ is a normal subgroup of $G$, then  $H N \/ N$ is a Hall subgroup of $G \/ N$.]

As in the proof of the theorem of 4.1.1, we use
  $|H N| = |H| dot |N|\/ |H inter.sq N|$. Dividing both by $|N|$ yields
$|H N\/N| = |H|\/|H inter.sq N|$.

Since $H inter.sq N ≤ H$, Lagrange’s theorem gives $|H inter.sq N| ∣ |H|$, 
so in particular
$|H N\/N| ∣ |H|$.

On the other hand,
$|G\/N : H N\/N| = |G : H N|$.

Because $H ≤ H N ≤ G$, multiplicativity of indices implies
$|G : H| = |G : H N| dot |H N : H|$, 
hence $|G : H N| ∣ |G : H|$, and therefore
$|G\/N : H N\/N| ∣ |G : H|$.

Let $d = gcd(|H N\/N|, |G\/N : H N\/N|)$. 

Then $d ∣ |H|$ and $d ∣ |G : H|$, hence $d ∣ gcd(|H|, |G : H|) = 1$. 

Since $H$ is Hall in $G$. Thus $d = 1$, and the result follows. 

== API Landscape<4.2>
=== Motivation 
Compared to the abelian simple case, the formalization of Hall subgroups requires a richer coordination of APIs. The two theorems express coprime properties that simultaneously involve subgroup cardinalities and subgroup indices, both of which are as natural numbers in Lean. While cardinality is straightforward to handle via `Nat.card` for finite types equipped with `Fintype` instance, the treatment of index is more delicate, as it interacts with multiple levels of subgroup structure. 

In pen-and-paper style mathematics, a subgroup can be viewed simultaneously as a subgroup of several groups without ambiguity. In Lean however, every term carries a specific type. For instance, $H inter.sq N$ may be represented as a term of type `Subgroup G` or `Subgroup N`. Although they represent the same underlying set in informal mathematics, they inhabit different types in Lean. Consequently, the choice of ambient group must be fixed during the formalization process.

The choice depends on how well existing APIs compose through coercions and whether additional bridging lemmas are required. If a lemma expects $H inter.sq N$ to inhabit  `Subgroup G` but it is represented as `Subgroup N`, when coercions do not adequately bridge these representations, additional lemmas are often required to connect them explicitly. Thus, the complexity of the Hall formalization stems not only from the mathematical content, but from the necessity of aligning type-level representations with the available API infrastructure.

The following subsections analyse the APIs that are required to support this coordination.
=== Representation of Index <4.2.2>
In mathematics, the index is defined as the number of left cosets: $|G : H| = |{g dot H|g in G}|$. Under additional assumptions, this quantity admits alternative descriptions:
- if H is a normal subgroup of $G$, the cardinality of the quotient group $|G : H| = |G \/ H|$.
- if G is a finite group, the ratio of cardinality (by Lagrange's theorem): $|G:H| = |G| \/ |H|$
In Mathlib, the standard definition of index is:
```lean
noncomputable def index : ℕ := Nat.card (G ⧸ H)
```If $H$ is a subgroup of $G$, its index in $G$ is expressed as `H.index`. This definition reflects the quotient-type perspective. During formalization, it is often convenient to rewrite the index in whichever form best suits the context: sometimes as the cardinality of a quotient type, sometimes as a numerical ratio. These expressions describe the same quantity under the relevant assumptions.

Moreover, when working with nested subgroups, such as $H inter.sq K <= K <= G$, I require the index of one subgroup relative to another. For this purpose, Mathlib provides the function `relIndex`:

```lean noncomputable def relIndex : ℕ := (H.subgroupOf K).index```

This expresses the index of a subgroup relative to a larger subgroup within the same ambient group, where `subgroupOf` is a construction in Lean which treats $H inter.sq K$ as a subgroup of $K$. As a result, in the first Hall subgroup theorem the $|N : H inter.sq N| $ could be written as `H.relIndex N`. 
=== The Subgroup API and Lattice Structure
One may notice that the intersection of two subgroups $H$ and $N$ is expressed using the meet operation $inter.sq$ rather than by directly referring to the intersection of their underlying sets. This reflects the fact that `Subgroup G` forms a lattice structure under the subgroup partial order.

Mathlib formalizes this structure in `Mathlib.Algebra.Group.Subgroup.Lattice`, where meet and join correspond to intersection and generated products of subgroups, respectively. As a result, standard subgroup constructions are available as lattice rather than set-theoretic operations. This design is not merely a mathematical convenience but is embedded in the library infrastructure. Structural properties of subgroups are therefore preserved at the API level, allowing us to focus on higher-level reasoning instead of repeatedly reconstructing basic subgroup facts.

To illustrate the importance of recognizing this lattice structure, consider a more direct approach one might take before fully exploiting the available API. In one of my early attempts, I explicitly constructed the intersection of subgroup $N$ as:
```lean
def inter_of_subHN {G : Type*} [Group G]
    (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup N :=
  (H ⊓ N).comap N.subtype
```
where I use the `comap` and `subtype` to manually transport $H inter.sq N$ from the original type Subgroup $G$ into the ambient group Subgroup $N$. While this construction is mathematically correct and accepted by Lean, it reimplements a structural translation that is already captured by the existing abstraction in Mathlib. The manual transport via `comap` becomes unnecessary. The subgroup API, together with the lattice structure and `relIndex`, provides a higher-level interface for reasoning about relative subgroups.  

=== The First and Second Isomorphism Theorem
Although it is not immediately clear how the first and second isomorphism theorems would contribute to the formal proof, I examine their formulations in Mathlib. The two Hall subgroup lemmas appear as exercises in the same section of Dummit and Foote, which suggests that structural considerations may be relevant to their proof strategies. This motivates a closer inspection of the corresponding formal statements.

In Mathlib, the first and second isomorphism theorems are represented purely structurally:
```lean
-- The First Isomorphism Theorem.
@[to_additive]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) 
  ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

-- Noether's Second Isomorphism Theorem. 
@[to_additive]
noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) 
    [hN : N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  quotientInfEquivProdNormalizerQuotient H N le_normalizer_of_normal
```
However, the Hall subgroup theorems are statements about indices, divisibility, and coprimality. From this consideration, what I ultimately require are numerical equalities rather than explicit group isomorphisms. In @4.3 I will clarify how these structural equivalences inform the development of the formal proof. 
=== Quotient Group
In Mathlib, a quotient group is defined for a normal subgroup `N : Subgroup G` and `[N.Normal]` via the quotient type `G ⧸ N`:
```lean
@[to_additive]
instance Quotient.group : Group (G ⧸ N) := (QuotientGroup.con N).group
```
The notation `G ⧸ N`, introduced via the `HasQuotient` type class, provides the quotient as a type. The assumption `[N.Normal]` is required to equip this type with a group structure via instance inference.
Associated with every normal subgroup is the canonical group homomorphism:
```lean
@[to_additive]
def mk' : G →* G ⧸ N :=
  MonoidHom.mk' QuotientGroup.mk fun _ _ => rfl
```
which maps each element of `G` to its equivalence class in the quotient. These constructions suggest two complementary entry points into quotient group reasoning:
- *Type-driven entry*: One works directly with the quotient type `G ⧸ N`, relying on instance inference to supply its group structure once `[N.Normal]` is available.
- *Morphism-driven entry*: Alternatively, one passes through the canonical homomorphism `G →* G ⧸ N`, transporting subgroup information via kernel and image constructions.
Both viewpoints describe the same mathematical object, but they emphasize different interactions within the library: the type-driven approach proceeds top-down, requesting a quotient group and relying on type class inference to provide the necessary structure. The morphism-driven approach follows the traditional mathematical route, constructing the quotient group bottom-up from explicit algebraic data. As discussed in @4.2.2, the index of a subgroup is defined via the cardinality of a quotient type `Nat.card (G ⧸ H)`. Consequently, quotient constructions are not merely structural devices: they directly interact with counting invariants. @4.3 clarifies how these two entry points cooperate in the formal proof of the Hall subgroup theorems.

== Formal Statements and Choices of Proof Strategy <4.3>
Conceptually, the Hall condition can be viewed as an arithmetic invariant expressed as $gcd(|H|, |G:H| = 1)$. The first proof shows that coprimality property propagates along the chain $H inter.sq N arrow H arrow G$, while the second proof is along $H arrow H N arrow G$ via quotient. Both proofs rely on translating the intersection and product operations into multipilicative relations among indexes. The key equation $|H N| = |H| dot |N| \/|H inter.sq N|$ serves as a bridge between subgroup-theoretic constructions and arithmetic invariant. Once this bridge is established, the problem reduces to divisibility propagation along index factorizations.
=== Revisiting the Paper Proof
Now I revisit the above argument from a formal perspective.

In this section I present the formal statements of the two Hall subgroup theorems and explain the strategic choices made in their formalization. As discussed in @4.1, both paper proofs rely on the proposition:$|H N| = |H| dot |N| \/|H inter.sq N|$， which in Lean could be expressed as a statement about the cardinality of the union of left cosets:
```lean
lemma card_of_left_cosets (H : Subgroup G) (N : Subgroup G) :
    Nat.card (⋃ h : H, h • N : Set G) =
    (Nat.card H * Nat.card N) / Nat.card ((H ∩ N : Set G)) := by sorry
```
While this is mathematically faithful, it is technically inconvenient in a formal proof because the counting happens at the level of `Set G`. In Lean, `Set G` is defined as a predicate `G → Prop`, so it doesn't carry finiteness or cardinality data directly. To compute the cardinality of a union such as `⋃ h : H, h • N`, one must first reinterpret it as a subtype and provide appropriate `Fintype` or `Finite` instances. 

Rather than pursuing this set-level counting approach, the formal development uses the second isomorphism theorem `quotientInfEquivProdNormalQuotient`, as discussed in 4.2.4,  to get counting information and massage the term into the shape that I want. From the isomorphic structure $H \/ (H inter.sq N) tilde.equiv H N\/ N$, I have $ |H N\/ N| = |H \/ (H inter.sq N)| = |H| \/ |H inter.sq N| $

In the formal development, the Hall condition is expressed as the arithmetic statement
`Nat.gcd (Nat.card H) H.index = 1`.
Coprimality is therefore encoded directly as an equality in `ℕ`, and its propagation is realized through explicit divisibility relations such as `X.index ∣ Y.index` and `Nat.card K ∣ Nat.card H`. Rather than reasoning informally about prime factors, the proof transforms a `Nat.gcd = 1` statement along a chain of divisibility lemmas.

From this formal perspective, the stability of the Hall property emerges as a structured arithmetic invariant encoded at the level of natural numbers and transported through subgroup operations, rather than as a consequence of informal counting arguments.

=== The Formal Proof of the First Theorem
The formal statement of the first Hall subgroup theorem is:
```lean
/-! Prove that H ⊓ N is a Hall Subgroup of N-/
theorem hall_inter_of_normal_is_hall {G : Type*} [Group G] [Fintype G] 
    (H : Subgroup G) (N : Subgroup G) [N.Normal]
    (hH : Nat.Coprime H.index (Nat.card H)):
    Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by sorry
```
I start from rewriting the coprimality goal using `Nat.coprime_iff_gcd_eq_one`. 

The original goal
```lean
⊢ (H.relIndex N).Coprime (Nat.card ↥(H ⊓ N))
```
is thus transformed into 
```lean
⊢ (H.relIndex N).gcd (Nat.card ↥(H ⊓ N)) = 1
```
The key idea is not to compute the detail about this gcd explicitly. Instead of analysing the prime factors of `H.relIndex N` and `|H ⊓ N|`directly, I prove that their gcd divides  `gcd(|G:H|, |H|)`, which equals to $1$ by the Hall subgroup assumption on $H$. Accordingly, the central intermediate goal becomes:
```lean
⊢ (H.relIndex N).gcd (Nat.card ↥(H ⊓ N)) ∣ H.index.gcd (Nat.card ↥H)
```
From here I establish the divisibility statement into two steps:
- First, I prove: 
```lean
    have h1 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ 
      H.index := by sorry
```
- Second, I prove:
```lean
    have h2 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ 
      Nat.card H := by sorry
```
After that this proof can be done by `Nat.dvd_one`.

I make a few remarks on the auxiliary tools used in this argument. In `h2`, the result follows directly from Lagrange's theorem, while `h1` needs more effort due to the followling reasons:

Many lemmas in mathlib describe the index of a normal subgroup relative to an ambient subgroup (e.g. `N.relIndex H`), whereas here I need information about `H.relIndex N`. To bridge this gap, I establish the following multiplicative relation:
```lean
theorem index_eq_index_sup_mul_relIndex_of_normal {G : Type*} [Group G] 
    [Fintype G] (H N : Subgroup G) [N.Normal] :
    H.index = (H ⊔ N).index * H.relIndex N := by sorry -- proof omitted
```
The above identity reflects the interaction between normality and lattice operations and can be viewed as a cardinal version of the second isomorphism theorem.

Secondly, to support this, I also formalize a cardinal formulation of the second isomorphism:
```lean
theorem snd_iso_card_normalizer {G : Type*} [Group G] [Fintype G] 
    (H N : Subgroup G) [N.Normal] :
    Nat.card (H ⧸ N.subgroupOf H) = 
    Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by sorry --proof omitted
```
This lemma serves as a bridge between the structural isomorphism theorem and the numerical identities required for index computations.
=== The Formal Proof of the Second Theorem
The formal statement of the second Hall subgroup theorem is:
```lean
/-! Prove that HN ⧸ N is a Hall subgroup of G ⧸ N-/
theorem quo_of_sup_normal_hall_is_hall {G : Type*} [Group G] [Fintype G]
    (H N: Subgroup G) [N.Normal]
    (hH : Nat.Coprime H.index (Nat.card H)) :
    Nat.Coprime ((H ⊔ N).map (QuotientGroup.mk' N)).index
    (Nat.card ((H ⊔ N).map (QuotientGroup.mk' N))) := by 
  sorry --proof omitted
```
The formal proof resembles the pen-paper proof in @4.1: under the assumption `Nat.Coprime H.index (Nat.card H)`, the strategy is to prove:
- new index, namely `((H ⊔ N).map (QuotientGroup.mk' N)).index`, divides the old index `H.index`
- new cardinality, namely `Nat.card ((H ⊔ N).map (QuotientGroup.mk' N))`,  divides the old cardinality `Nat.card H `

Thus the proof skeleton is constructed by two division goals and three proof terms:
```lean
  -- equation |G ⧸ N : HN ⧸ N| = |G : HN|:
  have I : ((H ⊔ N).map (QuotientGroup.mk' N)).index = (H ⊔ N).index := by 
    sorry -- proof omitted
  -- Goal 1: to prove |G ⧸ N : HN ⧸ N| ∣  |G ∣ N|
  have thisI : ((H ⊔ N).map (QuotientGroup.mk' N)).index ∣ H.index := by
    simpa [I] using (Subgroup.index_dvd_of_le (le_sup_left : H ≤ H ⊔ N))
  -- Goal 2: to prove |HN ⧸ N| ∣ |H|
  have thisII : Nat.card ((H ⊔ N).map (QuotientGroup.mk' N)) ∣ 
      Nat.card H := by 
    sorry -- proof omitted
  exact Nat.Coprime.of_dvd thisI thisII hH
```
The proof of `have I` uses the lemma `Subgroup.index_map_eq`, in which I use the canonical quotient map `let f : G →* (G ⧸ N) := QuotientGroup.mk' N` to show that the index remains unchanged when projecting `H ⊔ N` into the quotient group `G ⧸ N`. After that I use the subgroup relation `H ≤ H ⊔ N` to get the first divisibility statement. The Proof of `thisII` needs some additional treatment due to dependent types: the cardinality of a group should remain the same regardless of whether it is viewed as a subgroup A or as subgroup B. I use a lemma to establish this property, and present its whole proof here, since there are several points I want to illustrate:
```lean
lemma card_supQuotient_eq_card_map
    {G : Type*} [Group G] [Fintype G]
    (H N : Subgroup G) [N.Normal] :
    Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) =
    Nat.card ((H ⊔ N).map (QuotientGroup.mk' N)) := by
  apply Nat.card_congr
  let f : ↥(H ⊔ N) →* (G ⧸ N) :=
    (QuotientGroup.mk' N).comp (Subgroup.subtype (H ⊔ N))
  have hker : f.ker = N.subgroupOf (H ⊔ N) := by aesop
  have hrange : f.range = (H ⊔ N).map (QuotientGroup.mk' N) := by aesop
  have hIso :
      (↥(H ⊔ N) ⧸ f.ker) ≃* ↥f.range := 
    QuotientGroup.quotientKerEquivRange f
  have hQuot : (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) ≃* (↥(H ⊔ N) ⧸ f.ker) :=
    QuotientGroup.quotientMulEquivOfEq (G := ↥(H ⊔ N)) 
    (M := N.subgroupOf (H ⊔ N)) (N := f.ker) hker.symm
  have hRange : ↥f.range ≃* ↥((H ⊔ N).map (QuotientGroup.mk' N)) := by
    rw [hrange]
  exact (hQuot.trans hIso).trans hRange |>.toEquiv
```
 Mathematically, the equality $∣H N\/(N inter.sq H N)∣=∣H  N$ mapped into $G\/N∣$ is an immediate consequence of the first isomorphism theorem.
However, in Lean this equality must be obtained by explicitly constructing an equivalence of types. The invocation of `Nat.card_congr` at the beginning of the proof therefore determines the entire strategy. To establish equality of cardinalities, one must:
- construct the canonical homomorphism, which is:
```lean 
      let f : ↥(H ⊔ N) →* (G ⧸ N)
```
- identify its kernel and range, I oberserve that in:
```lean 
      have hker : f.ker = N.subgroupOf (H ⊔ N)
```

```lean
      have hrange : f.range = (H ⊔ N).map (QuotientGroup.mk' N)
```
- apply the formal first isomorphism theorem:  
```lean
      have hIso : (↥(H ⊔ N) ⧸ f.ker) ≃* ↥f.range :=
        QuotientGroup.quotientKerEquivRange f
```
- and transport the resulting multiplicative equivalence to a type-level equivalence: 
```lean
      exact (hQuot.trans hIso).trans hRange |>.toEquiv
```



 