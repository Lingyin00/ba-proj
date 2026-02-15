#import "../template.typ": *
= Formalization of Two Theorems on Hall Subgroups(9 pages)
In this section, we formalize two theorems describing the behavior of Hall subgroups with respect to normal subgroups - namely under intersection and under forming products with a normal subgroup and passing to the corresponding quotient group. 

While the theorems formalized in this chapter only rely on elementary tools such as index computations and the isomorphism theorems, the broader theory of Hall subgroups is closely connected to the structural analysis of finite groups. In particular, every Sylow subgroup of a group is a Hall subgroup(corresponding to the prime set ${p}$). However unlike Sylow subgroups, Hall subgroups do not necessarily exist in arbitrary finite groups. The alternating group $A_5$, which is simple, provides a classical example where certain $pi$-Hall subgroups fail to exist. As these deeper structural aspects lie beyond the scope of the present thesis, we do not pursue them further here. Interested readers may consult a standard textbook in abstract algebra for additional information.

== Mathematical statement (1 page)
 #theorem[Hall Subgroups][If $H$ is a Hall subgroup of $G$ and $N$ is the normal subgroup of $G$, then $H ⊓ N$ is a Hall subgroup of $N$.]

One typical textbook proof idea is sketched as follows:
firstly, since $H inter.sq N$ is a subgroup of $H$, we have $|H inter.sq N| ∣ |H|$ due to Langrage theorem. 

Since $N$ is a normal subgroup of $G$, and $H N$ is the subgroup of $G$, together with this proposition $|H N| = |H| dot |N| \/|H inter.sq N| $(*citation*), we could get:
  $|N : H inter.sq N|
    = |N| \/ |H ∩ N|
    = |H N| \/ |H|
    = |H N : H|$. 
By decompositing the index of $H$ in $G$, we could get: $|G : H| = |G : H N| dot|H N : H|$, so $|H N : H| ∣ |G : H|$. 

Now together with $|H inter.sq N| ∣ |H|$, we have:
  $|N : H inter.sq N| ∣ |G : H|$.
Since $|H|$ and $[G : H]$ is coprime(recall that $H$ is  Hall subgroup), then $|H inter.sq N|, |N : H inter.sq N|$ is also coprime.
 
#theorem[Hall Subgroups][If $H$ is a Hall subgroup of $G$ and $N$ is the normal subgroup of $G$, then  $H N \/ N$ is a Hall subgroup of $G \/ N$.]

Like it in the proof of the first theorem, we use
  $|H N| = |H| dot |N|\/ |H inter.sq N|$, dividing it by $|N|$ yields
$|H N\/N| = |H|\/|H inter.sq N|$.

Since $H ∩ N ≤ H$, Lagrange’s theorem gives $|H ∩ N| ∣ |H|$, 
so in particular
$|(H N)\/N| ∣ |H|$.

On the other hand,
$|G\/N : (H N)\/N| = |G : H N|$.

Because $H ≤ H N ≤ G$, multiplicativity of indices implies
$|G : H| = |G : H N| dot |H N : H|$, 
hence $|G : H N| ∣ |G : H|$, and therefore
$|G\/N : (H N)\/N| ∣ |G : H|$.

Let $d = gcd(|(H N)\/N|, |G\/N : (H N)\/N|)$. Then $d ∣ |H|$ and $d ∣ |G : H|$, so $d ∣ gcd(|H|, |G : H|) = 1$, since $H$ is Hall in $G$. Thus $d = 1$, and the result follows. 

- TODO: 这个paper proof的总结，到时候再回来写。需要强调的其实是那个proposition。比较Meta地讲讲这到底是怎样一个proposition。

== API landscape (3.5 Pages)
=== Motivation 
Compared to the abelian simple case, the Hall formalization requires a richer coordination of APIs. The two theorems express coprimality properties that simultaneously involve subgroup cardinalities and subgroup indices, both of which are represented in `Nat`. While cardinality is straightforward to handle via `Nat.card` for finite types equipped with `Fintype` instance, the treatment of index is more delicate, as it interacts with multiple levels of subgroup structure. 

In pen-and-paper style mathematics, a subgroup can be viewed simultaneously as a subgroup of several groups without ambiguity. In Lean however, every term carries a specific type. For instance, $H inter.sq N$ may be represented as a term of type `Subgroup G` or `Subgroup N`. Although mathematically equivalent, these are distinct at the type level and Lean treats them differently. Consequently, the choice of ambient group must be fixed during the formalization process.

The choice depends on how well existing APIs compose through coercions and whether additional bridging lemmas are required. If a lemma expects $H inter.sq N$ to inhabit in `Subgroup G` but represented in `Subgroup N`, when coercions do not adequately bridge these representations, additional lemmas are often required to connect them explicitly. Thus, the complexity of the Hall formalization stems not only from the mathematical content, but from the necessity of aligning type-level representations with the available API infrastructure.

The following subsections analyze the APIs that are required to support this coordination.
=== Representation of index
In mathematics, there're three equivalent perspectives to understand index: 
- the number of left cosets: $|G : H| = |{g dot H|g in G}|$. 
- if H is normal subgroup of $G$, the cardinality of quotient group $|G : H| = |G \/ H|$.
- if G is a finite group, the divide of cardinality (according to Lagrange theorem): $|G:H| = |G| \/ |H|$
In mathlib, the standard definition of index is:
```lean
noncomputable def index : ℕ := Nat.card (G ⧸ H)
```If $H$ is a subgroup of $G$, its index in $G$ is expressed as `H.index`. This definition reflects the quotient-type perspective, while the classical interpretations such as coset counting and cardinality ratio are recovered through lemmas like Lagrange theorem rather than separate definitions. During the formalization, however, we may rewrite the index into different equivalent forms depending on the context. Certain lemmas are phrased in terms of quotient types, others in terms of cardinality relations, and switching between these forms is often guided by convenience.

Moreover, when working with nested subgroups, such as $H inter.sq K <= K <= G$, we require the index of one subgroup relative to another. For this purpose, mathlib provides the function `relIndex`:

```lean noncomputable def relIndex : ℕ := (H.subgroupOf K).index```

This expresses the index of a subgroup relative to a larger subgroup within the same ambient group. For instance, in our first Hall Subgroup theorem the $|N : H inter.sq N| $ could be written as `H.relIndex N`. 
=== Subgroup API and lattice structure
- lattice结构，为什么可以直接写 meet /join, 是因为有一个API的存在, 而且因为normal subgroup
- 几种不同的表示 H ⊓ N is a subgroup of N 的方法（参考代码）
  - comap and relIndex, 为什么最后我选择了relIndex, 可以直接在这里进行解释
=== The first and second isomorphism
- first isomorphism theorem 和second isomorphism在Lean里面的形态(调查它是因为这个exercise出现在了textbook的这一个章节，这是这两个proof得以证明的关键hints)
=== Quotient Group
- QuotientGroup.mk 来表示quotient
=== Theorem statement
- 最后展示theorem statement，并且讲明白coercion在这里的重要作用，以及ambient group的重要作用。主要是那个小箭头，为什么是必不可少的。
== Choice of proof strategy (4 Pages)
=== theorem 1
- theorem 1: 结构先行，rewrite 消去。重点解释为什么教材的方法行不通，因为在Set上进行计数
=== theorem 2
- theorem 2: 利用Nat.congr, 拿到结构。重点解释为什么quotient反而让形式化变得简单，而不用来处理像前面那么多的结构问题（可能是因为quotient把结构给商掉了？）
== Summarization (0.5 Page)
- 数学层面
counting和同构。计数信息可以从同构得来(theorem 1). 为了证明计数相等，我们可以把问题提升到同构(theorem 2).
- 逻辑层面
- 形式化层面

#pagebreak()

 