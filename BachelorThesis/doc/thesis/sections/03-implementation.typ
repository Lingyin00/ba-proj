= Main Part I: Implementation

== Formalization insight

===  Integer vs. Natural Number

Although the distinction between natural and integer exponents is often glossed over on paper, it becomes unavoidable in a proof assistant, where subgroup generation must explicitly account for inverses.

This provides a small but concrete example of how formalization reveals implicit assumptions in informal mathematics.

```lean
@[to_additive]
theorem mem_zpowers_pow_iff {g : α} {k : ℕ} :
    g ∈ Subgroup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1 := by
  sorry

@[to_additive]
theorem mem_zpowers_pow_iff {g : G} {k : ℤ} :
    g ∈ Subgroup.zpowers (g ^ k) ↔ k.gcd (↑(orderOf g) : ℤ) = 1 := by 
  sorry
```
- It reveals the fact of the genenration of a subgroup: both side instead of one side
- In math we don't explicitly clarify whether $k$ in $g ^ k$ an integer or a natural number
- Formalization forces an explicit choice of index types, revealing implicit assumptions in informal mathematics.
