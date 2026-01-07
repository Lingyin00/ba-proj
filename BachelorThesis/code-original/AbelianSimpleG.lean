import Mathlib.GroupTheory.SpecificGroups.Cyclic

noncomputable section -- on the Prop level
--set_option trace.Meta.synthInstance true
/-!
Exercise 3.4.1 `Abelian Simple Group`
-- Prove that if G is an abelian simple group then G ≃* Zₚ for some prime p
-/
variable {G : Type*} [CommGroup G] [IsSimpleGroup G]

-- **?this small lemma might be a PR to mathlib?**
omit [IsSimpleGroup G] in
@[simp]
lemma finiteCyclic_iff_finiteCarrier (g : G) :
    Finite (Subgroup.zpowers g) = ((Subgroup.zpowers g) : Set G).Finite := by
  rfl

/-! Using g to build a finite cyclic group-/
omit [IsSimpleGroup G] in
lemma finite_finOrder_zpow (g : G) (hp : ¬orderOf g = 0) :
    Finite (Subgroup.zpowers g) := by
  simp_all only [orderOf_eq_zero_iff, not_not, finiteCyclic_iff_finiteCarrier, finite_zpowers]

#check isOfFinOrder_iff_pow_eq_one
#check isOfFinOrder_iff_zpow_eq_one

/-! Finitness of an abelian simple group -/
lemma finite_abelianSimple : Finite G := by
  obtain ⟨g, hg⟩ := -- G is cyclic
    (isCyclic_iff_exists_zpowers_eq_top : IsCyclic G ↔ _).mp (by infer_instance)
  by_contra hnf

  -- using zpowers g and Infinite G to get that orderOg g is 0
  have horder : orderOf g = 0 := by
    by_contra h0
    have hfin : Finite (Subgroup.zpowers g) := by exact finite_finOrder_zpow g h0
    haveI : Finite ((⊤ : Subgroup G)) := by simpa [hg] using hfin
    -- transfer the Finiteness through surjection into G，to get contradiction
    have hfinG : Finite G :=
      Finite.of_surjective (Subtype.val : (⊤ : Subgroup G) → G)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    exact hnf hfinG
  let H : Subgroup G := Subgroup.zpowers (g ^ 2)
  have Hnorm : H.Normal := by exact Subgroup.normal_of_comm H
  have hneq_Top : H ≠ ⊤ := by
    intro htop
    have h3 : g ^ 3 ∈ Subgroup.zpowers g := by exact Subgroup.npow_mem_zpowers g 3
    have hn3 : g ^ 3 ∉ H := by
      by_contra hn
      change ∃ z : ℤ  , (g ^ 2) ^ z = g ^ 3 at hn
      rcases hn with ⟨z, hz⟩
      have hz₁ : (g ^ (2 : ℤ)) ^ z = g ^ (3 : ℤ) := by simpa [zpow_ofNat] using hz
      have hz₂ : g ^ (2 * z : ℤ) = g ^ (3 : ℤ) := by simpa [zpow_mul] using hz₁
      have h1 : g ^ (2 * z - 3 : ℤ) = 1 := by
        have := congrArg (fun x => x * g ^ (-3 : ℤ)) hz₂
        simpa [sub_eq_add_neg, zpow_add] using this
      have hne0 : (2 * z - 3 : ℤ) ≠ 0 := by omega
      by_cases hg1 : g = 1
      · simp_all only [Subgroup.zpowers_one_eq_bot, bot_ne_top]
      · have : ¬ IsOfFinOrder g := by apply orderOf_eq_zero_iff.mp horder
        have finOrder_g : IsOfFinOrder g := by
          refine (isOfFinOrder_iff_zpow_eq_one).mpr ?_
          exact ⟨2 * z - 3, hne0, h1⟩
        exact this finOrder_g
    simp_all only [not_finite_iff_infinite, orderOf_eq_zero_iff, Subgroup.mem_top,
      not_true_eq_false]
  have hneq_bot : H ≠ ⊥ := by
    intro hbot
    have : Nat.card H = 1 := (Subgroup.eq_bot_iff_card H).mp hbot
    have ne : g ^ 2 ≠ (1 : G) := by
      by_contra he
      have hh : orderOf g = 2 := by
        refine orderOf_eq_prime_iff.mpr ?_
        constructor
        · assumption
        · intro hg1
          have ho1 : orderOf g = 1 := by simp [hg1]
          have : (0 : ℕ) = 1 := by rw [← horder]; exact ho1
          exact Nat.zero_ne_one this
      have h02 : (0 : ℕ) = 2 := by rw [← horder]; exact hh
      exact (by decide : (0 : ℕ) ≠ 2) h02
    have hmemg2 : g ^ 2 ∈ H := by
      refine (Subgroup.mem_zpowers_iff).mpr ?_
      exact ⟨1 , by simp⟩
    rw [hbot] at hmemg2
    exact ne hmemg2
  have := IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := H) Hnorm
  rcases this <;> contradiction

/-！Main theorem : if G is an abelian simple group then G ≃* Zₚ for some prime p. -/
theorem abelianSimpleG_isoOfZMod_prime :
    ∃ p : ℕ , (Nat.Prime p) ∧ Nonempty (Additive G ≃+ ZMod p) := by
  have hcyc : IsCyclic G := by infer_instance -- a simple abelian group is cyclic
  rcases (isCyclic_iff_exists_zpowers_eq_top.mp hcyc) with ⟨g, hg⟩ -- get the generator
  let p : ℕ := orderOf g -- get the order of g, not assuming g ≠ 0 here
  have orderG : Nat.card G = p := by exact Eq.symm (orderOf_eq_card_of_zpowers_eq_top hg)
  have FinG : Finite G := by exact finite_abelianSimple
  -- using the mathlib theorem about prime_card
  have hp : Nat.Prime p := by rw [← orderG]; apply IsSimpleGroup.prime_card
  use p
  constructor
  · assumption
  · refine Nonempty.intro ?_
    rw [← orderG]
    have e : ZMod (Nat.card G) ≃+ Additive G := by
      simpa using zmodAddCyclicAddEquiv (G := Additive G) (by infer_instance)
    exact e.symm

example : Nat.Prime (Nat.card G) := by
  letI := finite_abelianSimple (G := G)
  apply IsSimpleGroup.prime_card

/-**?** mathlib assumes finite as premises, but actually it is not necessary-/
lemma fintype_abelianSimpleG : Nonempty (Fintype G) := by
  refine (finite_iff_nonempty_fintype G).mp ?_
  exact finite_abelianSimple
