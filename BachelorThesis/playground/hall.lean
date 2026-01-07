import Mathlib.GroupTheory.Index
/- `Summary`:
  1. this proof is done on paper by:
    firstly showing the connection of |HN| and |H|, |N|
  2. see the conncetion to the second Isomphorphic theorem
  3. transfer the co-prime property
  However in Lean it is better proved using backward reasoning. Otherwise when introducing the
  first lemma, the cardinality of HN(the union of unique left cosets) is problematic, since
  left coset is defined on set, counting on set arouses non-trival type problems for later proof.
-/
set_option trace.Meta.synthInstance true
open scoped Pointwise
/-*This file contains the scratch during the proof of HallSubgroup.lean*-/
#check Subgroup.subtype
#check Subgroup.index_eq_card
#check Subgroup.card_mul_index
--#check relIndex
#check Subgroup.card_eq_card_quotient_mul_card_subgroup --Lagrange's theorem

variable {G : Type*} [Group G] [Fintype G]

/- *Counting on set might overcomplicate the Lean proof, paper must be adjusted with mathlib*-/
lemma order_union_of_left_cosets (H : Subgroup G) (N : Subgroup G) :
    Nat.card (⋃ h : H, h • N : Set G) =
    (Nat.card H * Nat.card N) / Nat.card ((H ∩ N : Set G)) := by
  sorry
/- *vs. computation on structure*-/
lemma snd_iso_index (H N : Subgroup G) (hLE : H ≤ N.normalizer) :
    Nat.card (↥H ⧸ N.subgroupOf H) = Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by
  sorry

/-*using the mathlib definition if my method cannot work* -/
theorem inter_of_hallSub_normal_is_Hall_one (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  sorry

-- /- **?** this trival result shoud be added in mathlib? or is it already exist -/
-- lemma index_eq_of_mul_eq_mul  {n : ℕ} (H : Subgroup G)
--     (h : Nat.card (G ⧸ H) * Nat.card H = Nat.card H * n) : H.index = n := by
--   have hn : Nat.card (G ⧸ H) = n := by
--     sorry
--   simpa [Subgroup.index, Nat.card_eq_fintype_card] using hn


/- *!attention: wrong definition!!!*-/
--   have hH : (Nat.card H : ℕ) ∣  Nat.card G := by exact Subgroup.card_subgroup_dvd_card H
--   obtain ⟨n, hn⟩ := hH
--   have : H.index = n := by
--   surprised.shouldn't it just result followed from lagrange theorem and the definition of index?
--     rw[Subgroup.card_eq_card_quotient_mul_card_subgroup H] at hn --using the Lagrange's theorem
--     exact index_eq_of_mul_eq_mul H hn
--   have hpn: n.Coprime (Nat.card ↥H) := by simpa [this] using hH
--   -- clue: focusing the divisibility and prime translation in equations
--   sorry

#check Subgroup.subgroupOf
/- *Note the equation*  `subgroupOf K = Subgroup.comap K.subtype H`-/

@[to_additive]
theorem mem_zpowers_zpow_iff {g : G} {k : ℤ} :
    g ∈ Subgroup.zpowers (g ^ k) ↔ k.gcd (orderOf g) = 1 := by
  simp_rw [← Nat.dvd_one, Int.gcd_dvd_iff, Nat.cast_one, ← Int.sub_eq_iff_eq_add', ← dvd_def,
    ← Int.modEq_iff_dvd, ← zpow_eq_zpow_iff_modEq, zpow_one, zpow_mul, ← mem_zpowers_iff]
  -- apply Iff.intro
  -- · intro hgk
  --   rcases (Subgroup.mem_zpowers_iff.mp hgk) with ⟨m, hm⟩
  --   have hm' : g ^ (k * m) = g := by simpa [zpow_mul] using hm
  --   have h1 : g ^ (k * m - 1) = 1 := by simp[zpow_sub, hm']
  --   have hdiv : (↑(orderOf g) : ℤ) ∣ (k * m - 1) := orderOf_dvd_iff_zpow_eq_one.mpr h1
  --   rcases hdiv with ⟨t, ht⟩
  --   let d : ℤ := k.gcd (↑(orderOf g) : ℤ)
  --   have dk : d ∣ k := Int.gcd_dvd_left k (↑(orderOf g) : ℤ)
  --   have dn : d ∣ (↑(orderOf g) : ℤ) := Int.gcd_dvd_right k (↑(orderOf g) : ℤ)
  --   have dkm : d ∣ k * m := dk.mul_right m
  --   have dnt : d ∣ (↑(orderOf g) : ℤ) * t := dn.mul_right t
  --   have hlin : k * m - (↑(orderOf g) : ℤ) * t = 1 := by omega
  --   have d1 : d ∣ 1 := by
  --     have : d ∣ k * m - (↑(orderOf g) : ℤ) * t := Int.dvd_sub dkm dnt
  --     simpa [hlin] using this
  --   have hd1: d = 1 := by
  --     have habs : (Int.natAbs d : ℕ) ∣ 1 := by
  --       rcases d1 with ⟨c, hc⟩
  --       refine ⟨Int.natAbs c, ?_⟩
  --       have := congrArg Int.natAbs hc
  --       simpa [Int.natAbs_mul] using this
  --     have habs1 : Int.natAbs d = 1 := Nat.dvd_one.mp habs
  --     have hdpm : d = 1 ∨ d = -1 := by omega
  --     cases hdpm with
  --     | inl h => exact h
  --     | inr h =>
  --       exfalso
  --       have : (0 : ℤ) ≤ -1 := by simp_all only [Int.reduceNeg, IsUnit.neg_iff, isUnit_one,
  --         IsUnit.dvd, Int.natAbs_of_isUnit,reduceCtorEq]
  --       omega
  --   simpa [d] using hd1
  -- · intro kgcd
  --   by_cases h : orderOf g = 0
  --   · rw [h] at kgcd
  --     simp only [CharP.cast_eq_zero, Int.gcd_zero] at kgcd
  --     have hk : k = 1 ∨ k = -1 := Int.natAbs_eq_natAbs_iff.mp kgcd
  --     cases hk <;> simp_all
  --   · let n : ℤ := (↑(orderOf g) : ℤ)
  --     have hbez :
  --         (k.gcd n : ℤ) = k * Int.gcdA k n + n * Int.gcdB k n :=
  --       Int.gcd_eq_gcd_ab k n
  --     have hab1 : k * Int.gcdA k n + n * Int.gcdB k n = 1 := by
  --       have : k.gcd n = 1 := by exact kgcd
  --       simpa [this] using hbez.symm
  --     let a : ℤ := Int.gcdA k n
  --     let b : ℤ := Int.gcdB k n
  --     have hab1' : a * k + b * n = 1 := by
  --       simpa [a, b, n, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
  --     have hn : g ^ n = 1 := by simp only [zpow_natCast, pow_orderOf_eq_one, n]
  --     refine ⟨a, ?_⟩
  --     calc
  --       (g ^ k) ^ a = g ^ (k * a) := by simpa using (zpow_mul g k a).symm
  --       _   = g ^ (a * k) * 1:= by simp [mul_comm]
  --       _   = g ^ (a * k) * g ^ (b * n) := by
  --         have : g ^ (b * n) = 1 := by
  --           calc
  --             g ^ (b * n) = g ^ (n * b) := by simp [mul_comm]
  --             _ = (g ^ n) ^ b := by simpa using (zpow_mul g n b)
  --             _ = 1 := by simp [hn]
  --         simp [this]
  --       _   = g ^ (a * k + b * n) := by simp [zpow_add]
  --       _   = g := by simp [hab1']
