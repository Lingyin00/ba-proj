import Mathlib.GroupTheory.Index
import Init.Data.Nat.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
--set_option trace.Meta.synthInstance true
/-!
Exercise 3.3.10 `Hall Subgroup`
-- A subgroup H of a finite group G is called a Hall Subgroup of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/

variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (N : Subgroup G) [N.Normal]

/-! The definition of Hall Group-/
abbrev IsHallSubgroup (H : Subgroup G) : Prop := Nat.Coprime H.index (Nat.card H)

/-! The definition that H ⊓ N is a subgroup of N-/
abbrev inter_of_subHN (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup N :=
  (H ⊓ N).comap N.subtype -- this might be unnecessary by using relIndex from the mathlib def.
#check H.relIndex N

/-! The definition that H ⊔ N is a subgroup of G-/
abbrev HN (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup G := H ⊔ N

#check QuotientGroup.quotientInfEquivProdNormalizerQuotient
#check Subgroup.subgroupOf
#check Nat.card_eq_of_bijective
lemma snd_iso_index (H N : Subgroup G) (hLE : H ≤ N.normalizer) :
    Nat.card (↥H ⧸ N.subgroupOf H) = Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by
  sorry -- Next I need to clarify the right ambient type on each level

/-! Prove that H ⊓ N is a Hall Subgroup of N-/
theorem inter_of_hallSub_normal_is_Hall_new (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  have hgcd :
      Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.gcd H.index (Nat.card H) := by
    have h1 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ H.index := by
      have : H.relIndex N ∣ H.index := by
        have hIndex : H.index = (H ⊔ N).index * H.relIndex N := by
          have card_G_one : Nat.card G = H.index * Nat.card H := by
            exact Eq.symm (Subgroup.index_mul_card H)
          have card_G_two : Nat.card G = (H ⊔ N).index * Nat.card (H ⊔ N : Subgroup G):= by
            exact Eq.symm (Subgroup.index_mul_card (H ⊔ N))
          -- H, HN, N index decomposition
          have h_index : Nat.card H =
              Nat.card (↥H ⧸ N.subgroupOf H) * Nat.card (N.subgroupOf H) := by
            apply Subgroup.card_eq_card_quotient_mul_card_subgroup
          have hn_index_in_HN : Nat.card (H ⊔ N : Subgroup G) =
              Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card (N.subgroupOf (H ⊔ N)) := by
            exact Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
          have hN : Nat.card (N.subgroupOf (H ⊔ N)) = Nat.card N := by
            sorry -- the cardinality of N shouldn't change, when the ambient type changes
          have hn_index : Nat.card (H ⊔ N : Subgroup G) =
              Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card N := by
            rw [hN] at hn_index_in_HN
            assumption
          have n_index : Nat.card N =
              H.relIndex N * Nat.card (H.subgroupOf N) := by
            apply Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf N)
          rw [h_index] at card_G_one
          rw [card_G_one, hn_index, n_index] at card_G_two
          -- *using the 2.Isomorphism theorem Index Version*
          rw [snd_iso_index] at card_G_two
          · have : Nat.card ↥(N.subgroupOf H) = Nat.card ↥(H.subgroupOf N) := by
              sorry --the same idea as above
            rw [← this] at card_G_two
            simp [mul_comm] at card_G_two
            have neq01 : Nat.card ↥(N.subgroupOf H) ≠ 0 := by
              simpa [Nat.card_eq_fintype_card] using (by sorry) -- this follows from [Fintype G]
            have neq02 : Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) ≠ 0 := by
              simpa [Nat.card_eq_fintype_card] using (by sorry)
            have hq :
                H.index * (Nat.card ↥(N.subgroupOf H) *
                Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N))) =
                ((H ⊔ N).index * H.relIndex N) * (Nat.card ↥(N.subgroupOf H) *
                Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N))) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using card_G_two
            simp_all only [Nat.card_eq_fintype_card, ne_eq, mul_eq_mul_right_iff, mul_eq_zero,
              or_self, or_false]
          · exact Subgroup.le_normalizer_of_normal
        exact Dvd.intro_left (H ⊔ N).index (id (Eq.symm hIndex))
      have h : (H.relIndex N).gcd (Nat.card ↥(H ⊓ N)) ∣ H.relIndex N :=
        Nat.gcd_dvd_left _ _
      exact Nat.dvd_trans h this
    have h2 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.card H := by
      have hLag : Nat.card (H ⊓ N : Subgroup G) ∣ Nat.card H := by
        apply Subgroup.card_dvd_of_le
        exact inf_le_left
      have hgcd :
          Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G))∣ Nat.card (H ⊓ N : Subgroup G) :=
        Nat.gcd_dvd_right _ _
      exact Nat.dvd_trans hgcd hLag
    exact Nat.dvd_gcd h1 h2
  have : Nat.gcd H.index (Nat.card H) = 1 := Nat.coprime_iff_gcd_eq_one.mp hH
  have : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) = 1 := by
    exact Nat.dvd_one.mp (by simpa [this] using hgcd)
  exact this

/-! The definition that HN ⧸ N is a subgroup of G ⧸ N-/
def HNmodNisSubgroup (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup (G ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

/-! Prove that HN ⧸ N is a Hall subgroup of G ⧸ N-/
theorem CosetsOfQuotientGrpIsHall (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (HNmodNisSubgroup H N).index (Nat.card ((HNmodNisSubgroup H N))) := by
  sorry
