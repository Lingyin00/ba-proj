import Mathlib.GroupTheory.Index
import Init.Data.Nat.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
noncomputable section
--set_option trace.Meta.synthInstance true
/-!
Exercise 3.3.10 `Hall Subgroup`
-- A subgroup H of a finite group G is called a Hall Subgroup of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/

--variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (N : Subgroup G) [N.Normal]

/-! The definition of Hall Group-/
abbrev IsHallSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  Nat.Coprime H.index (Nat.card H)

/-! The definition that H ⊓ N is a subgroup of N-/
abbrev inter_of_subHN {G : Type*} [Group G]
  (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup N :=
  (H ⊓ N).comap N.subtype -- this might be unnecessary by using relIndex from the mathlib def.

/-! The definition that H ⊔ N is a subgroup of G-/
abbrev HN {G : Type*} [Group G] (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup G := H ⊔ N

#check QuotientGroup.quotientInfEquivProdNormalizerQuotient
#check Subgroup.subgroupOf
#check Nat.card_eq_of_bijective

-- **Second isomorphism theorem (cardinality version)**
theorem snd_iso_card {G : Type*} [Group G] [Fintype G] (H N : Subgroup G) (hLE : H ≤ N.normalizer) :
    Nat.card (H ⧸ N.subgroupOf H) = Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by
  letI := Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := N) hLE
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := H) (N := N) hLE
  simpa using
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient (H := H ) (N := N) hLE).toEquiv

theorem snd_iso_card_normalizer {G : Type*} [Group G] [Fintype G] (H N : Subgroup G) [N.Normal] :
    Nat.card (H ⧸ N.subgroupOf H) = Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) :=
  snd_iso_card H N Subgroup.le_normalizer_of_normal

theorem index_eq_index_sup_mul_relIndex_of_normal {G : Type*} [Group G] [Fintype G]
    (H N : Subgroup G) [N.Normal] :
    H.index = (H ⊔ N).index * H.relIndex N := by
  have card_G_two : Nat.card G = (H ⊔ N).index * Nat.card (H ⊔ N : Subgroup G):=
    (Subgroup.index_mul_card (H ⊔ N)).symm
  have h_index : Nat.card H = Nat.card (↥H ⧸ N.subgroupOf H) * Nat.card (N.subgroupOf H) := by
    apply Subgroup.card_eq_card_quotient_mul_card_subgroup
  have hn_index_in_HN : Nat.card (H ⊔ N : Subgroup G) =
      Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card (N.subgroupOf (H ⊔ N)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have hN : Nat.card (N.subgroupOf (H ⊔ N)) = Nat.card N := by
    have hle : N ≤ H ⊔ N := le_sup_right
    simpa using Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hn_index : Nat.card (H ⊔ N : Subgroup G) =
    Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card N := by
    simpa [hN] using hn_index_in_HN
  have n_index : Nat.card N = H.relIndex N * Nat.card (H.subgroupOf N) := by
    apply Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf N)
  rw [← (Subgroup.index_mul_card H), h_index, hn_index, n_index,
    snd_iso_card_normalizer] at card_G_two
  set A : Nat := Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N))
  set B : Nat := Nat.card ↥(N.subgroupOf H)
  have hInter :
      Nat.card { x : ↥N // x ∈ H.subgroupOf N } = Nat.card { x : ↥H // x ∈ N.subgroupOf H } := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
        invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl }
  have card_G_two' := card_G_two
  rw [hInter] at card_G_two'
  have hq : H.index * (B * A) = ((H ⊔ N).index * H.relIndex N) * (B * A) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using card_G_two'
  have hne : B * A ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt (by exact Nat.card_pos)) (Nat.ne_of_gt (by exact Nat.card_pos))
  exact (Nat.mul_left_inj hne).mp hq


/-! Prove that H ⊓ N is a Hall Subgroup of N-/
theorem hall_inter_of_normal_is_hall {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  have hgcd :
      Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.gcd H.index (Nat.card H) := by
    have h1 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ H.index := by
      have : H.relIndex N ∣ H.index := by
        have hIndex : H.index = (H ⊔ N).index * H.relIndex N := by
          exact index_eq_index_sup_mul_relIndex_of_normal H N
        exact Dvd.intro_left (H ⊔ N).index (id (Eq.symm hIndex))
      have h : (H.relIndex N).gcd (Nat.card ↥(H ⊓ N)) ∣ H.relIndex N :=
        Nat.gcd_dvd_left _ _
      exact Nat.dvd_trans h this
    have h2 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.card H := by
      have hLag : Nat.card (H ⊓ N : Subgroup G) ∣ Nat.card H := by
        apply Subgroup.card_dvd_of_le inf_le_left
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
def HNmodNisSubgroup {G : Type*} [Group G]
    (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup (G ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

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
      (↥(H ⊔ N) ⧸ f.ker) ≃* ↥f.range := QuotientGroup.quotientKerEquivRange f
  have hQuot :
      (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) ≃* (↥(H ⊔ N) ⧸ f.ker) :=
    QuotientGroup.quotientMulEquivOfEq (G := ↥(H ⊔ N)) (M := N.subgroupOf (H ⊔ N)) (N := f.ker)
      hker.symm
  have hRange : ↥f.range ≃* ↥((H ⊔ N).map (QuotientGroup.mk' N)) := by
    rw [hrange]
  exact (hQuot.trans hIso).trans hRange |>.toEquiv


lemma card_supQuotient_eq_card_map2
  {G : Type*} [Group G] [Fintype G]
  (H N : Subgroup G) [N.Normal] :
  Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) = Nat.card ((H ⊔ N).map (QuotientGroup.mk' N)) := by
  apply Nat.card_congr
  let f : ↥(H ⊔ N) →* (G ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.subtype (H ⊔ N))
  have hker : f.ker = N.subgroupOf (H ⊔ N) := by aesop
  have hrange : f.range = (H ⊔ N).map (QuotientGroup.mk' N) := by aesop
  -- **Question: cannot rw directly because of dependent motive??**
  -- using **the first isomorphism theorem**
  have h1 : (↥(H ⊔ N) ⧸ f.ker) ≃* ↥f.range := QuotientGroup.quotientKerEquivRange f
  have eQuot : (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) ≃* (↥(H ⊔ N) ⧸ f.ker) := by
  -- using **isomorphism theorem**
    simpa using (QuotientGroup.quotientMulEquivOfEq (G := ↥(H ⊔ N))
      (M := N.subgroupOf (H ⊔ N)) (N := f.ker) hker.symm)
  have e₁ : (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) ≃* ↥f.range :=
    ((id h1.symm).trans (id eQuot.symm)).symm
  have eRange : ↥f.range ≃* ↥((H ⊔ N).map (QuotientGroup.mk' N)) := by rw [hrange]
  have eMul :
    (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) ≃* ↥((H ⊔ N).map (QuotientGroup.mk' N)) :=
    e₁.trans eRange
  exact eMul.toEquiv

/-! Prove that HN ⧸ N is a Hall subgroup of G ⧸ N-/
theorem CosetsOfQuotientGrpIsHall {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime ((H ⊔ N).map (QuotientGroup.mk' N)).index
      (Nat.card ((H ⊔ N).map (QuotientGroup.mk' N))) := by
  -- Goal 1: to prove |G ⧸ N : HN ⧸ N| ∣  |G ∣ N|:
  have I : ((H ⊔ N).map (QuotientGroup.mk' N)).index = (H ⊔ N).index := by
    let f : G →* (G ⧸ N) := QuotientGroup.mk' N
    have hsurj : Function.Surjective f := by simpa [f] using (QuotientGroup.mk'_surjective N)
    have hker_le : f.ker ≤ H ⊔ N := by simp [f]
    simpa [f] using (Subgroup.index_map_eq (H := H ⊔ N) hsurj hker_le)
  have thisI : ((H ⊔ N).map (QuotientGroup.mk' N)).index ∣ H.index := by
    simpa [I] using (Subgroup.index_dvd_of_le (le_sup_left : H ≤ H ⊔ N))
  -- Goal 2: to prove |HN ⧸ N| ∣ |H|
  have thisII : Nat.card ((H ⊔ N).map (QuotientGroup.mk' N)) ∣ Nat.card H := by
    have hcard : Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N))
        = Nat.card ((H ⊔ N).map (QuotientGroup.mk' N)) :=
      card_supQuotient_eq_card_map (H := H) (N := N)
    have hdiv : Nat.card (H ⧸ N.subgroupOf H) ∣ Nat.card H := by -- Lagrange theorem
      exact Subgroup.card_quotient_dvd_card (α := H) (s := (N.subgroupOf H))
    have hsnd := snd_iso_card_normalizer (H := H) (N := N)
    simp_all only [Subgroup.mem_map, QuotientGroup.mk'_apply]
  exact Nat.Coprime.of_dvd thisI thisII hH
