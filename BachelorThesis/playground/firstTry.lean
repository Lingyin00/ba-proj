import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.Subgroup.Center

namespace one
variable (G H : Type*)
variable [Group G] [Group H]
variable (E F: Subgroup H)
variable (φ : G →* H)

#check E.comap φ

#check Subgroup.comap
/-!
  Exercise 3.1.1
  lemma: The preimage of a subgroup under a homomorphism is a subgroup
  Theorem 1: the preimage of a normal subgrooup under a homomorphism is a normal subgroup
  Theorem 2: The kernel of a homomorphismus is a normal subgroup
-/
lemma preImage_subGroup_of_subGroup (g : G) : g ∈ E.comap φ ↔ φ g ∈ E  := by exact
  Subgroup.mem_comap
-- The definition of comap in lean already uses the proof which φ(x)φ(y⁻¹) = φ(x)φ⁻¹(y) = φ(xy⁻¹) (rule of subgroup)

#check Subgroup.Normal.comap
#check F.comap φ
theorem preImage_normalSubgroup (h : F.Normal) : (F.comap φ).Normal := h.comap φ
-- Type class stuck bug: because of variable name mismatch
-- simpa using Subgroup.Normal.comap (N := H) (f := φ) h
-- Subgroup.Normal.comap (G := G) (N := H) (H := F) (f := φ) h


#check φ.ker
theorem kernel_of_normalSubgroup : φ.ker.Normal := by exact MonoidHom.normal_ker φ
end one

open Pointwise
open Function MulOpposite Set
--open scoped Pointwise
namespace lagrange
/-!
  Lagrange's Theorem:
  if G is a finite group, H is its subgroup
  then `|H| ∣ |G| ` and the number of left cosets of H in G equals `|G| / |H|`
-/
variable (G : Type*)
variable [Group G] [Fintype G] [Fintype (Set G)]
variable (a : G)
variable (H : Subgroup G) [Fintype H]
variable (s : Set G)
#check Fintype.card H -- ℕ
#check Fintype.card G
#check 3 ∣ 4
#check a • (H : Set G)
#check (Fintype.card H ) ∣ (Fintype.card G) -- Note: have to write it as `\|`, not `|`
theorem lagrange_divide : Fintype.card H ∣ Fintype.card G := by sorry
-- this is proved in file Mathlib.GroupTheory.Coset.Card
noncomputable instance : Fintype (a • (H : Set G) : Set G) := by (expose_names; apply Fintype.ofFinite )
theorem lagrange_coset : Fintype.card G / Fintype.card H = Fintype.card (a • (H ) : Set G) := by sorry

end lagrange

namespace centerG
/-!
  Exercise 3.2.4
  if |G| = pq (p,q are some primes),
  then either G is abelian or Z(G) = 1
-/

variable (G : Type*)
variable [Group G] [Finite G]
variable (p q : ℕ)
#check CommGroup G
#check Prime p
#check Subgroup.center G

def IsAbelianG [Group G] (a : G) (b : G) := a * b = b * a
theorem abelianOrCenterOne (hp : Prime p) (hq : Prime q) (hG : Nat.card G = p*q) (a b : G):
    IsAbelianG G a b ∨ Subgroup.center G = (⊥ : Subgroup G) := sorry

end centerG
