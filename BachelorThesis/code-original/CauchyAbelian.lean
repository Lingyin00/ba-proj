import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Defs

/-! In mathlib there already exists a general version of `Cauchy's theorem`,
    which is proved by using properties of orbit decomposition.
    Here we show a special case that if a group is also abelian,
    then the proof of Cauchy's theorem could be made by induction.-/

/-! *Proposition 21* from Chapter 3 in _Dummit&Forte_ :
    If G is a finite abelian group and p is a prime dividing |G|,
    then G contains an element of order p. -/
theorem exists_orderOf_eq_prime_of_dvd_card {G : Type*} {p : Nat} [Fintype G] [CommGroup G]
    (hp1 : Nat.Prime p) (hp2 : p ∣ Nat.card G) : ∃ x : G, orderOf x = p := by
  sorry
