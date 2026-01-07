// Get Polylux from the official package repository
#import "@preview/polylux:0.4.0": *

// Make the paper dimensions fit for a presentation and the text larger
#set page(paper: "presentation-16-9")
#set text(size: 23pt, font: "Lato")
#show raw.where(block: true): set text(0.8em / 1.3)
#show raw.where(lang: "lean"): r => {
  show "theorem": set text(purple)
  show "sorry": set text(red)
  show "lemma": set text(purple)
  show "by": set text(purple)
  show "Type": set text(black)
  show "have": set text(olive)
  show "exact": set text(olive)
  show "simpa": set text(olive)
  show "using": set text(olive)
  r
}
// Use #slide to create a slide and style it using your favourite Typst functions
#slide[
  #set align(horizon)

  = Extending the Group Theory Library in Mathlib
  =

  Lingyin Luo

  Dec.04.2025
]

#slide[
  == Background
  ==

  - Lean proof assistant and _mathlib_

  - The group theory API in mathlib

  - Mathematical reference: _Dummit & Foote, Abstract Algebra (3rd ed.)_

]

#slide[
  #set align(horizon)

  = Extending the Group Theory Library in Mathlib ?

]

#slide[
  == Plans for this project
  ==

  - Using the exisiting API to formalize theorems as follows:
      - Abelian Simple Group (exercise 3.4.1)
        - forward reasoning
      - Hall Subgroup (exercise 3.3.10)
        - backward reasoning
      - #text(fill: gray)[Cauchy's Theorem for Abelian Group (section 3.4, proposition 21)
        - proof by induction  (if time allows)]

  - Filling the possible gaps and making PRs to mathlib
]

#slide[
  == Formalization $eq.quest$ Translation
  e.g. _Abelian Simple Group is isomorphic to $Z \/ Z_p$_ is a clean argument 

   - Proof based on existing result from mathlib:   
  ```lean
  theorem IsSimpleAddGroup.prime_card {α : Type u_1} [AddCommGroup α]          
      [IsSimpleAddGroup α] [Finite α] : Nat.Prime (Nat.card α) := by
    sorry
  ```
    - Deriving the finiteness from premises, we get a more general version

  ```lean
  lemma finite_abelianSimple : Finite G := by
    sorry

  theorem abelianSimpleG_isoOfZMod_prime : ∃ p : ℕ, 
      (Nat.Prime p) ∧ Nonempty (Additive G ≃+ ZMod p) := by
    sorry
  ```
]

#slide[
  == Formalization $eq.not$ Translation
  Often requiring additional efforts
  - e.g. Hall Subgroup in mathlib is across different types: 
    - union of left cosets : `Set`
    - subgroup: `Subgroup`
    - quotient group: `HasQuotient.Quotient`
    - cardinality, index, coprime: `Nat`
    - lattice operation: `Lattice`
    - homomorphism and isomorphism: `MulEquiv`
  ```lean
  theorem inter_of_hallSub_normal_is_Hall_new (N H : Subgroup G)
      [N.Normal] (hH : Nat.Coprime H.index (Nat.card H)): 
      Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by
    sorry
  
  ```
]

#slide[
  == Formalization $eq.not$ Translation
 
  Thus, the proof strategy must be carefully considered.
  - Instead of following the paper proof which involes counting on set:
  ```lean
  lemma order_union_of_left_cosets (H : Subgroup G) (N : Subgroup G) :
      Nat.card (⋃ h : H, h • N : Set G) =
      (Nat.card H * Nat.card N) / Nat.card ((H ∩ N : Set G)) := by
    sorry
  ```
  - We decomposite $|G|$ in two differente ways, then $|H|, |N|, |H ⊔ N|$, finally do rewriting and canceling on this equation
  ```lean
  have card_G_one : Nat.card G = H.index * Nat.card H := by
    exact Eq.symm (Subgroup.index_mul_card H)
  have card_G_two : Nat.card G = (H ⊔ N).index * Nat.card (H ⊔ N : Subgroup G):= by
    exact Eq.symm (Subgroup.index_mul_card (H ⊔ N))
  -- without detailing further decompositions and the rewriting steps
  simpa [mul_comm, mul_left_comm, mul_assoc] using card_G_two
  ```
]


#slide[
  == Challenges
  
  ==
  - Before theorem hacking: research existing relevant API, choose proof strategy, fill missed lemmas

  - During the proof: make the proof type correct as well as natural in math
  - When Submitting the PR: hold technical discussions with mathlib maintainers
]

#slide[
  == Role of the proof assistant in math learning
  == 
  - Pros: formalization reveals structure that is invisible on paper
    - proof states are clearly stated in InfoView
    - the dependencies between lemmas become transparent

  - Cons: sometimes might let the technical details bury the intuition
    - large and complicated mathlib’s API 
    - paper-math friendly vs. Lean friendly 
]


#slide[
  == Current status
  ==
  - Clean up and refine the file of Abelian Simple Group

  - Finish `feat: (GroupTheory/SpecificGroups/Cyclic): generalize the proof of prime_card by not assuming Finite (PR #32152)`
  - Finish the proof of Hall Subgroup, make the second possible PR
  - Start the writing process in about 2 weeks (deadline Jan.27)
]

#slide[
  == Q&A
  ===
  - Any questions or suggestions :)?
 
]
