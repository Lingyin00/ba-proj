[![Lean Action CI](https://github.com/Lingyin00/bachelor-thesis/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Lingyin00/bachelor-thesis/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.25.0--rc2-blue.svg)](https://leanprover-community.github.io/)
[![mathlib4](https://img.shields.io/badge/mathlib4-5b49109-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)


# Bachelor-Thesis

This formalization [project](https://github.com/Lingyin00/ba-proj) begins with the narrative of _Chapter 3: Quotient Groups and Homomorphisms_ from _**Abstract Algebra**_ by Dummit & Foote.  
It is built on top of *mathlib*, using its existing formalization of group theory, rather than redefining concepts from scratch.

## Goal
 - Formalizing selected exercises from D&F in Lean 4
 - Submiting PRs of possibly interesting and useful lemmas to *mathlib*

## Theorems

- AbelianSimpleG (from exercise 3.4.1): without the premises that _G_ is *finite*.
  - The illustration code in paper is from [this commit](https://github.com/leanprover-community/mathlib4/pull/32152/changes/5ce5135ddcfd86db3ae6cccf11b420310cbb9266)
- HallSubgroup (from exercise 3.3.10): concerning the definitions of _Hall Subgroup_ and orders
  - Illustration code is in the file [BachelorThesis/code-original/HallSubgroup.G](https://github.com/Lingyin00/ba-proj/blob/main/BachelorThesis/code-original/HallSubgroup.lean)


