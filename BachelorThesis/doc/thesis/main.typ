#import "template.typ":*
#let target_date = datetime(year: 2026, month: 2, day: 24)
#show : official.with(
  title: [
    Extending the Group Theory Library in Mathlib
  ],
  author: "Lingyin Luo",
  email: "Luo.Lingyin@campus.lmu.de",
  matriculation: [TODO],
  thesis-type: [Bachelor's Thesis],
  advisor: [Xavier Généreux],
  supervisor: [Prof. Dr. Jasmin Blanchette],
  submission_date: target_date.display("[month repr:long] [day], [year]"),
  glossary: (
    (key: "DTT", short: "DTT", long: "dependent type theory"),
  ),
  abstract: [
This thesis investigates the formalization of classical group-theoretic arguments in the proof assistant Lean, with a focus on the interaction between mathematical structure and library design in mathlib. Two case studies are developed: a theorem characterizing abelian simple groups and two theorems concerning Hall subgroups and their stability under intersection and quotient by normal subgroups.

The first case study resulted in a contribution to mathlib, including a refinement of an existing lemma and a generalization motivated by the review process. This experience illustrates how formal developments evolve from problem-driven proofs toward structurally reusable library components.

The second case study analyzes the formal reconstruction of textbook proofs of the Hall subgroup theorems. While the underlying mathematics relies only on elementary index computations and isomorphism theorems, the formalization requires careful coordination of seveal APIs and careful treatments on type correctness. In particular, the Hall condition is treated as a coprimality invariant transported along explicit chains of divisibility relations.

  ],
  acknowledgement: [
TODO
  ],
)  

#include("sections/01-introduction.typ")
#include("sections/02-background.typ")
#include("sections/03-implementation.typ")
#include("sections/04-evaluation.typ")
#include("sections/07-Discussion.typ")
#include("sections/05-related-work.typ")
#include("sections/06-conclusion.typ")
#include("sections/08-future-work.typ")
